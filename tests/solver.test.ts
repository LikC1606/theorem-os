import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { canonicalMathProblemStatementPayloads, type MathProblemContract } from '../src/math/contracts';
import { LEAN_EVAL_BENCHMARK_COMMIT } from '../src/math/leanEvalCatalogAdapter';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { readSolverRunState } from '../src/solver/archive';
import { hashMathFormalSourceDeclaration, type MathematicsVerifierBatchRequest, type MathematicsVerifierBatchResult } from '../src/math/verifier';
import * as verifier from '../src/math/verifier';
import { readSolverProblem, assertSolverSources, assertSolverProjectSources, commitSolverSources, git, withSolverWorktree, SolverSourceError, type SolverProblem } from '../src/solver/problem';
import { checkSolverProof } from '../src/solver/modules/evidence';
import { directSolverModules } from '../src/solver/modules';
import { configurableSolverModules } from '../src/solver/modules/custom';
import { runSolver } from '../src/solver/run';
import { rememberSolverFailure, solverProofFeedback } from '../src/solver/feedback';
import { createMathRetrievalCorpus } from '../src/math/mathRetrievalCorpus';
import * as retrievalCorpus from '../src/math/mathRetrievalCorpus';
import type { MathAgentOptions, MathAgentSession } from '../src/runtime/codexSession';
import { prepareDeepSeekProfile } from '../src/runtime/deepseek';
import { prepareWestlakeProfile } from '../src/runtime/westlake';
import { CooperativeResearch, readCooperationPlan, parseCooperationPlan, taskVersion, assignmentDeliveryFile, type CooperativeAction, type CooperativeTask, type RouteGroup } from '../src/solver/cooperation';
import { canonicalMathJson } from '../src/math/mathRuntimeIo';
import { deliveryDetails, readDeliveryLines, readMathResponse } from '../src/solver/deliveries';
import { assertStatementSnapshot, captureStatementContexts, isStatementAction, readBacktranslation, statementSnapshot, writeStatementSnapshot } from '../src/solver/statementReview';
import { parseLeanStatementContexts } from '../src/math/leanStatementContext';
import { captureProofReferences, proofReferencesUnchanged } from '../src/solver/proofReferences';
import { applyTaskChanges, checkTaskProof, checkTaskProofs, createTaskSourceProjector, taskChanges } from '../src/solver/cooperativeProof';
import { readContinuationPage, readContinuationSnapshot } from '../src/solver/continuationInput';
import { inspectScopedLeanDeclarations, leanDeclarationContextCommands } from '../src/math/leanSource';
import { recordRouteBlockers, refreshRouteBlockers } from '../src/solver/routeControl';
import type { TaskRecord, RouteRecord } from '../src/solver/tasks';
import { buildTheoremKnowledge, writeTheoremKnowledge } from '../src/solver/theoremKnowledge';
import { readKnowledgeCatalog, writePackedKnowledge } from '../src/solver/theoremKnowledgeStore';
import { pendingResearchHandoffs, researchHandoffs, resolveResearchHandoffs } from '../src/solver/researchHandoffs';
import { buildRunInspection } from '../src/solver/inspection';
import { createTaskConnectionCheck } from '../src/solver/taskConnections';
import { deferred } from './helpers/async';

const host = vi.hoisted(() => ({ verify: vi.fn(), createSession: vi.fn(), officialGate: vi.fn(), build: vi.fn(), delay: vi.fn(),
  prepare: vi.fn(), freeze: vi.fn(), readiness: vi.fn(), connectivity: vi.fn(), packages: undefined as string | undefined }));
vi.mock('../src/math/leanDiagnostics', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/leanDiagnostics')>(), runLeanDiagnostics: host.prepare,
}));
vi.mock('../src/math/leanTypeDiagnostics', () => ({ checkLeanType: async () => {
  throw new Error('Offline solver fixture: type preflight is tested separately.');
} }));
vi.mock('node:timers/promises', async importOriginal => ({
  ...await importOriginal<typeof import('node:timers/promises')>(), setTimeout: host.delay,
}));
vi.mock('../src/math/mathBuildManifest', () => ({ readMathBuildManifest: host.build }));
vi.mock('../src/math/leanToolchainReadiness', () => ({ checkResolvedLeanToolchainReadiness: host.readiness }));
vi.mock('../src/runtime/codexConnectivity', () => ({ checkCodexProviderConnectivity: host.connectivity }));
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
    results: request.items.map((item, index) => ({ ...item, sourceDeclarationHash: item.expectedSourceDeclarationHash,
      checkId: item.id?.trim() || `check-${index + 1}`, sessionId: 'host', checkedAt: 2,
      receiptId: `fixture-${request.targetCommit}-${item.theoremName}`,
      targetCommit: request.targetCommit, status: 'kernel_verified', claim: 'statement' })) as MathematicsVerifierBatchResult['results'] };
}

/** Marks the batch and every result as failed; `fields` adds result fields such as an error preview. */
function failed(batch: MathematicsVerifierBatchResult, fields: Partial<MathematicsVerifierBatchResult['results'][number]> = {}): MathematicsVerifierBatchResult {
  return { ...batch, status: 'failed', results: batch.results.map(result => ({ ...result, status: 'failed', ...fields })) };
}

const unsolved = 'Submission.lean:4:1: error: unsolved goals\n⊢ True';

/** A model session stub whose turns run `turn`; `fields` adds session fields such as lastError. */
function session(thread: string | ((options: MathAgentOptions) => string),
  turn: (options: MathAgentOptions, message: string) => Promise<string>, fields: Partial<MathAgentSession> = {}) {
  return async (options: MathAgentOptions): Promise<MathAgentSession> => ({ threadId: typeof thread === 'string' ? thread : thread(options),
    ...fields, run: message => turn(options, message), close: vi.fn(), interrupt: vi.fn() });
}

function commitFixture(worktree: string, message: string, ...flags: string[]) {
  git(worktree, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', ...flags, '--no-gpg-sign', '--quiet', '-m', message]);
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
    host.prepare.mockReset().mockImplementation(async input => {
      for (const file of input.files) if (/^StatementContext[0-9a-f]+\.lean$/u.test(file)) {
        const source = fs.readFileSync(path.join(input.projectRoot, file), 'utf8');
        const reports = [...source.matchAll(/\("id", Lean.toJson "([^"]+)"\)/gu)].map(match =>
          ({ id: match[1], context: { type: 'True', constants: [], omitted: [] } }));
        fs.mkdirSync(path.join(input.projectRoot, '.lake'), { recursive: true });
        fs.writeFileSync(path.join(input.projectRoot, '.lake', file.replace('StatementContext', 'statement-context-').replace('.lean', '.json')), JSON.stringify(reports));
      }
      return { exitCode: 0, timedOut: false, phases: [] };
    });
    host.readiness.mockReset().mockReturnValue({ status: 'ready' });
    host.connectivity.mockReset().mockResolvedValue({ status: 'reachable', httpStatus: 401 });
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
    commitFixture(workspace, 'Public baseline');
    fs.appendFileSync(path.join(workspace, '.git', 'info', 'exclude'), '\n/active-problem.json\n**/.lake/\n');
    problem = readSolverProblem(workspace, receipt.activeProblemPath);
    output = path.join(directory, 'run.json');
    const task = path.join(directory, 'task.md'); const build = path.join(directory, 'build.json');
    fs.writeFileSync(task, 'Prove the original targets'); fs.writeFileSync(build, '{}');
    args = ['--workspace', workspace, '--task-file', task, '--build-manifest', build, '--output', output, '--max-turns', '1', '--workers', '1'];
    host.verify.mockImplementation(async request => verified(request));
    host.officialGate.mockResolvedValue({ comparison: { status: 'official_verified' } });
    host.createSession.mockImplementation(session(options => options.threadId || 'fixture-thread', async options => {
      fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
      return 'completed';
    }));
  });
  afterEach(() => { vi.useRealTimers(); vi.restoreAllMocks(); vi.unstubAllEnvs(); fs.rmSync(directory, { recursive: true, force: true }); });

  function configureDefinitionGoal() {
    const source = original.replace('theorem first', 'noncomputable def C : Nat := by sorry\ntheorem first');
    const receipt = JSON.parse(fs.readFileSync(problem.activeProblemPath, 'utf8'));
    const payload = canonicalMathProblemStatementPayloads({ ...receipt.contract, formalStatement: source });
    receipt.contract = { ...receipt.contract, formalStatement: source,
      statementHash: mathDigest(payload.informal), leanStatementHash: mathDigest(payload.lean) };
    receipt.publicObligations.unshift({ name: 'Submission.C', declarationHash: hashMathFormalSourceDeclaration(source, 'Submission.C') });
    fs.writeFileSync(problem.activeProblemPath, JSON.stringify(receipt));
    for (const file of ['Submission.lean', 'Challenge.lean']) fs.writeFileSync(path.join(project, file), source);
    git(workspace, ['add', '--', 'generated']);
    commitFixture(workspace, 'Original definition goal');
    problem = readSolverProblem(workspace, problem.activeProblemPath);
    const task: CooperativeTask = { id: 'constant', kind: 'goal', objective: 'Fill the original definition', dependsOn: [], revision: 0,
      proofPath: 'Submission.lean', theoremName: 'Submission.C' };
    return { source, task };
  }

  it('runs a custom M1 without the Codex route while retaining proof checks and independent acceptance', async () => {
    host.connectivity.mockResolvedValue({ status: 'unavailable' });
    const modules = { ...directSolverModules, id: 'custom-execution', M1: { ...directSolverModules.M1,
      version: 'custom-execution-v1', open: (options: MathAgentOptions) => host.createSession(options) } };
    expect(await runSolver(args, directory, modules)).toBe(0);
    expect(host.connectivity).not.toHaveBeenCalled();
    expect(host.verify.mock.calls.length).toBeGreaterThanOrEqual(2);
    expect(host.officialGate).toHaveBeenCalledOnce();
    expect(JSON.parse(fs.readFileSync(output, 'utf8')).status).toBe('evaluated_passed');
  });

  it('loads a CLI module plan, retains independent acceptance and rejects changed policies on resume', async () => {
    const plan = { scheduler: 'plan' as const, context: 'essential' as const, custom: [] };
    const file = path.join(directory, 'module-plan.json'); fs.writeFileSync(file, JSON.stringify(plan));
    expect(await runSolver([...args, '--module-plan', file], directory)).toBe(0);
    const state = JSON.parse(fs.readFileSync(output + '.runtime/state.json', 'utf8'));
    const modules = configurableSolverModules(plan, 'cooperative', 1);
    expect(state.moduleConfiguration.versions.M4).toBe(modules.M4.version);
    expect(state.moduleConfiguration.versions.M2).toBe(directSolverModules.M2.version);
    expect(host.verify.mock.calls.length).toBeGreaterThanOrEqual(2);
    const completed = fs.readFileSync(output, 'utf8');
    fs.writeFileSync(file, JSON.stringify({ ...plan, context: 'full' }));
    expect(await runSolver([...args, '--module-plan', file, '--resume'], directory)).toBe(1);
    expect(fs.readFileSync(output, 'utf8')).toBe(completed);
  });

  it.each([
    ['DeepSeek', prepareDeepSeekProfile, 'deepseek-v4-pro', 'https://api.deepseek.com'],
    ['Westlake', prepareWestlakeProfile, 'deepseek-flash', 'https://hpc-api.westlake.edu.cn/v1'],
  ] as const)('binds %s provider configuration to saved runs and rejects profile changes on resume', async (name, prepare, model, endpoint) => {
    const profile = path.join(directory, name.toLowerCase());
    const digest = prepare(profile, model, 'high');
    vi.stubEnv('CODEX_HOME', profile);
    const providerArgs = [...args, '--model', model, '--effort', 'high'];
    expect(await runSolver(providerArgs, directory)).toBe(0);
    const state = JSON.parse(fs.readFileSync(output + '.runtime/state.json', 'utf8'));
    expect(state).toMatchObject({ providerProfile: profile, providerProfileDigest: digest });
    expect(host.createSession.mock.calls[0][0]).toMatchObject({ profile, model, effort: 'high' });
    expect(await runSolver([...providerArgs, '--resume'], directory)).toBe(0);
    const completed = fs.readFileSync(output, 'utf8');
    const calls = host.createSession.mock.calls.length;
    const replacement = path.join(directory, 'other-profile');
    prepare(replacement, model, 'high');
    vi.stubEnv('CODEX_HOME', replacement);
    expect(await runSolver([...providerArgs, '--resume'], directory)).toBe(1);
    expect(fs.readFileSync(output, 'utf8')).toBe(completed);
    expect(host.createSession).toHaveBeenCalledTimes(calls);
    vi.stubEnv('CODEX_HOME', profile);
    const config = path.join(profile, 'config.toml');
    fs.chmodSync(config, 0o600);
    fs.writeFileSync(config, fs.readFileSync(config, 'utf8').replace(endpoint, 'https://changed-provider.invalid'));
    expect(await runSolver([...providerArgs, '--resume'], directory)).toBe(1);
    expect(fs.readFileSync(output, 'utf8')).toBe(completed);
    expect(host.createSession).toHaveBeenCalledTimes(calls);
  });

  function continuationFixture(text = 'Historical route; its proof has not been replayed.') {
    const source = path.join(directory, 'previous-notes.txt');
    const file = path.join(directory, 'continuation-input.json');
    fs.writeFileSync(source, text);
    const sha256 = mathDigest(text);
    fs.writeFileSync(file, JSON.stringify({ schema: 'theorem-os.continuation-input.v1',
      taskDigest: mathDigest(fs.readFileSync(args[args.indexOf('--task-file') + 1])), problemReceiptDigest: problem.receiptDigest,
      attachments: ['previous', 'same-content'].map(id => ({ id, kind: 'research-notes', path: source,
        bytes: Buffer.byteLength(text), sha256 })) }));
    return { file, source, text, sha256 };
  }

  it('freezes explicit attachments for all four roles while preserving the verbatim task digest', async () => {
    const taskFile = args[args.indexOf('--task-file') + 1];
    const taskText = 'Preserve all controls.\n\n# Previous proof\nThis remains literal task text.\n';
    fs.writeFileSync(taskFile, taskText);
    const fixture = continuationFixture();
    expect(await runSolver([...args, '--workers', '4', '--startup-only', '--continuation-manifest', fixture.file], directory)).toBe(0);
    expect(host.createSession).not.toHaveBeenCalled();
    const state = readSolverRunState(`${output}.runtime/state.json`);
    expect(state.taskDigest).toBe(mathDigest(taskText));
    expect(fs.readFileSync(taskFile, 'utf8')).toBe(taskText);
    expect(state.continuationDigest).toMatch(/^[a-f0-9]{64}$/u);
    for (const worker of state.workers!) {
      const snapshot = path.join(worker.worktree, problem.projectRelative, '.lake/continuation.json');
      expect(fs.statSync(snapshot).mode & 0o777).toBe(0o400);
      expect(readContinuationSnapshot(snapshot, state.continuationDigest!).manifest.taskDigest).toBe(state.taskDigest);
      expect(readContinuationPage(snapshot, state.continuationDigest!, 'previous').text).toBe(fixture.text);
      expect(fs.readdirSync(path.join(path.dirname(snapshot), 'continuation'))).toEqual([`${fixture.sha256}.txt`]);
    }
  });

  it('resumes from frozen attachments after the original input files are removed', async () => {
    const fixture = continuationFixture();
    expect(await runSolver([...args, '--startup-only', '--continuation-manifest', fixture.file], directory)).toBe(0);
    const before = readSolverRunState(`${output}.runtime/state.json`).continuationDigest;
    fs.rmSync(fixture.source); fs.rmSync(fixture.file);
    expect(await runSolver([...args, '--startup-only', '--resume'], directory)).toBe(0);
    expect(readSolverRunState(`${output}.runtime/state.json`).continuationDigest).toBe(before);
    expect(host.createSession).not.toHaveBeenCalled();
  });

  it('delivers the mandatory frozen attachment index to a resumed model turn after original inputs are removed', async () => {
    const fixture = continuationFixture();
    expect(await runSolver([...args, '--startup-only', '--continuation-manifest', fixture.file], directory)).toBe(0);
    const before = readSolverRunState(`${output}.runtime/state.json`);
    fs.rmSync(fixture.source); fs.rmSync(fixture.file);
    let received = false;
    host.createSession.mockImplementation(session('continuation-resume', async (options, message) => {
      const current = readSolverRunState(`${output}.runtime/state.json`);
      const section = current.lastContextManifest!.included.find(item => item.id === `continuation-input:${before.continuationDigest}`);
      expect(section).toMatchObject({ kind: 'continuation', required: true });
      expect(message).toContain('continuation read --snapshot');
      expect(message).toContain(before.continuationDigest);
      expect(message).not.toContain(fixture.text);
      const snapshot = path.join(options.workspace, problem.projectRelative, '.lake/continuation.json');
      expect(message).toContain(snapshot);
      expect(readContinuationPage(snapshot, before.continuationDigest!, 'previous').text).toBe(fixture.text);
      fs.writeFileSync(path.join(options.workspace, problem.projectRelative, 'Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
      received = true;
      return 'completed';
    }));
    expect(await runSolver([...args, '--resume'], directory)).toBe(0);
    expect(received).toBe(true);
    expect(host.createSession).toHaveBeenCalledOnce();
    expect(readSolverRunState(`${output}.runtime/state.json`).continuationDigest).toBe(before.continuationDigest);
  });

  it.each([
    { target: 'manifest', change: 'missing' }, { target: 'body', change: 'missing' },
    { target: 'manifest', change: 'corrupted' }, { target: 'body', change: 'corrupted' },
  ] as const)('rebuilds a missing worker attachment but rejects a corrupted copy ($target, $change)', async ({ target, change }) => {
    const fixture = continuationFixture();
    expect(await runSolver([...args, '--startup-only', '--continuation-manifest', fixture.file], directory)).toBe(0);
    const before = readSolverRunState(`${output}.runtime/state.json`);
    const snapshot = path.join(before.worktree, problem.projectRelative, '.lake/continuation.json');
    const changed = target === 'manifest' ? snapshot : path.join(path.dirname(snapshot), 'continuation', `${fixture.sha256}.txt`);
    fs.rmSync(fixture.source); fs.rmSync(fixture.file);
    if (change === 'missing') fs.rmSync(changed);
    else {
      const bytes = fs.readFileSync(changed); bytes[bytes.length - 1] ^= 1;
      fs.chmodSync(changed, 0o600); fs.writeFileSync(changed, bytes); fs.chmodSync(changed, 0o400);
    }
    expect(await runSolver([...args, '--resume'], directory)).toBe(change === 'missing' ? 0 : 1);
    if (change === 'missing') {
      expect(host.createSession).toHaveBeenCalledOnce();
      expect(readContinuationPage(snapshot, before.continuationDigest!, 'previous').text).toBe(fixture.text);
      expect(fs.statSync(changed).mode & 0o777).toBe(0o400);
    } else {
      expect(host.createSession).not.toHaveBeenCalled();
      expect(readSolverRunState(`${output}.runtime/state.json`)).toMatchObject({
        continuationDigest: before.continuationDigest, turns: 0, error: 'math_continuation_frozen_file_changed',
      });
    }
    expect(readContinuationPage(path.join(`${output}.runtime`, 'continuation.json'), before.continuationDigest!, 'previous').text)
      .toBe(fixture.text);
  });

  it.each(['manifest', 'snapshot', 'body', 'missing'] as const)
  ('checks attached %s identity before a completed run can return early', async changed => {
    const fixture = continuationFixture();
    expect(await runSolver([...args, '--continuation-manifest', fixture.file], directory)).toBe(0);
    const completed = fs.readFileSync(output, 'utf8'), calls = host.createSession.mock.calls.length;
    const stateBefore = fs.readFileSync(`${output}.runtime/state.json`, 'utf8');
    const snapshot = path.join(`${output}.runtime`, 'continuation.json');
    const body = path.join(`${output}.runtime`, 'continuation', `${fixture.sha256}.txt`);
    let resume = [...args, '--resume'];
    if (changed === 'manifest') resume.push('--continuation-manifest', continuationFixture('Replaced historical route.').file);
    else if (changed === 'missing') fs.rmSync(body);
    else {
      const target = changed === 'snapshot' ? snapshot : body;
      fs.chmodSync(target, 0o600); fs.writeFileSync(target, 'Replaced frozen content.');
    }
    expect(await runSolver(resume, directory)).toBe(1);
    expect(fs.readFileSync(output, 'utf8')).toBe(completed);
    expect(fs.readFileSync(`${output}.runtime/state.json`, 'utf8')).toBe(stateBefore);
    expect(host.createSession).toHaveBeenCalledTimes(calls);
  });

  it('rejects adding attachments to an existing unattached run before its completed-result shortcut', async () => {
    expect(await runSolver(args, directory)).toBe(0);
    const completed = fs.readFileSync(output, 'utf8'), calls = host.createSession.mock.calls.length;
    const fixture = continuationFixture();
    expect(await runSolver([...args, '--resume', '--continuation-manifest', fixture.file], directory)).toBe(1);
    expect(fs.readFileSync(output, 'utf8')).toBe(completed);
    expect(host.createSession).toHaveBeenCalledTimes(calls);
    expect(fs.existsSync(path.join(`${output}.runtime`, 'continuation.json'))).toBe(false);
  });

  function knowledgeFixture(filename = 'knowledge.json', type = 'True', format: 'v1' | 'v2' = 'v1') {
    const write = format === 'v1' ? writeTheoremKnowledge : writePackedKnowledge;
    return write(path.join(directory, filename), buildTheoremKnowledge([{
      name: 'Saved.helper', file: 'Submission.lean', type, typeKind: 'closed-task-type', kind: 'lemma',
      description: 'Historical helper', premises: [],
      dependencies: { statement: [], proof: [], tasks: [], coverage: 'unavailable' },
      files: { 'Submission.lean': `namespace Saved\nlemma helper : ${type} := by trivial\nend Saved\n` },
      provenance: { kind: 'solver-check', problemId: 'previous-problem', source: '/archive/state.json',
        sourceDigest: 'a'.repeat(64), receiptIds: ['historical-receipt'] },
    }]));
  }

  it.each(['v1', 'v2'] as const)('prepares identical read-only %s knowledge snapshots for all four workers without opening a model', async format => {
    const catalog = knowledgeFixture('knowledge.json', 'True', format);
    expect(await runSolver([...args, '--workers', '4', '--startup-only', '--knowledge-base', catalog.file], directory)).toBe(0);
    expect(host.createSession).not.toHaveBeenCalled();
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.knowledgeDigest).toBe(catalog.sha256);
    for (const worker of state.workers) {
      const snapshot = path.join(worker.worktree, 'generated/p/.lake/theorem-knowledge.json');
      expect(mathDigest(fs.readFileSync(snapshot))).toBe(catalog.sha256);
      expect(fs.statSync(snapshot).mode & 0o222).toBe(0);
      const saved = readKnowledgeCatalog(snapshot, catalog.sha256);
      expect(saved.format).toBe(format);
      expect(Object.values(saved.base.sources)).toEqual(Object.values(readKnowledgeCatalog(catalog.file).base.sources));
    }
    expect(await runSolver([...args, '--workers', '4', '--startup-only', '--resume', '--knowledge-base', catalog.file], directory)).toBe(0);
  });

  it('offers pinned knowledge commands to the solver while retaining independent proof acceptance', async () => {
    const catalog = knowledgeFixture();
    const entry = readKnowledgeCatalog(catalog.file).base.entries[0]!;
    const declaration = { name: 'Submission.saved_bridge', file: 'Submission.lean' };
    const claim = { id: entry.id, catalogDigest: catalog.sha256, declaration };
    const messages: string[] = [];
    host.verify.mockImplementation(async (request: MathematicsVerifierBatchRequest) => {
      const result = verified(request);
      return { ...result, results: result.results.map(item => ({ ...item, declarationReferences: { statement: [],
        proof: item.theoremName === 'Submission.first' ? [declaration] : [] } })) };
    });
    host.createSession.mockImplementation(session('knowledge-fixture', async (options, message) => {
      messages.push(message);
      fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original
        .replace('theorem first', 'lemma saved_bridge : True := by trivial\ntheorem first')
        .replace('first : True := by sorry', 'first : True := by exact saved_bridge')
        .replace('second : True := by sorry', 'second : True := by trivial'));
      fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), JSON.stringify({
        summary: 'Adapt the saved bridge for the first original target; prove the second directly.',
        knowledgeUses: [claim, { ...claim, catalogDigest: mathDigest('forged-catalog') }],
      }));
      return 'completed';
    }));
    expect(await runSolver([...args, '--knowledge-base', catalog.file], directory)).toBe(0);
    const options = host.createSession.mock.calls[0]![0] as MathAgentOptions;
    expect(options.instructions).toContain('knowledge search --catalog');
    expect(options.instructions).toContain(catalog.sha256);
    expect(options.instructions).toContain('historical receipts');
    expect(options.instructions).toContain('knowledge dependencies --catalog');
    expect(options.instructions).toContain('knowledge consumers --catalog');
    expect(options.instructions).toContain('not instantiated applications');
    expect(options.instructions).toContain('knowledge source --catalog');
    expect(options.instructions).toContain('--offset NEXT_OFFSET');
    expect(options.instructions).toContain('--environment');
    expect(options.instructions).toContain('--problem-receipt');
    expect(messages).toHaveLength(1);
    expect(messages[0]).toContain('theorem-os.knowledge-context.v1');
    expect(messages[0]).toContain('Saved.helper');
    expect(messages[0]).toContain('Submission.first');
    expect(messages[0]).toContain('Submission.second');
    expect(messages[0]).not.toContain('by trivial');
    expect(JSON.parse(fs.readFileSync(output, 'utf8')).status).toBe('evaluated_passed');
    const recorded = readSolverRunState(`${output}.runtime/state.json`);
    expect(recorded.knowledgeRetrievals?.observations).toEqual(expect.arrayContaining([
      expect.objectContaining({ catalogDigest: catalog.sha256, included: true, candidateIds: expect.any(Array),
        contextDigest: expect.any(String) }),
    ]));
    expect(recorded.knowledgeUses).toEqual([
      { ...claim, consumer: { taskId: 'original_goal_1', taskDigest: expect.any(String) },
        status: 'checked-reference', attribution: 'model-reported-origin', workerId: 'solver',
        commit: recorded.check!.commit, checkedCommit: recorded.check!.commit, checkedSourceDigest: recorded.check!.sourceDigest },
      { ...claim, consumer: { taskId: 'original_goal_2', taskDigest: expect.any(String) },
        status: 'reported-attempt', attribution: 'model-reported-origin', workerId: 'solver', commit: recorded.check!.commit },
    ]);
    expect(vi.mocked(console.log).mock.calls.map(([line]) => JSON.parse(line)).filter(item => item.event === 'knowledge_use_rejected'))
      .toEqual([expect.objectContaining({ commit: recorded.check!.commit, rejected: 1 }),
        expect.objectContaining({ commit: recorded.check!.commit, rejected: 1 })]);
    expect(buildRunInspection(recorded).knowledge).toMatchObject({ status: 'enabled', retrievalCoverage: 'recorded' });
    expect(host.verify.mock.calls.length).toBeGreaterThanOrEqual(2);
    expect(host.officialGate).toHaveBeenCalledOnce();
  });

  it('rejects damaged packed worker source objects on resume before model dispatch', async () => {
    const catalog = knowledgeFixture('knowledge.json', 'True', 'v2');
    expect(await runSolver([...args, '--startup-only', '--knowledge-base', catalog.file], directory)).toBe(0);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    const snapshot = path.join(state.worktree, 'generated/p/.lake/theorem-knowledge.json');
    const manifest = JSON.parse(fs.readFileSync(snapshot, 'utf8'));
    const blob = path.join(path.dirname(snapshot), manifest.objectsDirectory, Object.keys(manifest.sources)[0]!);
    fs.chmodSync(blob, 0o600);
    fs.writeFileSync(blob, fs.readFileSync(blob, 'utf8').replace('True', 'Fals'));
    fs.chmodSync(blob, 0o400);
    expect(await runSolver([...args, '--startup-only', '--resume', '--knowledge-base', catalog.file], directory)).toBe(1);
    expect(host.createSession).not.toHaveBeenCalled();
  });

  it.each(['omitted', 'replaced'])('rejects a %s knowledge snapshot on resume before model dispatch', async change => {
    const first = knowledgeFixture(), replacement = knowledgeFixture('replacement.json', 'True /\\ True');
    expect(await runSolver([...args, '--startup-only', '--knowledge-base', first.file], directory)).toBe(0);
    expect(await runSolver([...args, '--startup-only', '--resume',
      ...(change === 'replaced' ? ['--knowledge-base', replacement.file] : [])], directory)).toBe(1);
    expect(host.createSession).not.toHaveBeenCalled();
  });

  it('runs independent peers without planning or sharing and accounts for both sessions', async () => {
    let started = 0;
    const bothStarted = deferred();
    host.createSession.mockImplementation(session('independent', async (options, message) => {
      expect(message).not.toContain('Cooperative assignment:');
      expect(fs.existsSync(path.join(options.workspace, 'COOPERATION.json'))).toBe(false);
      options.onUsage({ totalTokens: 100, inputTokens: 80, outputTokens: 20 });
      if (++started === 2) bothStarted.resolve();
      await bothStarted.promise;
      fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
      return 'completed';
    }));
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '2', '--coordination', 'independent'], directory)).toBe(0);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.cooperation).toBeUndefined();
    expect(state.coordination).toBe('independent');
    expect(state.turns).toBe(2);
    expect(state.dispatchCounts).toEqual({ proof: 2 });
    expect(state.workers.map((worker: any) => worker.dispatchCounts)).toEqual([{ proof: 1 }, { proof: 1 }]);
    expect(JSON.parse(fs.readFileSync(output, 'utf8')).solveWallMs).toBeGreaterThanOrEqual(0);
    expect(state.usage).toEqual({ totalTokens: 200, inputTokens: 160, outputTokens: 40 });
    expect(state.workers.map((worker: any) => worker.turns)).toEqual([1, 1]);
    expect(host.createSession).toHaveBeenCalledTimes(2);
    expect(host.officialGate).toHaveBeenCalledOnce();
  });

  it('lets independent proof work exceed twenty dispatches under the default wall-time budget', async () => {
    const attempts = new Map<string, number>();
    host.verify.mockImplementation(async request => {
      const checked = verified(request);
      return fs.readFileSync(path.join(request.projectRoot, 'Submission.lean'), 'utf8').includes('sorry') ? failed(checked) : checked;
    });
    host.createSession.mockImplementation(session(options => options.workspace, async options => {
      const count = (attempts.get(options.workspace) ?? 0) + 1;
      attempts.set(options.workspace, count);
      await Promise.resolve();
      if (count === 6) fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'),
        original.replaceAll('by sorry', 'by trivial'));
      return 'completed';
    }));
    const defaultBudget = args.filter((_, index) => args[index] !== '--max-turns' && args[index - 1] !== '--max-turns');
    expect(await runSolver([...defaultBudget, '--workers', '4', '--coordination', 'independent'], directory)).toBe(0);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.turns).toBeGreaterThan(20);
    expect(state.turns).toBeLessThanOrEqual(24);
    expect(state.dispatchCounts).toEqual({ proof: state.turns });
    expect(state.workers.every((worker: any) => worker.turns >= 5)).toBe(true);
  });

  it('counts failed independent turns within one shared budget', async () => {
    host.verify.mockImplementation(async request => failed(verified(request)));
    host.createSession.mockImplementation(session('failed-independent', async options => {
      options.onUsage({ totalTokens: 75 }); return 'failed';
    }, { lastError: 'fixture model failure' }));
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '3', '--coordination', 'independent'], directory)).toBe(1);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.turns).toBe(3);
    expect(state.usage.totalTokens).toBe(225);
    expect(host.createSession).toHaveBeenCalledTimes(3);
    expect(state.error).toBe('math_model_turn_failed');
    expect(state.workers.filter((worker: any) => worker.turns).every((worker: any) => worker.error === 'math_model_turn_failed')).toBe(true);
    expect(host.officialGate).not.toHaveBeenCalled();
  });

  it('stops new model turns at the reported token allowance without cancelling final proof verification', async () => {
    host.createSession.mockImplementation(session('token-proof', async options => {
      options.onUsage({ totalTokens: 120, inputTokens: 100, outputTokens: 20 });
      fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
      return 'completed';
    }));
    expect(await runSolver([...args, '--max-total-tokens', '100', '--max-turns', '0', '--max-run-seconds', '0',
      '--max-turn-seconds', '0'], directory)).toBe(0);
    const result = JSON.parse(fs.readFileSync(output, 'utf8'));
    expect(result).toMatchObject({ status: 'evaluated_passed', turns: 1,
      tokenBudget: { status: 'exhausted', reportedTotalTokens: 120, overrunTokens: 20, usageComplete: true } });
    expect(result.reason).toBeUndefined();
    expect(host.officialGate).toHaveBeenCalledOnce();
    expect(host.createSession.mock.results.length).toBe(1);
    expect((await host.createSession.mock.results[0].value).interrupt).not.toHaveBeenCalled();
  });

  it('uses one reported allowance across independent workers and records in-flight overrun', async () => {
    host.verify.mockImplementation(async request => failed(verified(request)));
    let started = 0;
    const running = deferred();
    const runs = vi.fn();
    const interrupts = vi.fn();
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ threadId: options.workspace,
      run: async () => {
        runs(); if (++started === 4) running.resolve(); await running.promise;
        options.onUsage({ totalTokens: 40 });
        return 'completed';
      }, close: vi.fn(), interrupt: interrupts }));
    expect(await runSolver([...args, '--workers', '4', '--coordination', 'independent', '--max-turns', '20',
      '--max-total-tokens', '100'], directory)).toBe(4);
    const result = JSON.parse(fs.readFileSync(output, 'utf8'));
    expect(result).toMatchObject({ status: 'limit_reached', reason: 'math_total_token_limit', turns: 4,
      usage: { totalTokens: 160 }, tokenBudget: { maxTotalTokens: 100, status: 'exhausted',
        reportedTotalTokens: 160, overrunTokens: 60, usageComplete: true } });
    expect(runs).toHaveBeenCalledTimes(4);
    expect(interrupts).not.toHaveBeenCalled();
    expect(host.officialGate).not.toHaveBeenCalled();
  });

  it.each([false, true])('gates internal requests without losing complete usage or final proof checks (solved: %s)', async solved => {
    const profile = path.join(directory, 'westlake-request-budget');
    prepareWestlakeProfile(profile, 'deepseek-flash', 'high');
    vi.stubEnv('CODEX_HOME', profile);
    host.verify.mockImplementation(async request => solved ? verified(request) : failed(verified(request)));
    const requests = vi.fn();
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ threadId: 'request-budget',
      usageSource: 'upstream-requests', lastError: 'HTTP 403 Forbidden',
      lastFailureDiagnostic: { code: 'unauthorized' as const }, run: async () => {
        for (const totalTokens of [60, 50]) {
          const admission = options.requestGate!();
          expect(admission.allowed).toBe(true);
          if (admission.allowed) {
            requests();
            const receipt = { usage: { inputTokens: totalTokens - 10, outputTokens: 10, totalTokens }, complete: true };
            admission.settle(receipt); admission.settle(receipt);
          }
        }
        // A native cumulative notification may be delayed, duplicated, or include historical thread state.
        options.onUsage({ totalTokens: 10_000 });
        for (let retry = 0; retry < 3; retry++) expect(options.requestGate!()).toEqual({ allowed: false, reason: 'math_total_token_limit' });
        if (solved) fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
        return 'failed';
      }, close: vi.fn(), interrupt: vi.fn() }));
    expect(await runSolver([...args, '--max-turns', '20', '--max-total-tokens', '100', '--model', 'deepseek-flash', '--effort', 'high'], directory)).toBe(solved ? 0 : 4);
    const result = JSON.parse(fs.readFileSync(output, 'utf8'));
    expect(result).toMatchObject({ status: solved ? 'evaluated_passed' : 'limit_reached', turns: 1,
      usage: { totalTokens: 110, inputTokens: 90, outputTokens: 20 }, tokenBudget: {
        enforcement: 'provider-observed-upstream-request-limit', status: 'exhausted', reportedTotalTokens: 110, usageComplete: true } });
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.requestUsageAccounting).toEqual({ startedRequests: 2, reportedRequests: 2, pendingRequests: 0, incomplete: false });
    expect(state.lastFailure?.reason).toBe(solved ? undefined : 'math_total_token_limit');
    expect(state.usageAccounting).toMatchObject({ startedTurns: 1, reportedTurns: 1, pending: false, incomplete: false });
    expect(requests).toHaveBeenCalledTimes(2); expect(host.delay).not.toHaveBeenCalled();
    expect(host.officialGate).toHaveBeenCalledTimes(Number(solved));
  });

  it('uses complete receipts from concurrent peers before allowing their next internal request', async () => {
    host.verify.mockImplementation(async request => failed(verified(request)));
    let started = 0, settled = 0;
    const running = deferred(), consumed = deferred();
    const requests = vi.fn();
    host.createSession.mockImplementation(session(options => options.workspace, async options => {
      const admission = options.requestGate!(); expect(admission.allowed).toBe(true);
      if (admission.allowed) {
        requests(); if (++started === 2) running.resolve(); await running.promise;
        admission.settle({ usage: { totalTokens: 60, inputTokens: 50, outputTokens: 10 }, complete: true });
        if (++settled === 2) consumed.resolve(); await consumed.promise;
      }
      expect(options.requestGate!()).toEqual({ allowed: false, reason: 'math_total_token_limit' });
      return 'failed';
    }, { usageSource: 'upstream-requests' }));
    expect(await runSolver([...args, '--workers', '2', '--coordination', 'independent', '--max-turns', '20', '--max-total-tokens', '100'], directory)).toBe(4);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'limit_reached', reason: 'math_total_token_limit',
      usage: { totalTokens: 120 }, tokenBudget: { status: 'exhausted', usageComplete: true, overrunTokens: 20 } });
    expect(requests).toHaveBeenCalledTimes(2);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.workers.every((worker: any) => worker.requestUsageAccounting.startedRequests === 1 && !worker.requestUsageAccounting.incomplete)).toBe(true);
  });

  it('blocks internal requests immediately after a missing receipt and retains known earlier usage', async () => {
    host.verify.mockImplementation(async request => failed(verified(request)));
    host.createSession.mockImplementation(session('request-missing-usage', async options => {
      const first = options.requestGate!();
      if (first.allowed) first.settle({ usage: { totalTokens: 40, inputTokens: 30, outputTokens: 10 }, complete: true });
      const second = options.requestGate!();
      if (second.allowed) second.settle({ complete: false });
      expect(options.requestGate!()).toEqual({ allowed: false, reason: 'math_model_usage_unavailable' });
      options.onUsage({ totalTokens: 40 });
      return 'failed';
    }, { usageSource: 'upstream-requests' }));
    expect(await runSolver([...args, '--max-turns', '20', '--max-total-tokens', '100'], directory)).toBe(4);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'limit_reached', reason: 'math_model_usage_unavailable',
      usage: { totalTokens: 40 }, tokenBudget: { status: 'usage-unavailable', reportedTotalTokens: 40, usageComplete: false } });
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.requestUsageAccounting).toEqual({ startedRequests: 2, reportedRequests: 1, pendingRequests: 0, incomplete: true });
    expect(host.delay).not.toHaveBeenCalled();
  });

  it('keeps a peer rejected before its first upstream request at known zero consumption', async () => {
    host.verify.mockImplementation(async request => failed(verified(request)));
    let entered = 0;
    const running = deferred(), exhausted = deferred();
    host.createSession.mockImplementation(session(options => options.workspace, async options => {
      if (++entered === 2) running.resolve(); await running.promise;
      if (options.environment?.DEEPSCIENTIST_MATH_WORKER_ID === 'solver') {
        const admission = options.requestGate!();
        expect(admission.allowed).toBe(true);
        if (admission.allowed) admission.settle({ usage: { totalTokens: 120, inputTokens: 100, outputTokens: 20 }, complete: true });
        exhausted.resolve(); return 'completed';
      }
      await exhausted.promise;
      expect(options.requestGate!()).toEqual({ allowed: false, reason: 'math_total_token_limit' });
      return 'failed';
    }, { usageSource: 'upstream-requests' }));
    expect(await runSolver([...args, '--workers', '2', '--coordination', 'independent', '--max-turns', '20', '--max-total-tokens', '100'], directory)).toBe(4);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'limit_reached', reason: 'math_total_token_limit',
      usage: { totalTokens: 120 }, tokenBudget: { reportedTotalTokens: 120, usageComplete: true } });
    const peer = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8')).workers[1];
    expect(peer.turns).toBe(1); expect(peer.usage).toBeUndefined();
    expect(peer.requestUsageAccounting).toEqual({ startedRequests: 0, reportedRequests: 0, pendingRequests: 0, incomplete: false });
  });

  it.each([false, true])('adds receipts after resuming a thread and preserves its historical label (legacy: %s)', async legacy => {
    const profile = path.join(directory, 'request-resume-profile');
    prepareWestlakeProfile(profile, 'deepseek-flash', 'high');
    vi.stubEnv('CODEX_HOME', profile);
    const requestArgs = [...args, '--model', 'deepseek-flash', '--effort', 'high'];
    let turns = 0;
    host.verify.mockImplementation(async request => turns < 2 ? failed(verified(request)) : verified(request));
    host.createSession.mockImplementation(session(options => options.threadId ?? 'request-resume', async options => {
      const admission = options.requestGate!();
      expect(admission.allowed).toBe(true);
      if (admission.allowed) admission.settle({ usage: { totalTokens: 40, inputTokens: 30, outputTokens: 10 }, complete: true });
      options.onUsage({ totalTokens: 40 });
      if (++turns === 2) fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
      return 'completed';
    }, { usageSource: 'upstream-requests' }));
    expect(await runSolver([...requestArgs, '--max-total-tokens', '100'], directory)).toBe(4);
    expect(JSON.parse(fs.readFileSync(output, 'utf8')).usage.totalTokens).toBe(40);
    if (legacy) {
      const stateFile = `${output}.runtime/state.json`, state = JSON.parse(fs.readFileSync(stateFile, 'utf8'));
      delete state.requestUsageAccounting;
      state.tokenBudget.enforcement = 'provider-observed-dispatch-limit';
      fs.writeFileSync(stateFile, JSON.stringify(state));
    }
    expect(await runSolver([...requestArgs, '--resume', '--max-turns', '2'], directory)).toBe(0);
    expect(host.createSession.mock.calls[1][0].threadId).toBe('request-resume');
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ usage: { totalTokens: 80 },
      tokenBudget: { maxTotalTokens: 100, usageComplete: true, reportedTotalTokens: 80,
        enforcement: legacy ? 'provider-observed-dispatch-limit' : 'provider-observed-upstream-request-limit' } });
    expect(JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8')).requestUsageAccounting)
      .toEqual({ startedRequests: legacy ? 1 : 2, reportedRequests: legacy ? 1 : 2, pendingRequests: 0, incomplete: false });
  });

  it('keeps request consumption additive when context rotation creates a new thread', async () => {
    let turns = 0;
    host.verify.mockImplementation(async request => turns < 2 ? failed(verified(request)) : verified(request));
    host.createSession.mockImplementation(async (options: MathAgentOptions) => {
      const first = host.createSession.mock.calls.length === 1;
      if (!first) expect(options.threadId).toBeUndefined();
      return { threadId: first ? 'request-large-context' : 'request-new-context',
        usageSource: 'upstream-requests', lastInputTokens: first ? 100_000 : 1000, run: async () => {
          const admission = options.requestGate!(); expect(admission.allowed).toBe(true);
          if (admission.allowed) admission.settle({ usage: { totalTokens: 40, inputTokens: 30, outputTokens: 10 }, complete: true });
          options.onUsage({ totalTokens: first ? 110_000 : 2000 });
          if (++turns === 2) fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
          return 'completed';
        }, close: vi.fn(), interrupt: vi.fn() };
    });
    expect(await runSolver([...args, '--max-turns', '2', '--max-total-tokens', '100'], directory)).toBe(0);
    expect(host.createSession).toHaveBeenCalledTimes(2);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.previousThreadIds).toEqual(['request-large-context']);
    expect(state.usage.totalTokens).toBe(80);
    expect(state.usageBeforeThread.totalTokens).toBe(40);
    expect(state.requestUsageAccounting).toEqual({ startedRequests: 2, reportedRequests: 2, pendingRequests: 0, incomplete: false });
    expect(state.tokenBudget).toMatchObject({ reportedTotalTokens: 80, usageComplete: true, status: 'available' });
  });

  it.each([false, true])('fails closed on unavailable completed usage with a finite allowance (partial: %s)', async partial => {
    host.verify.mockImplementation(async request => failed(verified(request)));
    const runs = vi.fn();
    let started = 0;
    const running = deferred();
    host.createSession.mockImplementation(session(options => options.workspace, async options => {
      runs(); if (++started === (partial ? 2 : 1)) running.resolve(); await running.promise;
      if (partial && options.environment?.DEEPSCIENTIST_MATH_WORKER_ID === 'solver') options.onUsage({ totalTokens: 40 });
      return 'completed';
    }));
    expect(await runSolver([...args, '--workers', partial ? '2' : '1', '--coordination', 'independent',
      '--max-turns', '20', '--max-total-tokens', '100'], directory)).toBe(4);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'limit_reached', reason: 'math_model_usage_unavailable',
      tokenBudget: { status: 'usage-unavailable', usageComplete: false, reportedTotalTokens: partial ? 40 : null } });
    expect(runs).toHaveBeenCalledTimes(partial ? 2 : 1);
    expect(host.officialGate).not.toHaveBeenCalled();
  });

  it.each(['transport', 'exception', 'failed', 'checkpoint', 'interrupted'] as const)
  ('keeps intermediate usage incomplete after a %s model turn with a finite allowance', async failure => {
    host.verify.mockImplementation(async request => failed(verified(request)));
    const runs = vi.fn();
    host.createSession.mockImplementation(session('partial-token-usage', async options => {
      runs(); options.onUsage({ totalTokens: 40 });
      if (failure === 'transport') throw new Error('math_codex_transport_closed:fixture');
      if (failure === 'exception') throw new Error('fixture_request_exception');
      return failure;
    }, { lastError: 'math_codex_transport_closed:fixture' }));
    expect(await runSolver([...args, '--max-turns', '20', '--max-total-tokens', '100'], directory)).toBe(4);
    expect(runs).toHaveBeenCalledOnce();
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({
      status: 'limit_reached', reason: 'math_model_usage_unavailable',
      usage: { totalTokens: 40 }, tokenBudget: { status: 'usage-unavailable', reportedTotalTokens: 40, usageComplete: false } });
    expect(JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8')).usageAccounting).toMatchObject({
      startedTurns: 1, reportedTurns: 0, incomplete: true, pending: false });
    expect(host.delay).not.toHaveBeenCalled();
    expect(host.officialGate).not.toHaveBeenCalled();
  });

  it.each(['reported-first', 'missing-first'] as const)
  ('preserves missing request usage inside a completed tool roundtrip (%s)', async order => {
    host.verify.mockImplementation(async request => failed(verified(request)));
    const runs = vi.fn();
    host.createSession.mockImplementation(session('mixed-request-usage', async options => {
      runs();
      expect(options.onUsageIncomplete).toBeTypeOf('function');
      if (order === 'missing-first') options.onUsageIncomplete!();
      options.onUsage({ totalTokens: 40 });
      if (order === 'reported-first') options.onUsageIncomplete!();
      return 'completed';
    }));
    expect(await runSolver([...args, '--max-turns', '20', '--max-total-tokens', '100'], directory)).toBe(4);
    expect(runs).toHaveBeenCalledOnce();
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({
      status: 'limit_reached', reason: 'math_model_usage_unavailable', usage: { totalTokens: 40 },
      tokenBudget: { status: 'usage-unavailable', usageComplete: false, reportedTotalTokens: 40 } });
    expect(JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8')).usageAccounting).toMatchObject({
      startedTurns: 1, reportedTurns: 0, incomplete: true, pending: false });
    expect(host.officialGate).not.toHaveBeenCalled();
  });

  it('retains partial request usage across later completed turns with an unlimited allowance', async () => {
    let turns = 0;
    host.verify.mockImplementation(async request => turns < 2 ? failed(verified(request)) : verified(request));
    host.createSession.mockImplementation(session('mixed-request-unlimited', async options => {
      options.onUsage({ totalTokens: ++turns * 40 });
      if (turns === 1) options.onUsageIncomplete!();
      else fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'),
        original.replaceAll('by sorry', 'by trivial'));
      return 'completed';
    }));
    expect(await runSolver([...args, '--max-turns', '2', '--max-total-tokens', '0'], directory)).toBe(0);
    expect(turns).toBe(2);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'evaluated_passed', usage: { totalTokens: 80 },
      tokenBudget: { status: 'unlimited', reportedTotalTokens: 80, usageComplete: false } });
    expect(JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8')).usageAccounting).toMatchObject({
      startedTurns: 2, reportedTurns: 1, incomplete: true, pending: false });
  });

  it('keeps partial usage visible while preserving unlimited retries after a transport failure', async () => {
    let turns = 0;
    host.verify.mockImplementation(async request => turns < 2 ? failed(verified(request)) : verified(request));
    host.createSession.mockImplementation(session(() => `partial-token-${host.createSession.mock.calls.length}`, async options => {
      options.onUsage({ totalTokens: 40 });
      if (++turns === 1) throw new Error('math_codex_transport_closed:fixture');
      fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
      return 'completed';
    }, { lastError: 'math_codex_transport_closed:fixture' }));
    expect(await runSolver([...args, '--max-turns', '2', '--max-total-tokens', '0'], directory)).toBe(0);
    expect(turns).toBe(2);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'evaluated_passed', usage: { totalTokens: 80 },
      tokenBudget: { status: 'unlimited', reportedTotalTokens: 80, usageComplete: false } });
  });

  it('rechecks the shared allowance after opening a session while another worker consumes it', async () => {
    host.verify.mockImplementation(async request => failed(verified(request)));
    const peerOpening = deferred(), allowanceConsumed = deferred();
    const runs = vi.fn();
    host.createSession.mockImplementation(async (options: MathAgentOptions) => {
      const lead = options.environment?.DEEPSCIENTIST_MATH_WORKER_ID === 'solver';
      if (!lead) { peerOpening.resolve(); await allowanceConsumed.promise; }
      return { threadId: options.workspace, run: async () => {
        runs(); await peerOpening.promise;
        options.onUsage({ totalTokens: 100 }); allowanceConsumed.resolve(); return 'completed';
      }, close: vi.fn(), interrupt: vi.fn() };
    });
    expect(await runSolver([...args, '--workers', '2', '--coordination', 'independent', '--max-turns', '20',
      '--max-total-tokens', '100'], directory)).toBe(4);
    expect(host.createSession).toHaveBeenCalledTimes(2);
    expect(runs).toHaveBeenCalledOnce();
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'limit_reached', turns: 1,
      tokenBudget: { status: 'exhausted', reportedTotalTokens: 100, usageComplete: true } });
  });

  it('admits the actual model request atomically after asynchronous turn preparation', async () => {
    host.verify.mockImplementation(async request => failed(verified(request)));
    const runs = vi.fn();
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ threadId: options.workspace,
      run: async () => { runs(); options.onUsage({ totalTokens: 100 }); return 'completed'; },
      close: vi.fn(), interrupt: vi.fn() }));
    expect(await runSolver([...args, '--workers', '2', '--coordination', 'independent', '--max-turns', '20',
      '--max-total-tokens', '100'], directory)).toBe(4);
    expect(runs).toHaveBeenCalledOnce();
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ turns: 1, dispatchCounts: { proof: 1 },
      tokenBudget: { status: 'exhausted', reportedTotalTokens: 100, usageComplete: true } });
  });

  it.each([80, 0])('retains the cumulative token allowance on resume and allows explicitly changing it to %s', async allowance => {
    let turns = 0;
    host.verify.mockImplementation(async request => turns < 2 ? failed(verified(request)) : verified(request));
    host.createSession.mockImplementation(session('token-resume', async options => {
      options.onUsage({ totalTokens: ++turns * 30 });
      if (turns === 2) fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'),
        original.replaceAll('by sorry', 'by trivial'));
      return 'completed';
    }));
    expect(await runSolver([...args, '--max-turns', '20', '--max-total-tokens', '30'], directory)).toBe(4);
    expect(turns).toBe(1);
    // Omitting the option must not silently turn a saved finite allowance into unlimited work.
    expect(await runSolver([...args, '--resume', '--max-turns', '20'], directory)).toBe(4);
    expect(turns).toBe(1);
    expect(await runSolver([...args, '--resume', '--max-turns', '20', '--max-total-tokens', '25'], directory)).toBe(4);
    expect(JSON.parse(fs.readFileSync(output, 'utf8')).tokenBudget).toMatchObject({ reportedTotalTokens: 30, overrunTokens: 5 });
    expect(turns).toBe(1);
    expect(await runSolver([...args, '--resume', '--max-turns', '20', '--max-total-tokens', String(allowance)], directory)).toBe(0);
    expect(turns).toBe(2);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'evaluated_passed', usage: { totalTokens: 60 },
      tokenBudget: { maxTotalTokens: allowance, reportedTotalTokens: 60, usageComplete: true } });
    expect(host.createSession).toHaveBeenCalledTimes(2);
  });

  it.each(['coordination', 'scheduler'])('freezes the CLI %s policy across resume', async policy => {
    expect(await runSolver([...args, '--startup-only'], directory)).toBe(0);
    const prepared = fs.readFileSync(output, 'utf8');
    expect(await runSolver([...args, '--resume', `--${policy}`, policy === 'scheduler' ? 'goals-first' : 'independent'], directory)).toBe(1);
    expect(fs.readFileSync(output, 'utf8')).toBe(prepared);
    expect(host.createSession).not.toHaveBeenCalled();
  });

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

  it('provides source recovery guidance and permits a repaired saved file without relaxing checks', () => {
    const file = path.join(project, 'Submission.lean');
    const helper = 'lemma helper : True := by trivial\n';
    fs.writeFileSync(file, original.replace('theorem first', `open scoped BigOperators\n${helper}theorem first`));
    let error: unknown;
    try { assertSolverProjectSources(problem, project); } catch (caught) { error = caught; }
    expect(error).toBeInstanceOf(SolverSourceError);
    expect(error).toMatchObject({ message: 'math_original_context_changed', proofPath: 'Submission.lean' });
    expect((error as SolverSourceError).recovery).toContain('inside their proofs');
    fs.writeFileSync(file, original.replace('theorem first', helper + 'theorem first'));
    expect(() => assertSolverProjectSources(problem, project)).not.toThrow();
    fs.writeFileSync(file, original.replace('fixed : Nat := 2', 'fixed : Nat := 3'));
    try { assertSolverProjectSources(problem, project); } catch (caught) { error = caught; }
    expect(error).toMatchObject({ message: 'math_original_declaration_changed', declarationName: 'fixed' });
    expect((error as SolverSourceError).recovery).toContain('fixed');
  });

  it.each(['first', 'second'])('projects documented declarations without orphan comments when keeping %s', target => {
    const source = original
      .replace('theorem first', '/-! Module documentation. -/\n/-- First /- nested -/ documentation. -/\ntheorem first')
      .replace('theorem second', '/-- Second documentation. -/\ntheorem second')
      .replace(`${target} : True := by sorry`, `${target} : True := by trivial`)
      .replace('end Submission', 'def marker : String := "/-- literal -/"\n/-- Hidden helper documentation. -/\nlemma hidden : True := by trivial\nend Submission');
    fs.writeFileSync(path.join(project, 'Submission.lean'), source);
    git(workspace, ['add', 'generated/p/Submission.lean']);
    commitFixture(workspace, 'Documented baseline');
    problem = readSolverProblem(workspace, problem.activeProblemPath);
    const commit = commitSolverSources(problem, workspace);
    const task: CooperativeTask = { id: target, kind: 'goal', objective: 'Prove the target', dependsOn: [], revision: 0,
      proofPath: 'Submission.lean', theoremName: `Submission.${target}` };
    const projected = createTaskSourceProjector(problem, workspace, commit)(task, []).get('Submission.lean')!;
    expect(projected).toContain(`theorem ${target} : True := by trivial`);
    expect(projected).not.toContain(`theorem ${target === 'first' ? 'second' : 'first'}`);
    expect(projected).toContain('lemma hidden');
    expect(projected).not.toMatch(/documentation/iu);
    expect(projected).toContain('def marker : String := "/-- literal -/"');
    expect(projected).toContain('namespace Submission');
    expect(projected).toContain('end Submission');
    expect(fs.readFileSync(path.join(project, 'Submission.lean'), 'utf8')).toBe(source);
  });

  it.each([
    ['', 'math_task_missing_declaration'],
    ['lemma BranchA.helper : True := by trivial\nlemma BranchB.helper : True := by trivial\n', 'math_task_ambiguous_declaration'],
    ['def helper : True := by trivial\n', 'math_task_requires_theorem'],
  ])('distinguishes an invalid assigned declaration: %s', (helper, code) => {
    fs.writeFileSync(path.join(project, 'Submission.lean'), original.replace('theorem first', helper + 'theorem first'));
    const commit = commitSolverSources(problem, workspace);
    const task: CooperativeTask = { id: 'helper', kind: 'lemma', objective: 'Prove the helper', dependsOn: [], revision: 0,
      proofPath: 'Submission.lean', theoremName: 'Submission.helper', type: 'True' };
    expect(() => createTaskSourceProjector(problem, workspace, commit)(task, [])).toThrow(code);
    expect(() => createTaskSourceProjector(problem, workspace, commit)(task, [])).toThrow('Target: Submission.helper');
    expect(host.verify).not.toHaveBeenCalled();
  });

  it('checks and merges only the body of a configured original definition goal', async () => {
    const { source, task } = configureDefinitionGoal();
    const candidate = source.replace('C : Nat := by sorry', 'C : Nat := 7');
    fs.writeFileSync(path.join(project, 'Submission.lean'), candidate);
    const commit = commitSolverSources(problem, workspace);
    host.verify.mockImplementation(async request => {
      const projected = fs.readFileSync(path.join(request.projectRoot, 'Submission.lean'), 'utf8');
      expect(projected).toContain('noncomputable def C : Nat := 7');
      expect(projected).toContain('def fixed : Nat := 2');
      expect(projected).not.toContain('theorem first');
      expect(projected).not.toContain('theorem second');
      expect(projected).not.toContain('sorry');
      expect(request.items.map(item => item.theoremName)).toEqual(['Submission.C']);
      return verified(request);
    });
    const proof = await checkTaskProof(problem, workspace, commit, task,
      { taskId: task.id, taskDigest: taskVersion(task), workerId: 'engineer', seedCommit: problem.baseCommit },
      [], {}, new AbortController().signal);
    expect(proof.passed).toBe(true);
    expect(host.verify).toHaveBeenCalledOnce();
    expect(proof.changes).toEqual([{ file: 'Submission.lean', name: 'C',
      before: 'noncomputable def C : Nat := by sorry\n', after: 'noncomputable def C : Nat := 7\n' }]);
    await withSolverWorktree(workspace, problem.baseCommit, async checkout => {
      const file = path.join(checkout, problem.projectRelative, 'Submission.lean');
      const peer = 'lemma peer : True := by trivial\n';
      fs.writeFileSync(file, source.replace('theorem first', peer + 'theorem first'));
      applyTaskChanges(problem, checkout, proof.changes);
      expect(fs.readFileSync(file, 'utf8')).toBe(candidate.replace('theorem first', peer + 'theorem first'));
      expect(() => assertSolverSources(problem, checkout)).not.toThrow();
    });
  });

  it('checks an exact original definition using a host-bound unfinished typed input', async () => {
    const { source, task: originalTask } = configureDefinitionGoal();
    const helper: CooperativeTask = { id: 'helper', kind: 'lemma', objective: 'Supply the construction input',
      type: 'True', theoremName: 'Submission.helper', proofPath: 'Submission.lean', dependsOn: [], revision: 0 };
    const task = { ...originalTask, dependsOn: [helper.id] };
    const tasks: TaskRecord[] = [helper, task].map(task => ({ task, status: 'pending', attempts: 0 }));
    const assignment = { taskId: task.id, taskDigest: taskVersion(task), workerId: 'engineer', seedCommit: problem.baseCommit,
      dependencies: [{ taskId: helper.id, taskDigest: taskVersion(helper) }] };
    const dispatched = { ...assignment, connectionCheck: createTaskConnectionCheck(task, assignment, tasks,
      { environmentDigest: 'fixture', problemReceiptDigest: problem.receiptDigest }) };
    fs.writeFileSync(path.join(project, 'Submission.lean'), source.replace('C : Nat := by sorry',
      'C : Nat := by\n  have h : True := Submission.helper\n  exact 7'));
    const commit = commitSolverSources(problem, workspace);
    host.verify.mockImplementation(async request => {
      const projected = fs.readFileSync(path.join(request.projectRoot, 'Submission.lean'), 'utf8');
      expect(projected).toContain('noncomputable def C (helper : True) : Nat := by');
      expect(projected).toContain('have h : True := helper');
      expect(projected).not.toContain('sorry'); return verified(request);
    });
    const proof = await checkTaskProof(problem, workspace, commit, task, dispatched,
      [], {}, new AbortController().signal, Infinity, [helper], 'fixture');
    expect(proof.passed).toBe(true);
    expect(proof.conditions).toEqual(assignment.dependencies);
    expect(proof.changes[0].after).not.toContain('(helper : True)');
    expect(host.verify).toHaveBeenCalledOnce();
  });

  it.each([
    { name: 'a changed type', edit: (source: string) => source.replace('C : Nat', 'C : Int'), error: 'math_original_declaration_changed' },
    { name: 'an added parameter', edit: (source: string) => source.replace('C : Nat', 'C (n : Nat) : Nat'), error: 'math_original_declaration_changed' },
    { name: 'a renamed target', edit: (source: string) => source.replace('def C : Nat', 'def otherC : Nat'), error: 'math_original_declaration_changed' },
    { name: 'a different namespace', edit: (source: string) => source.replace('def C : Nat', 'def Other.C : Nat'), error: 'math_original_declaration_changed' },
    { name: 'a changed frozen context', edit: (source: string) => source.replace('noncomputable def C', 'variable (extra : False)\nnoncomputable def C'), error: 'math_original_context_changed' },
    { name: 'a changed non-target definition', edit: (source: string) => source.replace('fixed : Nat := 2', 'fixed : Nat := 3'), error: 'math_original_declaration_changed' },
    { name: 'another original goal proof', edit: (source: string) => source.replace('first : True := by sorry', 'first : True := by trivial'), error: 'math_task_existing_declaration_changed' },
    { name: 'an abbrev in place of the original def', edit: (source: string) => source.replace('def C : Nat', 'abbrev C : Nat'), error: 'math_task_requires_theorem' },
    { name: 'a theorem in place of the original def', edit: (source: string) => source.replace('def C : Nat', 'theorem C : Nat'), error: 'math_task_requires_theorem' },
  ])('rejects $name before checking an original definition goal', async ({ edit, error }) => {
    const { source, task } = configureDefinitionGoal();
    fs.writeFileSync(path.join(project, 'Submission.lean'), edit(source.replace('C : Nat := by sorry', 'C : Nat := 7')));
    git(workspace, ['add', '--', 'generated/p/Submission.lean']);
    commitFixture(workspace, 'Invalid definition candidate');
    const commit = git(workspace, ['rev-parse', 'HEAD']);
    await expect(checkTaskProof(problem, workspace, commit, task,
      { taskId: task.id, taskDigest: taskVersion(task), workerId: 'engineer', seedCommit: problem.baseCommit },
      [], {}, new AbortController().signal)).rejects.toThrow(error);
    expect(host.verify).not.toHaveBeenCalled();
  });

  it.each([
    { kind: 'lemma' as const, theoremName: 'Submission.helper', type: 'Nat' },
    { kind: 'lemma' as const, theoremName: 'Submission.C', type: 'Nat' },
    { kind: 'goal' as const, theoremName: 'Submission.helper' },
    { kind: 'goal' as const, theoremName: 'Other.C' },
  ])('rejects definition impersonation through $kind target $theoremName', impostor => {
    const { source, task } = configureDefinitionGoal();
    fs.writeFileSync(path.join(project, 'Submission.lean'), source.replace('theorem first', 'def helper : Nat := 7\ntheorem first'));
    const commit = commitSolverSources(problem, workspace);
    expect(() => createTaskSourceProjector(problem, workspace, commit)({ ...task, ...impostor }, []))
      .toThrow('math_task_requires_theorem');
    expect(host.verify).not.toHaveBeenCalled();
  });

  it('allows explicit Mathlib imports while preserving original imports and trusted inputs', () => {
    const file = path.join(project, 'Submission.lean');
    const baseline = 'import Mathlib.Data.Nat.Basic\n' + original;
    fs.writeFileSync(file, baseline);
    commitSolverSources(problem, workspace);
    problem = readSolverProblem(workspace, problem.activeProblemPath);
    expect(problem.sourceImports?.['Submission.lean']).toEqual(['Mathlib.Data.Nat.Basic']);
    const candidate = 'import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv\n' + baseline;
    fs.writeFileSync(file, candidate);
    expect(() => assertSolverSources(problem, workspace)).not.toThrow();
    const { sourceImports: _imports, ...legacy } = problem;
    expect(() => assertSolverProjectSources(legacy, project)).toThrow('math_original_context_changed');
    for (const source of [original, candidate.replace('import Mathlib.Data.Nat.Basic\n', ''),
      ...['import Other', 'import Solution', 'import Mathlib', 'import Mathlib.Data.Real.Basic variable (h : False)']
        .map(command => command + '\n' + baseline)]) {
      fs.writeFileSync(file, source);
      expect(() => assertSolverProjectSources(problem, project)).toThrow('math_original_context_changed');
    }
    fs.writeFileSync(file, candidate);
    fs.writeFileSync(path.join(project, 'Challenge.lean'), 'import Mathlib.Data.Nat.Basic\n' + original);
    expect(() => assertSolverSources(problem, workspace)).toThrow('math_trusted_source_changed');
  });

  it.each([false, true])('allows helpers to import frozen public modules and rejects cycles (cycle: %s)', cycle => {
    const helper = 'Submission/Helpers.lean';
    fs.mkdirSync(path.join(project, 'Submission'));
    fs.writeFileSync(path.join(project, helper), '');
    fs.writeFileSync(path.join(project, 'ChallengeDeps.lean'), (cycle ? 'import Submission.Helpers\n' : '') + 'def publicSeed : Nat := 1\n');
    fs.writeFileSync(path.join(project, 'Submission.lean'), 'import ChallengeDeps\nimport Submission.Helpers\n' + original);
    const receipt = JSON.parse(fs.readFileSync(problem.activeProblemPath, 'utf8'));
    receipt.solverOwnedFiles.push(helper); receipt.trustedFiles.push('ChallengeDeps.lean');
    fs.writeFileSync(problem.activeProblemPath, JSON.stringify(receipt));
    git(workspace, ['add', 'generated']);
    commitFixture(workspace, 'Freeze public imports');
    problem = readSolverProblem(workspace, problem.activeProblemPath);
    fs.writeFileSync(path.join(project, helper), 'import ChallengeDeps\n');
    if (cycle) expect(() => assertSolverSources(problem, workspace)).toThrow('math_local_module_import_cycle');
    else {
      expect(() => assertSolverSources(problem, workspace)).not.toThrow();
      fs.writeFileSync(path.join(project, helper), '');
      applyTaskChanges(problem, workspace, [], [{ file: helper, module: 'ChallengeDeps' }]);
      expect(fs.readFileSync(path.join(project, helper), 'utf8')).toBe('import ChallengeDeps\n');
      expect(() => applyTaskChanges(problem, workspace, [], [{ file: helper, module: 'Solution' }])).toThrow('math_task_source_outside_scope');
    }
  });

  it('passes the frozen import policy to model-side diagnostic constraints', async () => {
    expect(await runSolver([...args, '--startup-only'], directory)).toBe(0);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    const prepared = path.join(state.worktree, problem.projectRelative);
    const constraints = JSON.parse(fs.readFileSync(path.join(prepared, '.lake/source-constraints.json'), 'utf8'));
    expect(constraints.sourceImports).toEqual(problem.sourceImports);
    fs.writeFileSync(path.join(prepared, 'Submission.lean'), 'import Mathlib.Data.Nat.Basic\n' + original);
    expect(() => assertSolverProjectSources(constraints, prepared)).not.toThrow();
    expect(host.createSession).not.toHaveBeenCalled();
  });

  it('allows single-name type queries while rejecting context changes beside them', () => {
    const file = path.join(project, 'Submission.lean');
    const probe = original.replace('theorem first', '#check Finset.sum_eq_single\n#check Nat.add_comm\ntheorem first');
    fs.writeFileSync(file, probe);
    expect(() => assertSolverProjectSources(problem, project)).not.toThrow();
    expect(() => assertSolverSources(problem, workspace)).not.toThrow();
    for (const command of ['#check True variable (h : False)', '#check True\nvariable (h : False)',
      '#check True\nset_option autoImplicit true', '#check True\nimport Other']) {
      fs.writeFileSync(file, original.replace('theorem first', `${command}\ntheorem first`));
      expect(() => assertSolverProjectSources(problem, project)).toThrow('math_original_context_changed');
    }
    fs.writeFileSync(file, probe.replace('first : True', 'first : False'));
    expect(() => assertSolverProjectSources(problem, project)).toThrow('math_original_declaration_changed');
  });

  it('allows read-only instance queries with bare and parenthesized types while rejecting trailing commands', () => {
    const file = path.join(project, 'Submission.lean');
    const probe = original.replace('theorem first',
      '#synth Finite ({-1, 1} : Set ℤ)\n#synth Fintype ({-1, 1} : Set ℤ)\n' +
      '#synth Fintype (Fin (2 + 1))\n#synth NormedSpace (ℝ) (X)\n#synth Nontrivial\n' +
      '#synth MeasureSpace ℝ\n#synth Fintype Nat\n#synth NormedSpace ℝ X\ntheorem first');
    fs.writeFileSync(file, probe);
    expect(() => assertSolverProjectSources(problem, project)).not.toThrow();
    expect(() => assertSolverSources(problem, workspace)).not.toThrow();
    for (const command of ['#synth True variable (h : False)', '#synth Fintype ({-1, 1} : Set ℤ)\nvariable (h : False)',
      '#synth Fintype (Nat) variable (h : False)', '#synth Fintype (Nat) import Other',
      '#synth Fintype (Nat) set_option autoImplicit true', '#synth Fintype (Nat)\nimport Other',
      '#synth Fintype (Nat)\nset_option autoImplicit true', '#synth Fintype (Nat); import Other',
      '#synth Fintype Nat variable (h : False)', '#synth MeasureSpace ℝ import Other',
      '#synth NormedSpace ℝ X set_option autoImplicit true', '#synth Fintype ((Nat)', '#synth Fintype (Nat))']) {
      fs.writeFileSync(file, original.replace('theorem first', `${command}\ntheorem first`));
      expect(() => assertSolverProjectSources(problem, project)).toThrow('math_original_context_changed');
    }
    fs.writeFileSync(file, probe.replace('first : True', 'first : False'));
    expect(() => assertSolverProjectSources(problem, project)).toThrow('math_original_declaration_changed');
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
    const checkpoint = 'Checked helper: keep this proof.\n' + 'x'.repeat(20000) + '\nNext step: apply the retained helper to the final goal.';
    host.verify.mockImplementation(async request => turn === 1 ? failed(verified(request), { stdoutPreview: unsolved }) : verified(request));
    host.createSession.mockImplementation(async (options: MathAgentOptions) => {
      const first = host.createSession.mock.calls.length === 1;
      return { threadId: first ? 'large-thread' : 'continued-thread', lastInputTokens: first ? 100_000 : 1000,
        close: first ? closes[0] : closes[1], interrupt: vi.fn(), run: async (message: string) => {
          messages.push(message); turn++;
          if (first) {
            fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), checkpoint);
            fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replace('by sorry', 'by trivial'));
          } else {
            expect(options.threadId).toBeUndefined();
            expect(message).toContain(checkpoint);
            expect(message).toContain('Original problem:');
            expect(message).toContain('unsolved goals');
            const manifest = JSON.parse(message.split('Context compilation manifest:\n')[1]);
            expect(manifest.usedBytes).toBeLessThanOrEqual(manifest.maxBytes);
            expect(manifest.included).toContainEqual(expect.objectContaining({ id: 'checkpoint', required: false }));
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
    host.createSession.mockImplementation(session('fixture-thread', async (options, message) => {
      messages.push(message);
      if (messages.length === 2) {
        expect(host.verify).not.toHaveBeenCalled();
        expect(git(options.workspace, ['rev-parse', 'HEAD'])).toBe(problem.baseCommit);
        expect(fs.readFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), 'utf8')).toContain('lemma helper');
      }
      fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'),
        messages.length === 1 ? withHelper.replace(from, to) : withHelper);
      return 'completed';
    }));
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
    host.createSession.mockImplementation(session('fixture-thread', async options => {
      fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replace('first : True', 'first : False'));
      return 'completed';
    }));
    expect(await runSolver([...args, '--max-turns', '2'], directory)).toBe(4);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'incomplete', turns: 2,
      solution_commit: null, solver_ready_receipt_valid: false, evaluator: { status: 'skipped' } });
    expect(host.verify).not.toHaveBeenCalled();
    expect(host.officialGate).not.toHaveBeenCalled();
    expect(git(workspace, ['rev-parse', 'HEAD'])).toBe(problem.baseCommit);
    const messages: string[] = [];
    host.createSession.mockImplementation(session(options => options.threadId!, async (options, message) => {
      messages.push(message);
      fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
      return 'completed';
    }));
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
    for (const corrupt of [
      (batch: MathematicsVerifierBatchResult) => batch.results.pop(),
      (batch: MathematicsVerifierBatchResult) => batch.results.push(batch.results[0]),
      (batch: MathematicsVerifierBatchResult) => batch.results.reverse(),
      (batch: MathematicsVerifierBatchResult) => { batch.targetCommit = 'b'.repeat(40); },
      (batch: MathematicsVerifierBatchResult) => { batch.status = 'failed'; },
    ]) {
      host.verify.mockImplementation(async request => { const batch = verified(request); corrupt(batch); return batch; });
      expect((await checkSolverProof(problem, workspace, {})).passed).toBe(false);
    }
    for (const [field, value] of Object.entries({ status: 'failed', targetCommit: 'b'.repeat(40), proofPath: 'wrong.lean',
      theoremName: 'wrong', statementHash: 'wrong', leanStatementHash: 'wrong', sourceDeclarationHash: 'wrong', claim: 'negation' })) {
      host.verify.mockImplementation(async request => { const batch = verified(request); Object.assign(batch.results[0], { [field]: value }); return batch; });
      expect((await checkSolverProof(problem, workspace, {})).passed, field).toBe(false);
    }
  });

  it('ignores a worker diagnostic log but not a tracked or nested one', () => {
    fs.writeFileSync(path.join(workspace, 'check-lean-submission.log'), 'diagnostic output\n');
    expect(() => assertSolverSources(problem, workspace)).not.toThrow();
    fs.writeFileSync(path.join(project, 'probe.log'), 'diagnostic output\n');
    expect(() => assertSolverSources(problem, workspace)).toThrow('math_source_outside_ownership');
    fs.unlinkSync(path.join(project, 'probe.log'));
    fs.writeFileSync(path.join(workspace, 'tracked.log'), 'committed on purpose\n');
    git(workspace, ['add', '--', 'tracked.log']);
    git(workspace, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--no-gpg-sign', '--quiet',
      '-m', 'Track a log']);
    fs.writeFileSync(path.join(workspace, 'tracked.log'), 'changed after the commit\n');
    expect(() => assertSolverSources(problem, workspace)).toThrow('math_source_outside_ownership');
    fs.unlinkSync(path.join(workspace, 'tracked.log'));
    fs.unlinkSync(path.join(workspace, 'check-lean-submission.log'));
  });

  it('keeps changing host journals outside the strict clean-checkout boundary', async () => {
    const journals = ['COOPERATION.json', 'CONTEXT-MANIFEST.json', 'DELIVERIES.jsonl', `DELIVERIES-${'a'.repeat(64)}.jsonl`];
    for (const file of journals) fs.writeFileSync(path.join(workspace, file), '{}\n');
    fs.writeFileSync(path.join(project, 'Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
    fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), 'Checked both original targets.');
    host.verify.mockImplementation(async request => {
      expect(git(request.projectRoot, ['status', '--porcelain=v1', '--untracked-files=all'])).toBe('');
      expect(git(request.projectRoot, ['rev-parse', 'HEAD'])).toBe(request.targetCommit);
      return verified(request);
    });
    const first = await checkSolverProof(problem, workspace, {});
    expect(first.passed).toBe(true);
    expect(git(workspace, ['ls-files', '--', ...journals])).toBe('');
    const exclude = path.resolve(workspace, git(workspace, ['rev-parse', '--git-path', 'info/exclude']));
    const rules = fs.readFileSync(exclude, 'utf8');
    for (const file of journals) fs.appendFileSync(path.join(workspace, file), '{"update":true}\n');
    const next = await checkSolverProof(problem, workspace, {}, undefined, first);
    expect(next.passed).toBe(true);
    expect(next.commit).toBe(first.commit);
    expect(fs.readFileSync(exclude, 'utf8')).toBe(rules);
    fs.writeFileSync(path.join(workspace, 'DELIVERIES-invalid.jsonl'), '{}\n');
    await expect(checkSolverProof(problem, workspace, {})).rejects.toThrow('math_source_outside_ownership');
    expect(host.verify).toHaveBeenCalledTimes(2);
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
    commitFixture(workspace, 'Canonical challenge namespace');
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

  it('reuses identical Lean rejections across notes while rechecking changed proofs and source constraints', async () => {
    host.verify.mockImplementation(async request => failed(verified(request), { stdoutPreview: unsolved }));
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
    expect(notes.verification).toBe(changed.verification);
    expect(notes.verification.targetCommit).toBe(changed.commit);
    expect(host.verify).toHaveBeenCalledTimes(2);
    const controller = new AbortController();
    controller.abort();
    await expect(checkSolverProof(problem, workspace, {}, controller.signal, notes)).rejects.toThrow();
    fs.writeFileSync(path.join(project, 'Submission.lean'), original.replace('first : True', 'first : False'));
    await expect(checkSolverProof(problem, workspace, {}, undefined, notes)).rejects.toThrow('math_original_declaration_changed');
    expect(host.verify).toHaveBeenCalledTimes(2);
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

  it.each(['winner', 'main'])('rejects completed-result reuse after the %s proof changes', async location => {
    expect(await runSolver(args, directory)).toBe(0);
    const worktree = location === 'main' ? workspace : path.join(`${output}.runtime`, 'worktree');
    const file = path.join(worktree, 'generated/p/Submission.lean');
    fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('by trivial', 'by exact True.intro'));
    expect(await runSolver([...args, '--resume'], directory)).toBe(1);
    expect(host.createSession).toHaveBeenCalledTimes(1);
    expect(console.log).toHaveBeenCalledWith(expect.stringContaining('math_resume_completed_proof_changed'));
  });

  it('rejects malformed restored control state before starting a model', async () => {
    expect(await runSolver([...args, '--startup-only'], directory)).toBe(0);
    const stateFile = `${output}.runtime/state.json`, state = JSON.parse(fs.readFileSync(stateFile, 'utf8'));
    state.turns = -1; fs.writeFileSync(stateFile, JSON.stringify(state));
    expect(await runSolver([...args, '--resume'], directory)).toBe(1);
    expect(host.createSession).not.toHaveBeenCalled();
    expect(console.log).toHaveBeenCalledWith(expect.stringContaining('math_resume_state_invalid:turns'));
  });

  it.each(['uncommitted', 'committed'])('rejects a %s change to the main workspace before adopting a checked proof', async change => {
    let changedHead: string;
    const check = async (...inputs: Parameters<typeof checkSolverProof>) => {
      const receipt = await checkSolverProof(...inputs);
      fs.writeFileSync(path.join(project, 'Submission.lean'), original.replaceAll('by sorry', 'by exact True.intro'));
      if (change === 'committed') commitSolverSources(problem, workspace);
      changedHead = git(workspace, ['rev-parse', 'HEAD']);
      return receipt;
    };
    expect(await runSolver(args, directory, { ...directSolverModules, M2: { ...directSolverModules.M2, check } })).toBe(1);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'runtime_error', reason: 'math_main_workspace_changed' });
    expect(git(workspace, ['rev-parse', 'HEAD'])).toBe(changedHead);
    expect(fs.readFileSync(path.join(project, 'Submission.lean'), 'utf8')).toContain('by exact True.intro');
    expect(host.verify).toHaveBeenCalledOnce();
    expect(host.officialGate).not.toHaveBeenCalled();
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
  // Receipt replay and concurrency fixtures prepare helpers under ordinary dependency waiting.
  const waitingPlanTasks = () => planTasks().map(task => task.kind === 'goal' ? { ...task, conditional: false } : task);
  const writePlan = (worktree: string, tasks: readonly CooperativeTask[], groups?: readonly RouteGroup[]) =>
    fs.writeFileSync(path.join(worktree, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify({ tasks, groups }) + '\n```\n');

  it('rejects forward original-goal dependencies and accepts a shared helper before both goals', () => {
    const tasks = planTasks();
    tasks[2] = { ...tasks[2], dependsOn: ['second'] };
    tasks[3] = { ...tasks[3], dependsOn: [] };
    expect(() => parseCooperationPlan(problem, { tasks })).toThrow('math_plan_forward_goal_dependency: first precedes second');
    tasks[2] = { ...tasks[2], dependsOn: ['a'] };
    tasks[3] = { ...tasks[3], dependsOn: ['a'] };
    expect(() => parseCooperationPlan(problem, { tasks })).not.toThrow();
  });

  it.each(['lemma', 'research', 'sketch'])('rejects a copied prompt placeholder before assigning %s proof work', kind => {
    const tasks = planTasks();
    expect(() => parseCooperationPlan(problem, { tasks: [
      { ...tasks[0], kind, type: ' FULL_CLOSED_LEAN_TYPE ' }, ...tasks.slice(1),
    ] })).toThrow('math_plan_placeholder_helper_type');
    expect(host.createSession).not.toHaveBeenCalled();
  });

  it.each(['research', 'sketch'])('treats typed %s tasks as lemma work while keeping advisory tasks read-only', kind => {
    const tasks = planTasks();
    const parsed = parseCooperationPlan(problem, { tasks: [
      { ...tasks[0], kind }, ...tasks.slice(1),
      { id: 'advice', kind, objective: 'Explore possible methods' },
    ] });
    expect(parsed.tasks[0]).toMatchObject({ kind: 'lemma', theoremName: 'Submission.a', type: 'True', proofPath: 'Submission.lean' });
    expect(parsed.tasks.at(-1)).toEqual({ id: 'advice', kind, objective: 'Explore possible methods', dependsOn: [], revision: 0 });
    expect(() => parseCooperationPlan(problem, { tasks: [{ ...tasks[0], kind, type: 123 }, ...tasks.slice(1)] })).not.toThrow(TypeError);
  });
  const assignmentFrom = (message: string) => JSON.parse(message.match(/Cooperative assignment:\n([^\n]+)/u)![1]) as CooperativeAction;
  function configureCooperation(run?: (action: CooperativeAction, options: MathAgentOptions, message: string) => Promise<string>,
    plan: () => CooperativeTask[] = planTasks) {
    const threadCalls = new Map<string, number>();
    host.verify.mockImplementation(async (request, options) => {
      const source = fs.readFileSync(path.join(request.projectRoot, 'Submission.lean'), 'utf8');
      const wrongType = request.items.some(item =>
        (options.expectedDeclarationType || options.expectedDeclarationTypes?.[item.theoremName]) &&
        source.includes(`${item.theoremName.split('.').at(-1)} : False`));
      const checked = verified(request);
      return !source.includes('sorry') && !wrongType ? checked
        : failed(checked, { stdoutPreview: 'Submission.lean:3:1: error: task type mismatch or unfinished proof\n⊢ True' });
    });
    host.createSession.mockImplementation(async (options: MathAgentOptions) => {
      const threadId = options.threadId || `thread-${options.environment!.DEEPSCIENTIST_MATH_WORKER_ID}`;
      if (!options.threadId) threadCalls.set(threadId, 0);
      return {
        threadId,
        close: vi.fn(), interrupt: vi.fn(), run: async (message: string) => {
          const calls = (threadCalls.get(threadId) ?? 0) + 1;
          threadCalls.set(threadId, calls);
          options.onUsage({ inputTokens: calls * 1000, totalTokens: calls * 1200 });
          const action = assignmentFrom(message);
          if (run) return run(action, options, message);
          if (action.kind === 'lead') writePlan(options.workspace, plan());
          else finishAssignment(action, options);
          return 'completed';
        },
      };
    });
  }

  it.each(['adopted', 'rejected', 'deferred'] as const)('consumes a research handoff through a durable %s Lead decision', async status => {
    const question: CooperativeTask = { id: 'question', kind: 'research', objective: 'Find a concrete bridge', dependsOn: [], revision: 0 };
    const proposal: CooperativeTask = { ...planTasks()[0], id: 'bridge', theoremName: 'Submission.bridge', objective: 'Bridge for the first original goal' };
    const initial = [question, ...planTasks().slice(2).map(task => ({ ...task, status: 'paused' as const,
      dependsOn: task.id === 'first' ? ['question'] : task.dependsOn }))];
    let plans = 0;
    configureCooperation(async (action, options, message) => {
      if (action.kind === 'lead') {
        if (++plans === 1) { writePlan(options.workspace, initial); return 'completed'; }
        const handoff = pendingResearchHandoffs(cooperationState())[0];
        expect(action.handoffIds).toEqual([handoff.id]);
        expect(message).toContain('Pending research proposals requiring a Lead decision');
        expect(message).toContain(handoff.id);
        expect(cooperationState().tasks.find((item: any) => item.task.id === 'first').attempts).toBe(0);
        expect(host.officialGate).not.toHaveBeenCalled();
        const tasks = [question, ...(status === 'adopted' ? [proposal] : []), ...initial.slice(1).map(task => ({ ...task,
          status: 'active', dependsOn: task.id === 'first' && status === 'adopted' ? ['bridge'] : task.dependsOn }))];
        fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), JSON.stringify({ tasks,
          ...(status === 'adopted' ? {} : { handoffDecisions: [{ id: handoff.id, status,
            reason: 'The proposed bridge does not discharge the missing quantitative estimate.' }] }) }));
      } else if (action.kind === 'task' && action.task.id === question.id) {
        fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), JSON.stringify({
          summary: 'This exact bridge has a concrete original-goal consumer.', conclusion: 'supporting', lemmaRequests: [proposal] }));
      } else if (action.kind === 'task' && action.task.kind === 'goal') {
        const file = path.join(options.workspace, 'generated/p/Submission.lean'), name = action.task.theoremName!.split('.').at(-1);
        const proof = name === 'first' ? status === 'adopted' ? 'by exact bridge' : 'by trivial' : 'by exact first';
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace(`${name} : True := by sorry`, `${name} : True := ${proof}`));
      } else finishAssignment(action, options);
      return 'completed';
    });
    const code = await runSolver([...args, '--workers', '2', '--max-turns', '9'], directory);
    expect(code, JSON.parse(fs.readFileSync(output, 'utf8')).reason).toBe(0);
    const state = cooperationState();
    expect(state.researchDecisions).toHaveLength(1);
    expect(state.researchDecisions[0].status).toBe(status);
    expect(state.tasks.find((item: any) => item.task.id === 'bridge')?.status).toBe(status === 'adopted' ? 'integrated' : undefined);
    expect(pendingResearchHandoffs(state)).toEqual([]);
    const restored = readSolverRunState(`${output}.runtime/state.json`);
    const inspection = buildRunInspection(restored);
    const journal = JSON.parse(fs.readFileSync(path.join(restored.worktree, 'COOPERATION.json'), 'utf8'));
    if (status === 'adopted') {
      expect(inspection.continuation.adoptedResearch).toEqual([expect.objectContaining({ sourceTaskId: question.id,
        taskId: proposal.id, recordedProof: 'checked', plannedGoalIds: expect.arrayContaining(['first']),
        proofConsumers: [], referenceCoverage: 'unknown' })]);
      expect(journal.continuation.adoptedResearch).toEqual(inspection.continuation.adoptedResearch);
    } else {
      expect(inspection.continuation.adoptedResearch).toEqual([]);
      expect(journal.continuation.adoptedResearch).toEqual([]);
    }
    expect(host.officialGate).toHaveBeenCalledOnce();
  });

  it('rejects an ignored research handoff before changing the graph, then accepts its corrected decision', async () => {
    const tasks = planTasks().map(task => ({ ...task, status: 'paused' as const }));
    const question: CooperativeTask = { id: 'question', kind: 'research', objective: 'Explore the missing bridge', dependsOn: [], revision: 0 };
    const proposal: CooperativeTask = { ...tasks[0], id: 'bridge', theoremName: 'Submission.bridge', status: 'active' };
    const lead = { id: 'solver', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles } as const;
    const peer = { ...lead, id: 'researcher-1', role: 'researcher' } as const;
    const state = { problem, environmentDigest: 'environment', turns: 0,
      cooperation: { tasks: [...tasks.map(task => ({ task, status: 'pending', attempts: 0 })),
        { task: question, status: 'completed', attempts: 1 }], deliveries: [{
        id: 'proposal', producer: peer.id, taskId: question.id, taskDigest: taskVersion(question), kind: 'research', status: 'advisory',
        summary: 'Exact bridge proposal.', statement: '', premises: [], dependencies: [], remainingObligations: [],
        evidenceRefs: [], createdAt: 1, lemmaRequests: [proposal] }] } } as any;
    const cooperative = new CooperativeResearch({ state, workers: [lead, peer], access: new Map(), signal: new AbortController().signal,
      modules: directSolverModules, save: vi.fn(), emit: vi.fn(), exclusiveCheck: check => check() });
    const action = await cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity });
    if (action?.kind !== 'lead') throw new Error('missing_handoff_decision');
    writePlan(workspace, [...tasks, question]);
    const before = state.cooperation.tasks.map((item: any) => item.task);
    await cooperative.deliver(lead, action, commitSolverSources(problem, workspace));
    expect(state.cooperation.error).toContain('math_handoff_unresolved:');
    expect(state.cooperation.tasks.map((item: any) => item.task)).toEqual(before);
    expect(state.cooperation.researchDecisions).toBeUndefined();
    const corrected = await cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity });
    if (corrected?.kind !== 'lead') throw new Error('missing_corrected_handoff_decision');
    fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), JSON.stringify({ tasks: [...tasks, question],
      handoffDecisions: [{ id: corrected.handoffIds![0], status: 'deferred', reason: 'A new analytic input is required.' }] }));
    await cooperative.deliver(lead, corrected, commitSolverSources(problem, workspace));
    expect(state.cooperation.error).toBeUndefined();
    expect(state.cooperation.researchDecisions[0].status).toBe('deferred');
    expect(host.verify).not.toHaveBeenCalled();
    expect(host.createSession).not.toHaveBeenCalled();
  });

  function handoffQueue(count = 18) {
    const question: CooperativeTask = { id: 'question', kind: 'research', objective: 'Investigate exact bridges', dependsOn: [], revision: 0 };
    const proposals = Array.from({ length: count }, (_, index) => ({ ...planTasks()[0],
      id: `bridge_${index}`, theoremName: `Submission.bridge_${index}` }));
    const tasks = [...planTasks().slice(2).map(task => ({ ...task, dependsOn: [], status: 'paused' as const })), question];
    const plan = parseCooperationPlan(problem, { tasks });
    const lead = { id: 'solver', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles } as const;
    const peer = { ...lead, id: 'researcher-1', role: 'researcher' } as const;
    const state = { problem, environmentDigest: 'environment', turns: 0,
      cooperation: { planVersion: mathDigest(canonicalMathJson({ tasks: plan.tasks, groups: plan.groups })),
        tasks: plan.tasks.map(task => ({ task, status: task.id === question.id ? 'completed' : 'pending', attempts: 0 })),
        groups: plan.groups.map(group => ({ group, turns: 0 })), deliveries: [{
          id: 'proposals', producer: peer.id, taskId: question.id, taskDigest: taskVersion(question), kind: 'research', status: 'advisory',
          summary: 'Exact bridge proposals.', statement: '', premises: [], dependencies: [], remainingObligations: [],
          evidenceRefs: [], createdAt: 1, lemmaRequests: proposals }] } } as any;
    const emit = vi.fn();
    const create = (restored = state) => new CooperativeResearch({ state: restored, workers: [lead, peer], access: new Map(),
      signal: new AbortController().signal, modules: directSolverModules,
      save: vi.fn(), emit, exclusiveCheck: check => check() });
    return { state, question, proposals, lead, peer, emit, create, cooperative: create() };
  }

  it('recovers a failed Lead request when an existing handoff decision adopts the current task revision', async () => {
    const { state, proposals, lead, cooperative } = handoffQueue(1);
    const plan = parseCooperationPlan(problem, { tasks: [
      ...state.cooperation.tasks.map((node: TaskRecord) => node.task), { ...proposals[0], revision: 1 },
    ] });
    state.cooperation.tasks = plan.tasks.map(task => ({ task,
      status: task.id === 'question' ? 'completed' : 'pending', attempts: 0 }));
    state.cooperation.groups = plan.groups.map(group => ({ group, turns: 0 }));
    const planVersion = state.cooperation.planVersion = mathDigest(canonicalMathJson({ tasks: plan.tasks, groups: plan.groups }));
    const [handoff] = pendingResearchHandoffs(state.cooperation);
    const bridge = plan.tasks.find(task => task.id === proposals[0].id)!;
    const previous = { id: handoff.id, deliveryId: handoff.deliveryId, status: 'adopted',
      taskId: bridge.id, taskDigest: taskVersion({ ...bridge, revision: 0 }) };
    state.cooperation.researchDecisions = [previous];
    expect(pendingResearchHandoffs(state.cooperation)).toHaveLength(1);
    const action = await cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity });
    if (action?.kind !== 'lead') throw new Error('missing_revised_handoff_decision');
    expect(action.handoffIds).toEqual([handoff.id]);
    writePlan(workspace, plan.tasks, plan.groups);

    const saved = await cooperative.deliver(lead, action, commitSolverSources(problem, workspace), true, 'request-failure');

    expect(saved).toEqual({ checkWhole: false, savedPlan: true });
    expect(state.cooperation.planVersion).toBe(planVersion);
    expect(state.cooperation.researchDecisions).toEqual([{ ...previous, taskDigest: taskVersion(bridge), contextDigest: handoff.contextDigest }]);
    expect(pendingResearchHandoffs(state.cooperation)).toEqual([]);
    const unchanged = await cooperative.deliver(lead, { ...action, handoffIds: [] },
      commitSolverSources(problem, workspace), true, 'request-failure');
    expect(unchanged).toEqual({ checkWhole: false });
    expect(state.cooperation.researchDecisions).toHaveLength(1);
    expect(host.createSession).not.toHaveBeenCalled();
    expect(host.verify).not.toHaveBeenCalled();
  });

  it('drains every queued handoff across batches and JSON restore despite an unchanged planning digest', async () => {
    const fixture = handoffQueue();
    let state = fixture.state, cooperative = fixture.cooperative;
    const batches: number[] = [], seen = new Set<string>();
    while (pendingResearchHandoffs(state.cooperation).length) {
      const action = await cooperative.next(fixture.lead, { maxTurns: Infinity, remainingMs: Infinity });
      if (action?.kind !== 'lead') throw new Error('missing_next_handoff_batch');
      batches.push(action.handoffIds!.length);
      expect(action.handoffIds!.every(id => !seen.has(id))).toBe(true);
      action.handoffIds!.forEach(id => seen.add(id));
      fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), JSON.stringify({ tasks: state.cooperation.tasks.map((item: any) => item.task),
        handoffDecisions: action.handoffIds!.map(id => ({ id, status: 'deferred', reason: 'Need a quantified bridge estimate.' })) }));
      await cooperative.deliver(fixture.lead, action, commitSolverSources(problem, workspace));
      expect(state.cooperation.error).toBeUndefined();
      if (batches.length === 1) { state = JSON.parse(JSON.stringify(state)); cooperative = fixture.create(state); }
    }
    expect(batches).toEqual([8, 8, 2]);
    expect(state.cooperation.researchDecisions).toHaveLength(18);
    expect(host.createSession).not.toHaveBeenCalled();
    expect(host.verify).not.toHaveBeenCalled();
  });

  it('does not let an unresolved backlog bypass the repeated invalid-plan guard', async () => {
    const { state, lead, emit, create, cooperative } = handoffQueue();
    for (let attempt = 0; attempt < 2; attempt++) {
      const action = await cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity });
      if (action?.kind !== 'lead') throw new Error('missing_handoff_retry');
      writePlan(workspace, state.cooperation.tasks.map((item: any) => item.task));
      await cooperative.deliver(lead, action, commitSolverSources(problem, workspace));
    }
    expect(state.cooperation.planRejection.stalled).toBe(true);
    expect(await cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity })).toBeUndefined();
    expect(emit).toHaveBeenCalledWith('plan_stalled', expect.anything());
    expect(pendingResearchHandoffs(state.cooperation)).toHaveLength(18);
    const restored = JSON.parse(JSON.stringify(state)), resumed = create(restored);
    await resumed.restore();
    expect(await resumed.next(lead, { maxTurns: Infinity, remainingMs: Infinity })).toBeUndefined();
    expect(restored.cooperation.planRejection.stalled).toBe(true);
    expect(pendingResearchHandoffs(restored.cooperation)).toHaveLength(18);
  });

  it.each(['removed', 'revised', 'group-revised', 'prerequisite-revised', 'late-arrival'] as const)(
    'rejects a model plan before mutation when it would lose a queued proposal source: %s', async change => {
      const { state, lead, question, create, cooperative } = handoffQueue(change === 'late-arrival' ? 8 : 9);
      if (change === 'prerequisite-revised') {
        const prerequisite = planTasks()[0];
        state.cooperation.tasks.push({ task: prerequisite, status: 'pending', attempts: 0 });
        const source = state.cooperation.tasks.find((item: any) => item.task.id === question.id);
        source.task = { ...source.task, dependsOn: [prerequisite.id] };
        state.cooperation.deliveries[0].taskDigest = taskVersion(source.task);
        state.cooperation.deliveries[0].dependencies = [{ taskId: prerequisite.id, taskDigest: taskVersion(prerequisite) }];
      }
      const action = await cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity });
      if (action?.kind !== 'lead') throw new Error('missing_handoff_batch');
      if (change === 'late-arrival') state.cooperation.deliveries.push({ ...state.cooperation.deliveries[0], id: 'late',
        lemmaRequests: [{ ...planTasks()[0], id: 'late_bridge', theoremName: 'Submission.late_bridge' }] });
      const before = structuredClone(state.cooperation.tasks);
      const tasks = before.map((item: any) => item.task).filter((task: CooperativeTask) =>
        !['removed', 'late-arrival'].includes(change) || task.id !== question.id).map((task: CooperativeTask) =>
        change === 'revised' && task.id === question.id || change === 'prerequisite-revised' && task.id === 'a'
          ? { ...task, revision: 1 } : task);
      fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), JSON.stringify({ tasks,
        ...(change === 'group-revised' ? { groups: [{ ...state.cooperation.groups[0].group, revision: 1 }] } : {}),
        handoffDecisions: action.handoffIds!.map(id => ({ id, status: 'deferred', reason: 'Need new evidence.' })) }));
      await cooperative.deliver(lead, action, commitSolverSources(problem, workspace));
      expect(state.cooperation.error).toContain('math_handoff_backlog_source_required:question');
      expect(state.cooperation.tasks.map(({ task, status, attempts }: TaskRecord) => ({ task, status, attempts })))
        .toEqual(before.map(({ task, status, attempts }: TaskRecord) => ({ task, status, attempts })));
      expect(state.cooperation.researchDecisions).toBeUndefined();
      expect(state.cooperation.deliveries.every((item: any) => item.status === 'advisory')).toBe(true);
      if (change === 'removed') {
        const restored = JSON.parse(JSON.stringify(state));
        await create(restored).restore();
        expect(restored.cooperation.tasks.map((item: TaskRecord) => item.task)).toEqual(before.map((item: TaskRecord) => item.task));
        expect(pendingResearchHandoffs(restored.cooperation)).toHaveLength(9);
      }
    });

  it('replans a ready original goal after its pinned engineer exits instead of waiting for an impossible assignment', async () => {
    const tasks = planTasks().slice(2).map(task => ({ ...task, dependsOn: task.id === 'first' ? [] : ['first'] }));
    const plan = parseCooperationPlan(problem, { tasks, groups: [{ id: 'main', objective: 'Original goals', engineerId: 'engineer' }] });
    const lead = { id: 'solver', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles } as const;
    const peer = { ...lead, id: 'researcher-1', role: 'researcher' } as const;
    const engineer = { ...lead, id: 'engineer', role: 'engineer' } as const;
    const state = { problem, environmentDigest: 'environment', turns: 0,
      cooperation: { tasks: plan.tasks.map(task => ({ task, status: 'pending', attempts: 0 })),
        groups: plan.groups.map(group => ({ group, turns: 0 })) } } as any;
    const cooperative = new CooperativeResearch({ state, workers: [lead, peer, engineer], access: new Map(), signal: new AbortController().signal,
      modules: directSolverModules, save: vi.fn(), emit: vi.fn(), exclusiveCheck: check => check() });
    cooperative.stopped(engineer, 'math_model_request_failed');
    const action = await cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity });
    expect(action?.kind).toBe('lead');
    if (action?.kind !== 'lead') throw new Error('missing_owner_replan');
    writePlan(workspace, tasks);
    await cooperative.deliver(lead, action, commitSolverSources(problem, workspace));
    expect(await cooperative.next(peer, { maxTurns: Infinity, remainingMs: Infinity })).toMatchObject({ kind: 'task', task: { id: 'first' } });
    expect(host.createSession).not.toHaveBeenCalled();
  });

  it.each([false, true])('allocates exploration from synchronous reservations with a cooling peer: %s', async coolingPeer => {
    await withSolverWorktree(workspace, problem.baseCommit, async researcherRoot => {
      await withSolverWorktree(workspace, problem.baseCommit, async engineerRoot => {
        const tasks: CooperativeTask[] = [...planTasks().slice(0, 2),
          { id: 'alternative', kind: 'research', objective: 'Investigate a distinct route', dependsOn: [], revision: 0 },
          ...planTasks().slice(2).map(task => ({ ...task, conditional: false }))];
        const plan = parseCooperationPlan(problem, { tasks });
        const lead = { id: 'solver', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles } as const;
        const researcher = { ...lead, id: 'researcher-1', role: 'researcher', worktree: researcherRoot } as const;
        const engineer = { ...lead, id: 'engineer', role: 'engineer', worktree: engineerRoot } as const;
        const workers = [lead, researcher, engineer, ...(coolingPeer ? [{ ...researcher, id: 'cooling-peer' }] : [])];
        const state: any = { problem, environmentDigest: 'environment', turns: 0,
          workers: workers.map(worker => ({ ...worker, turns: 0, phase: 'running',
            ...(worker.id === 'cooling-peer' ? { recovery: { phase: 'cooling-down', reason: 'math_model_request_failed',
              cycles: 1, startedAt: 1, nextRetryAt: Date.now() + 60_000, waitedMs: 0 } } : {}) })),
          cooperation: { tasks: plan.tasks.map(task => ({ task, status: 'pending', attempts: 0 })),
            groups: plan.groups.map(group => ({ group, turns: 0 })) } };
        const cooperative = new CooperativeResearch({ state, workers, access: new Map(), signal: new AbortController().signal,
          modules: directSolverModules, save: vi.fn(), emit: vi.fn(), exclusiveCheck: check => check() });
        try {
          expect(await cooperative.next(researcher, { maxTurns: Infinity, remainingMs: Infinity }))
            .toMatchObject({ kind: 'task', task: { id: 'a' } });
          expect(await cooperative.next(engineer, { maxTurns: Infinity, remainingMs: Infinity }))
            .toMatchObject({ kind: 'task', task: { id: 'alternative' } });
          expect(state.cooperation.tasks.find((node: TaskRecord) => node.task.id === 'b').status).toBe('pending');
          expect(host.createSession).not.toHaveBeenCalled();
        } finally { await cooperative.stop(); }
      });
    });
  });

  it('starts peer work after a completed invalid initial plan without consuming an unlimited planning loop', async () => {
    let leadTurns = 0;
    const peers = new Set<string>();
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') {
        leadTurns++;
        writePlan(options.workspace, planTasks().map(task => task.id === 'a' ? { ...task, theoremName: 'Submission.bad;name' } : task));
      } else if (action.kind === 'task') {
        peers.add(action.assignment.workerId);
        if (action.task.kind === 'goal') {
          const file = path.join(options.workspace, 'generated/p/Submission.lean');
          const name = action.task.theoremName!.split('.').at(-1);
          fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace(`${name} : True := by sorry`, `${name} : True := by trivial`));
        } else fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), 'Independent route findings retained.');
      } else finishAssignment(action, options);
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '0'], directory)).toBe(0);
    const state = cooperationState();
    expect(leadTurns).toBe(1);
    expect(peers.size).toBeGreaterThanOrEqual(2);
    expect(state.initialPlanFallback.reason).toContain('math_plan_invalid_proof_target');
    expect(state.tasks.filter((node: any) => node.task.kind === 'goal').every((node: any) => node.status === 'integrated')).toBe(true);
    expect(readCooperationPlan(problem, `${output}.runtime/worktree`).tasks).toEqual(state.tasks.map((node: any) => node.task));
    expect(host.officialGate).toHaveBeenCalledOnce();
  });

  it.each(['environment', 'peer-evidence'])('parks identical rejected plans across notes commits and resume, and retries after new %s', async input => {
    const plan = parseCooperationPlan(problem, { tasks: planTasks().map(task => ({ ...task, status: 'paused' })) });
    const lead = { id: 'solver', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles } as const;
    const peer = { ...lead, id: 'researcher-1', role: 'researcher' } as const;
    const state: any = { problem, runId: 'rejected-plan', turns: 0, phase: 'running', environmentDigest: 'fixture',
      cooperation: { error: 'repair_requested', canonicalCommit: problem.baseCommit,
        planVersion: mathDigest(canonicalMathJson(plan)), tasks: plan.tasks.map(task => ({ task, status: 'pending', attempts: 0 })),
        groups: plan.groups.map(group => ({ group, turns: 0 })) } };
    const progress = { id: 'known-progress', taskId: plan.tasks[0].id, taskDigest: taskVersion(plan.tasks[0]),
      kind: 'progress', status: 'advisory', summary: 'Known obstacle.', evidenceRefs: [], dependencies: [], remainingObligations: [] };
    state.cooperation.deliveries = [progress];
    const events: string[] = [];
    const create = () => new CooperativeResearch({ state, workers: [lead, peer], access: new Map(),
      signal: new AbortController().signal, save: () => {}, emit: event => events.push(event), modules: directSolverModules,
      exclusiveCheck: async check => check() });
    const cooperative = create(), budget = { maxTurns: Infinity, remainingMs: Infinity };
    const invalid = plan.tasks.map(task => task.id === 'first' ? { ...task, theoremName: 'Submission.changed' } : task);
    const commits: string[] = [];
    for (let attempt = 0; attempt < 2; attempt++) {
      const action = await cooperative.next(lead, budget);
      expect(action?.kind).toBe('lead');
      if (action?.kind !== 'lead') throw new Error('missing_repair_assignment');
      writePlan(workspace, invalid);
      fs.appendFileSync(path.join(workspace, 'RESEARCH.md'), `\nRepeated blocker explanation ${attempt}.\n`);
      const commit = commitSolverSources(problem, workspace); commits.push(commit);
      await cooperative.deliver(lead, action, commit);
    }
    expect(commits[0]).not.toBe(commits[1]);
    expect(state.cooperation.planRejection).toMatchObject({ stalled: true, error: 'math_plan_changed_original_target' });
    expect(await cooperative.next(lead, budget)).toBeUndefined();
    expect(events).toContain('plan_stalled');
    await cooperative.stop();
    const resumed = create();
    await resumed.restore();
    expect(await resumed.next(lead, budget)).toBeUndefined();
    state.cooperation.deliveries.push({ ...progress, id: 'heartbeat-new-id', createdAt: 42 });
    expect(await resumed.next(lead, budget)).toBeUndefined();
    if (input === 'environment') state.environmentDigest = 'repaired-environment';
    else state.cooperation.deliveries = [{ id: 'new-progress', taskId: plan.tasks[0].id,
      taskDigest: taskVersion(plan.tasks[0]), kind: 'progress', status: 'advisory', summary: 'New concrete library evidence.',
      evidenceRefs: ['Library.connection'], dependencies: [], remainingObligations: [] }];
    const reopened = await resumed.next(lead, budget);
    expect(reopened?.kind).toBe('lead');
    if (reopened?.kind !== 'lead') throw new Error('missing_reopened_assignment');
    writePlan(workspace, plan.tasks);
    await resumed.deliver(lead, reopened, commitSolverSources(problem, workspace));
    expect(state.cooperation.planRejection).toBeUndefined();
    expect(state.cooperation.error).toBeUndefined();
    expect(host.createSession).not.toHaveBeenCalled();
    expect(host.officialGate).not.toHaveBeenCalled();
    await resumed.stop();
  });

  it('retries an unfinished parked-frontier assessment after restore and remembers a completed assessment', async () => {
    const plan = parseCooperationPlan(problem, { tasks: planTasks() });
    writePlan(workspace, plan.tasks);
    const canonicalCommit = commitSolverSources(problem, workspace);
    let state: any = { problem, runId: 'frontier-restore', turns: 0, phase: 'running', environmentDigest: 'fixture',
      cooperation: { canonicalCommit, tasks: plan.tasks.map(task => ({ task, attempts: task.kind === 'lemma' ? 1 : 0,
        status: task.kind === 'lemma' ? 'blocked' : 'pending' })), groups: plan.groups.map(group => ({ group, turns: 0 })), blockers: [] } };
    const core = state.cooperation.tasks[0], blockers = state.cooperation.blockers;
    const proposal = { mechanism: 'A checked analytic input is missing.', scope: 'The core inference.',
      reopenOn: [{ kind: 'contract-changed' as const }] };
    for (let i = 0; i < 2; i++) recordRouteBlockers(blockers, [proposal], core.task, state.cooperation.tasks,
      state.environmentDigest, problem.receiptDigest);
    refreshRouteBlockers(blockers, state.cooperation.tasks, state.environmentDigest, problem.receiptDigest);
    const lead = { id: 'solver', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles } as const;
    const peer = { ...lead, id: 'researcher-1', role: 'researcher' } as const;
    const create = () => new CooperativeResearch({ state, workers: [lead, peer], access: new Map(),
      signal: new AbortController().signal, save: () => {}, emit: () => {}, modules: directSolverModules,
      exclusiveCheck: async check => check() });
    const budget = { maxTurns: Infinity, remainingMs: Infinity };
    const initial = create(); await initial.restore();
    expect(await initial.next(lead, budget)).toMatchObject({ kind: 'lead' });
    expect(state.cooperation.lastLeadInputDigest).toBeUndefined();
    await initial.stop(); state = JSON.parse(JSON.stringify(state));
    const resumed = create(); await resumed.restore();
    const action = await resumed.next(lead, budget);
    expect(action).toMatchObject({ kind: 'lead' });
    if (action?.kind !== 'lead') throw new Error('missing_resumed_frontier_assessment');
    writePlan(workspace, plan.tasks);
    await resumed.deliver(lead, action, commitSolverSources(problem, workspace));
    expect(state.cooperation.lastLeadInputDigest).toBe(action.planningInputDigest);
    expect(state.cooperation.tasks[0].routeParking).toHaveLength(1);
    await resumed.stop(); state = JSON.parse(JSON.stringify(state));
    const completed = create(); await completed.restore();
    const recovery = await completed.next(lead, budget);
    expect(recovery).toMatchObject({ kind: 'lead', recovery: { taskIds: ['b'] } });
    if (recovery?.kind !== 'lead') throw new Error('missing_unparked_frontier_recovery');
    fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify({
      tasks: plan.tasks, groups: plan.groups,
      recovery: { status: 'awaiting-input', reason: 'The unparked second construction needs a new mathematical premise.' },
    }) + '\n```');
    await completed.deliver(lead, recovery, commitSolverSources(problem, workspace));
    expect(await completed.next(lead, budget)).toBeUndefined();
    expect(state.cooperation.tasks[0].routeParking).toHaveLength(1);
    await completed.stop();
    state = JSON.parse(JSON.stringify(state));
    const settled = create(); await settled.restore();
    expect(await settled.next(lead, budget)).toBeUndefined();
    expect(state.cooperation.frontierRecoveries).toEqual([expect.objectContaining({ status: 'awaiting-input' })]);
    await settled.stop();
    expect(host.createSession).not.toHaveBeenCalled();
    expect(host.officialGate).not.toHaveBeenCalled();
  });

  it.each(['official_verified', 'failed'])('retains independent acceptance after integrating an original definition goal (%s)', async officialStatus => {
    const { task } = configureDefinitionGoal();
    const tasks: CooperativeTask[] = [task, ...['first', 'second'].map(name => ({ id: name, kind: 'goal' as const,
      objective: `Prove ${name} after filling the constant`, theoremName: `Submission.${name}`, proofPath: 'Submission.lean',
      dependsOn: ['constant'], revision: 0 }))];
    host.officialGate.mockResolvedValue({ comparison: { status: officialStatus } });
    let reviews = 0;
    configureCooperation(async (action, options) => {
      const file = path.join(options.workspace, 'generated/p/Submission.lean');
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'review') {
        reviews++;
        expect(fs.readFileSync(file, 'utf8')).not.toContain('sorry');
        expect(fs.readFileSync(file, 'utf8')).toContain('noncomputable def C : Nat := 7');
        expect(host.officialGate).not.toHaveBeenCalled();
        finishAssignment(action, options);
      } else if (action.kind === 'task') {
        expect(host.officialGate).not.toHaveBeenCalled();
        const source = fs.readFileSync(file, 'utf8');
        if (action.task.id === 'constant') {
          expect(options.instructions).toContain('An original goal may be a def');
          expect(source).toContain('theorem first : True := by sorry');
          expect(source).toContain('theorem second : True := by sorry');
          fs.writeFileSync(file, source.replace('C : Nat := by sorry', 'C : Nat := 7'));
        } else {
          expect(source).toContain('noncomputable def C : Nat := 7');
          fs.writeFileSync(file, source.replace(`${action.task.id} : True := by sorry`, `${action.task.id} : True := by trivial`));
        }
      } else throw new Error('unexpected_definition_goal_action');
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '3', '--max-turns', '7'], directory)).toBe(officialStatus === 'official_verified' ? 0 : 2);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.cooperation.tasks.every((node: any) => node.status === 'integrated')).toBe(true);
    expect(state.cooperation.review.status).toBe('accepted');
    expect(reviews).toBe(1);
    expect(host.officialGate).toHaveBeenCalledOnce();
    expect(host.verify.mock.calls.filter(([request]) => request.items.length === problem.targets.length).length).toBeGreaterThanOrEqual(2);
    expect(JSON.parse(fs.readFileSync(output, 'utf8')).status).toBe(officialStatus === 'official_verified' ? 'evaluated_passed' : 'evaluated_failed');
  });

  it('counts cooperative planning toward the token allowance and leaves unstarted proof work resumable', async () => {
    configureCooperation();
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '0', '--max-total-tokens', '1200'], directory)).toBe(4);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state).toMatchObject({ turns: 1, dispatchCounts: { planning: 1 },
      tokenBudget: { status: 'exhausted', reportedTotalTokens: 1200, usageComplete: true } });
    expect(state.cooperation.tasks.map((node: any) => node.status)).toEqual(['pending', 'pending', 'pending', 'pending']);
    expect(host.officialGate).not.toHaveBeenCalled();
  });

  it('continues through proof checks and independent acceptance after a bounded initial planning checkpoint', async () => {
    configureCooperation();
    let leadTurns = 0, proofTurns = 0;
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({
      threadId: options.threadId ?? `bounded-${options.environment!.DEEPSCIENTIST_MATH_WORKER_ID}`,
      usageSource: 'upstream-requests' as const, lastError: 'HTTP 403 Forbidden',
      lastFailureDiagnostic: { code: 'unauthorized' as const }, close: vi.fn(), interrupt: vi.fn(),
      run: async (message: string) => {
        const action = assignmentFrom(message);
        const admission = options.requestGate!(); expect(admission.allowed).toBe(true);
        const totalTokens = action.kind === 'lead' ? 300 : 20;
        if (admission.allowed) admission.settle({ usage: { totalTokens, inputTokens: totalTokens - 5, outputTokens: 5 }, complete: true });
        if (action.kind === 'lead') {
          leadTurns++;
          expect(options.requestGate!()).toEqual({ allowed: false, reason: 'math_initial_planning_limit' });
          return 'failed';
        }
        if (action.kind === 'task' && action.task.kind === 'goal') {
          proofTurns++;
          expect(host.officialGate).not.toHaveBeenCalled();
          const file = path.join(options.workspace, problem.projectRelative, action.task.proofPath!);
          const name = action.task.theoremName!.split('.').at(-1);
          fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace(`${name} : True := by sorry`, `${name} : True := by trivial`));
        } else finishAssignment(action, options);
        return 'completed';
      },
    }));
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '8', '--max-total-tokens', '1000'], directory)).toBe(0);
    const state = readSolverRunState(`${output}.runtime/state.json`);
    expect(leadTurns).toBe(1); expect(proofTurns).toBe(2);
    expect(state.cooperation!.initialPlanFallback).toBeDefined();
    expect(state.tokenBudget).toMatchObject({ status: 'available', usageComplete: true });
    expect(state.workers!.every(worker => !worker.lastFailure && !worker.error)).toBe(true);
    expect(state.cooperation!.tasks.every(node => node.status === 'integrated')).toBe(true);
    expect(state.check?.passed).toBe(true);
    expect(JSON.parse(fs.readFileSync(output, 'utf8')).status).toBe('evaluated_passed');
    expect(host.officialGate).toHaveBeenCalledOnce();
  });

  it('keeps cooperative in-flight helper checks after reaching the shared token allowance', async () => {
    let started = 0;
    const bothStarted = deferred();
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') {
        // Both proof slots must reach the helper barrier before this fixture exhausts its allowance.
        writePlan(options.workspace, planTasks().map(task => task.kind === 'goal' ? { ...task, conditional: false } : task));
        return 'completed';
      }
      if (action.kind === 'task' && action.task.kind === 'lemma') {
        if (++started === 2) bothStarted.resolve(); await bothStarted.promise;
      }
      finishAssignment(action, options); return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '0', '--max-total-tokens', '3600'], directory)).toBe(4);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state).toMatchObject({ turns: 3, dispatchCounts: { planning: 1, proof: 2 },
      tokenBudget: { status: 'exhausted', reportedTotalTokens: 3600, usageComplete: true } });
    expect(state.cooperation.tasks.map((node: any) => node.status)).toEqual(['integrated', 'integrated', 'pending', 'pending']);
    expect(host.officialGate).not.toHaveBeenCalled();
  });

  it('commits saved cooperative proofs on the host and persists worker activity', async () => {
    configureCooperation(async (action, options, message) => {
      if (action.kind === 'task') {
        expect(options.instructions).toContain('The host freezes the saved sources');
        expect(message).not.toContain('commit allowed sources and notes');
        expect(options.instructions).not.toContain('Report checker startup errors and return');
        expect(options.instructions).toContain('then retry the saved-file check');
        options.onActivity!({ event: 'lean_lock_waiting', itemType: 'commandExecution' });
      }
      finishAssignment(action, options);
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '6'], directory)).toBe(0);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.cooperation.tasks.every((node: any) => node.status === 'integrated')).toBe(true);
    expect(state.workers.find((worker: any) => worker.id === 'researcher-1').lastActivity)
      .toMatchObject({ event: 'lean_lock_waiting', at: expect.any(Number) });
    expect(host.officialGate).toHaveBeenCalledOnce();
  }, 20_000);

  it.each([false, true])('preserves cooperative saved work after a disconnected request, target saved=%s', async complete => {
    let attempts = 0, seedCommit = '';
    configureCooperation(async (action, options, message) => {
      if (action.kind === 'task' && action.task.id === 'a') {
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        if (++attempts === 1) {
          seedCommit = action.assignment.seedCommit;
          fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('theorem first', 'lemma saved_support : True := by trivial\ntheorem first'));
          fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), 'Saved partial proof; finish a next.');
          if (complete) finishAssignment(action, options);
          return 'failed';
        }
        expect(action.assignment.seedCommit).toBe(seedCommit);
        expect(fs.readFileSync(file, 'utf8')).toContain('lemma saved_support : True := by trivial');
        expect(fs.readFileSync(path.join(options.workspace, 'RESEARCH.md'), 'utf8')).toContain('Saved partial proof');
        expect(message).toContain('math_task_missing_declaration');
      }
      finishAssignment(action, options); return 'completed';
    });
    const create = host.createSession.getMockImplementation()!;
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ ...await create(options),
      lastError: 'stream disconnected before completion: error sending request' }));
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '8'], directory)).toBe(0);
    expect(attempts).toBe(complete ? 1 : 2);
    expect(host.delay).toHaveBeenCalledTimes(complete ? 0 : 1);
    expect(cooperationState().tasks.every((node: any) => node.status === 'integrated')).toBe(true);
    expect(cooperationState().deliveries.some((record: any) => record.taskId === 'a' && record.kind === 'failure')).toBe(false);
    expect(host.officialGate).toHaveBeenCalledOnce();
  });

  it.each([2, 4])('starts original goal work after an empty Lead checkpoint with %s workers', async count => {
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') {
        expect(options.turnTimeoutMs).toBe(180_000);
        return 'checkpoint';
      }
      if (action.kind === 'task' && action.task.kind === 'research') {
        fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), 'Both targets have direct proofs; this finding is advisory.');
      } else if (action.kind === 'task' && action.task.kind === 'goal') {
        expect(action.task.dependsOn).toEqual([]);
        expect(options.turnTimeoutMs).toBe(180_000);
        const name = action.task.theoremName!.split('.').at(-1);
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace(`theorem ${name} : True := by sorry`, `theorem ${name} : True := by trivial`));
      } else finishAssignment(action, options);
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', String(count), '--max-turns', '6', '--max-turn-seconds', '180'], directory)).toBe(0);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.cooperation.initialPlanFallback).toMatchObject({ reason: expect.any(String) });
    expect(state.cooperation.tasks.filter((node: any) => node.task.kind === 'goal').map((node: any) => node.task.theoremName))
      .toEqual(problem.targets.map(target => target.theoremName));
    expect(state.workers.find((worker: any) => worker.role === 'lead').turns).toBeGreaterThan(0);
    expect(state.workers.some((worker: any) => worker.role !== 'lead' && worker.turns > 0)).toBe(true);
    expect(state.cooperation.tasks.filter((node: any) => node.task.kind === 'goal')
      .every((node: any) => node.status === 'integrated' && node.attempts > 0)).toBe(true);
    expect(state.usage).toMatchObject({ inputTokens: state.turns * 1000, totalTokens: state.turns * 1200 });
  });

  it.each([180, 0])('keeps a valid task graph at a Lead checkpoint and respects turn limit %s', async seconds => {
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') expect(options.turnTimeoutMs).toBe(seconds === 0 ? undefined : seconds * 1000);
      finishAssignment(action, options);
      return action.kind === 'lead' ? 'checkpoint' : 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '6', '--max-turn-seconds', String(seconds)], directory)).toBe(0);
    expect(cooperationState().initialPlanFallback).toBeUndefined();
    expect(cooperationState().tasks.map((node: any) => node.task.id)).toEqual(planTasks().map(task => task.id));
  });

  it.each([
    { status: 'checkpoint', savedFinding: false },
    { status: 'interrupted', savedFinding: false },
    { status: 'checkpoint', savedFinding: true },
  ])('resumes an advisory $status without unlocking consumers (saved finding: $savedFinding)', async ({ status, savedFinding }) => {
    const tasks: CooperativeTask[] = [
      { id: 'question', kind: 'research', objective: 'Find a proof route', dependsOn: [], revision: 0 },
      ...planTasks().slice(2).map(task => ({ ...task, dependsOn: task.id === 'first' ? ['question'] : ['first'] })),
    ];
    let attempts = 0, seed = '', researchWorkspace = '';
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') {
        writePlan(options.workspace, tasks);
        for (const worker of JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8')).workers.slice(1)) {
          writePlan(worker.worktree, tasks);
          commitSolverSources(problem, worker.worktree);
        }
      } else if (action.kind === 'task' && action.task.id === 'question') {
        if (++attempts === 1) {
          seed = action.assignment.seedCommit; researchWorkspace = options.workspace;
          if (savedFinding) fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), 'The current route uses True.intro; both targets remain to be proved.');
          return status;
        }
        expect(action.assignment.seedCommit).toBe(seed);
        expect(options.workspace).toBe(researchWorkspace);
        expect(cooperationState().deliveries ?? []).toEqual([]);
        expect(cooperationState().tasks.slice(1).every((node: any) => node.attempts === 0)).toBe(true);
        if (savedFinding) expect(fs.readFileSync(path.join(options.workspace, 'RESEARCH.md'), 'utf8')).toContain('The current route');
        else fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), 'The current route uses True.intro; both targets remain to be proved.');
      } else if (action.kind === 'task') {
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace(`${action.task.id} : True := by sorry`, `${action.task.id} : True := by trivial`));
      } else finishAssignment(action, options);
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '6'], directory)).toBe(0);
    expect(attempts).toBe(2);
    expect(cooperationState().deliveries.filter((record: any) => record.kind === 'research'))
      .toMatchObject([{ taskId: 'question', summary: 'The current route uses True.intro; both targets remain to be proved.' }]);
    expect(cooperationState().tasks[0]).toMatchObject({ status: 'completed', attempts: 2 });
  });

  it.each([false, true])('checks saved cooperative proof checkpoints without publishing unfinished work as failure (complete: %s)', async complete => {
    let attempts = 0, seed = '';
    configureCooperation(async (action, options, message) => {
      if (action.kind === 'task' && action.task.id === 'a') {
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        if (++attempts === 1) {
          seed = action.assignment.seedCommit;
          fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('theorem first', 'lemma partial : True := by trivial\ntheorem first'));
          if (complete) finishAssignment(action, options);
          return 'checkpoint';
        }
        expect(action.assignment.seedCommit).toBe(seed);
        expect(fs.readFileSync(file, 'utf8')).toContain('lemma partial : True := by trivial');
        expect(message).toContain('math_task_missing_declaration');
        expect(cooperationState().deliveries?.some((record: any) => record.taskId === 'a' && record.kind === 'failure')).toBeFalsy();
      }
      finishAssignment(action, options); return 'completed';
    });
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '8'], directory)).toBe(0);
    expect(attempts).toBe(complete ? 1 : 2);
    expect(cooperationState().tasks[0].status).toBe('integrated');
  });

  it.each(['markdown', 'json'])('requests a Lead decision after two unchanged completed %s research deliveries', async format => {
    const tasks: CooperativeTask[] = [
      { id: 'question', kind: 'research', objective: 'Find a current proof route', dependsOn: [], revision: 0 },
      ...planTasks().slice(2).map(task => ({ ...task, dependsOn: task.id === 'first' ? ['question'] : ['first'] })),
    ];
    let attempts = 0;
    configureCooperation(async (action, options, message) => {
      if (action.kind === 'lead') {
        writePlan(options.workspace, tasks);
        for (const worker of JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8')).workers.slice(1)) {
          fs.writeFileSync(path.join(worker.worktree, 'RESEARCH.md'), format === 'markdown' ? 'An old route that has not been checked.' :
            JSON.stringify({ summary: 'An old route that has not been checked.' }));
          commitSolverSources(problem, worker.worktree);
        }
      } else {
        expect(action.kind === 'task' && action.task.id).toBe('question');
        if (++attempts > 1) expect(message).toContain('math_research_delivery_unchanged');
        // Changing only the mode must not make the inherited finding fresh.
        fs.chmodSync(path.join(options.workspace, 'RESEARCH.md'), 0o755);
      }
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '3'], directory)).toBe(4);
    expect(attempts).toBe(2);
    expect(cooperationState().tasks[0]).toMatchObject({ status: 'blocked', attempts: 2, feedback: expect.stringContaining('math_research_delivery_unchanged') });
    expect(cooperationState().tasks.slice(1).every((node: any) => node.attempts === 0)).toBe(true);
    expect(cooperationState().deliveries).toEqual([expect.objectContaining({ taskId: 'question', kind: 'failure', status: 'failed' })]);
    expect(host.verify).not.toHaveBeenCalled();
  });

  it('resumes a proof review checkpoint without accepting its saved verdict prematurely', async () => {
    let reviews = 0;
    configureCooperation(async (action, options) => {
      if (action.kind === 'review' && ++reviews === 1) {
        finishAssignment(action, options); return 'checkpoint';
      }
      if (action.kind === 'review') {
        expect(cooperationState().review.status).toBe('running');
        expect(cooperationState().deliveries.some((record: any) => record.kind === 'review')).toBe(false);
        expect(host.officialGate).not.toHaveBeenCalled();
      }
      finishAssignment(action, options); return 'completed';
    });
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '7'], directory)).toBe(0);
    expect(reviews).toBe(2);
    expect(cooperationState().deliveries.filter((record: any) => record.kind === 'review')).toMatchObject([{ status: 'accepted' }]);
  });

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
      if (!action.assignment.connectionCheck) {
        expect(source).toContain('lemma a : True := by trivial');
        expect(source).toContain('lemma b : True := by trivial');
      }
      fs.writeFileSync(file, source.replace('first : True := by sorry', 'first : True := by exact And.left (And.intro a b)'));
    } else fs.writeFileSync(file, source.replace('second : True := by sorry', 'second : True := by exact first'));
  }

  it('provides an unambiguous Lead plan example when multiple Lean files are owned', async () => {
    const helper = 'Submission/Helpers.lean';
    fs.mkdirSync(path.join(project, 'Submission'));
    fs.writeFileSync(path.join(project, helper), 'namespace Submission.Helpers\nend Submission.Helpers\n');
    const receipt = JSON.parse(fs.readFileSync(problem.activeProblemPath, 'utf8'));
    receipt.solverOwnedFiles.push(helper);
    fs.writeFileSync(problem.activeProblemPath, JSON.stringify(receipt));
    git(workspace, ['add', '--', 'generated/p/Submission/Helpers.lean']);
    commitFixture(workspace, 'Owned helper module');
    problem = readSolverProblem(workspace, problem.activeProblemPath);
    expect(await runSolver([...args, '--workers', '4', '--startup-only'], directory)).toBe(0);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    state.cooperation = { tasks: [] };
    const context = directSolverModules.M4.build(problem, state, { root: directory, worktree: state.worktree,
      environment: {}, taskText: 'Prove both targets', retrievalRoot: project,
      assignment: { kind: 'lead', seedCommit: problem.baseCommit } });
    expect(context.instructions).toContain(JSON.stringify(problem.ownedFiles));
    expect(context.instructions).toContain('leave Lean sources unchanged during planning');
    expect(context.instructions).toContain('Return the plan without running Lean diagnostics');
    expect(context.instructions).not.toContain('FULL_CLOSED_LEAN_TYPE');
    const example = JSON.parse(context.instructions.match(/Write one JSON object in RESEARCH\.md: (\{.*?\})\. Include/u)![1]);
    example.tasks[0].theoremName = 'Submission.helper';
    example.tasks[0].type = 'True';
    example.tasks[1].theoremName = 'Submission.first';
    example.tasks.push({ id: 'second', kind: 'goal', objective: 'Prove the second target', theoremName: 'Submission.second' });
    expect(parseCooperationPlan(problem, example).tasks[0].proofPath).toBe('Submission.lean');
    example.tasks[0].proofPath = helper;
    expect(parseCooperationPlan(problem, example).tasks[0].proofPath).toBe(helper);
    fs.writeFileSync(path.join(workspace, 'RESEARCH.md'),
      'Mathematical route: prove the shared helper, then apply it to each original target.\n\n```math-plan\n' +
      JSON.stringify(example) + '\n```\n');
    expect(readCooperationPlan(problem, workspace).tasks[0].proofPath).toBe(helper);
    delete example.tasks[0].proofPath;
    expect(() => parseCooperationPlan(problem, example)).toThrow('math_plan_invalid_proof_target');
    expect(host.createSession).not.toHaveBeenCalled();
  });

  it('accepts larger cooperative plans and preserves their full mathematical content', () => {
    const type = '(True ∧ '.repeat(1000) + 'True' + ')'.repeat(1000);
    const premises = ['P'.repeat(2001), ...Array(32).fill('A')];
    const tasks: CooperativeTask[] = [...planTasks(), ...Array.from({ length: 29 }, (_, index) => ({
      id: `question-${index}`, kind: 'research' as const, objective: 'Explore an independent question', dependsOn: [], revision: 0,
    }))];
    tasks[0] = { ...tasks[0], objective: 'O'.repeat(2001), type, premises, statementReview: true, informalStatement: 'M'.repeat(8001) };
    const groups: RouteGroup[] = [{ id: 'main', objective: 'G'.repeat(2001), status: 'active', revision: 0, maxConcurrent: 4 },
      ...Array.from({ length: 16 }, (_, index) => ({ id: `route-${index}`, objective: 'Explore another route', status: 'active' as const, revision: 0 }))];
    writePlan(workspace, tasks, groups);
    const plan = readCooperationPlan(problem, workspace);
    expect(plan.tasks).toHaveLength(33); expect(plan.groups).toEqual(groups);
    expect(plan.tasks[0]).toMatchObject(tasks[0]);
    expect(() => parseCooperationPlan(problem, { ...plan, tasks: plan.tasks.filter(task => task.id !== 'second') }))
      .toThrow('math_plan_incomplete_original_coverage');
    expect(() => parseCooperationPlan(problem, { ...plan, tasks: plan.tasks.map(task => task.id === 'a' ? { ...task, dependsOn: ['first'] } : task) }))
      .toThrow('math_plan_dependency_cycle');
    expect(() => parseCooperationPlan(problem, { ...plan, tasks: plan.tasks.map(task => task.id === 'a' ? { ...task, premises: [123] } : task) }))
      .toThrow('math_plan_invalid_task');
  });

  it('reads an explicitly empty route list as the implicit main route', () => {
    const tasks = planTasks().map(task => ({ ...task, groupId: undefined }));
    const planned = parseCooperationPlan(problem, { tasks, groups: [] });
    expect(planned.groups).toEqual([{ id: 'main', objective: 'Prove the original problem', status: 'active', revision: 0 }]);
    expect(planned.tasks.every(task => task.groupId === undefined)).toBe(true);
    expect(parseCooperationPlan(problem, { tasks })).toEqual(planned);
  });

  it.each(['lead', 'task', 'backtranslate', 'statement-review', 'review'])('does not charge an unstarted cooperative %s assignment', async stoppedKind => {
    const statementPhase = stoppedKind === 'backtranslate' || stoppedKind === 'statement-review';
    const tasks = statementPhase ? statementTasks() : planTasks();
    // Keep independent proof work from stopping all peers before the statement context is ready.
    if (statementPhase) tasks[1] = { ...tasks[1], dependsOn: ['a'] };
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else finishAssignment(action, options);
      return 'completed';
    });
    const select = vi.fn((...inputs: Parameters<typeof directSolverModules.M3.select>) => {
      const assignment = inputs[3]!;
      const stop = stoppedKind === 'lead' ? true : stoppedKind === 'review' ? assignment.kind === 'review' :
        assignment.kind !== 'lead' && !(stoppedKind === 'statement-review' && assignment.kind === 'backtranslate');
      return stop ? { operation: 'stop' as const, reason: 'no-operation' as const } : directSolverModules.M3.select(...inputs);
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '12'], directory,
      { ...directSolverModules, M3: { ...directSolverModules.M3, select } })).toBe(4);
    expect(select.mock.calls.some(call => call[3]?.kind === stoppedKind)).toBe(true);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    const spent = stoppedKind === 'review' ? 4 : stoppedKind === 'statement-review' ? 1 : 0;
    expect(state.cooperation.groups?.[0]?.turns ?? 0).toBe(spent);
    expect(state.turns).toBe(spent + (stoppedKind === 'lead' ? 0 : 1));
    expect(Object.values(state.dispatchCounts).reduce((sum: number, value: any) => sum + value, 0)).toBe(state.turns);
    expect(state.dispatchCounts.planning ?? 0).toBe(stoppedKind === 'lead' ? 0 : 1);
    expect(state.cooperation.tasks.every((node: any) => node.attempts === (stoppedKind === 'review' ? 1 : 0))).toBe(true);
    if (stoppedKind === 'review') expect(state.cooperation.review.status).toBe('pending');
    if (stoppedKind === 'backtranslate') expect(state.cooperation.statementReviews[0].status).toBe('pending');
    if (stoppedKind === 'statement-review') expect(state.cooperation.statementReviews[0].status).toBe('translated');
  });

  it('executes the direct method through cooperative roles without singleton lemma proposals', async () => {
    const operations: string[] = [];
    configureCooperation(async (action, options, message) => {
      expect(message).not.toContain('Propose one new ordinary theorem');
      expect(message).not.toContain('"target":"Original.qualifiedTarget"');
      expect(message).not.toContain('Research operation:');
      finishAssignment(action, options); return 'completed';
    });
    const execute = vi.fn(async (...inputs: Parameters<typeof directSolverModules.M1.execute>) => {
      operations.push(inputs[2]);
      return directSolverModules.M1.execute(...inputs);
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '6'], directory,
      { ...directSolverModules, M1: { ...directSolverModules.M1, execute } })).toBe(0);
    expect(new Set(operations)).toEqual(new Set(['direct']));
    expect(cooperationState().tasks.every((node: any) => node.status === 'integrated')).toBe(true);
    expect(host.officialGate).toHaveBeenCalledOnce();
  });

  it('uses replacement task evidence, blind contexts, role slots and reviewer selection in one cooperative solve', async () => {
    const checkTask = vi.fn(directSolverModules.M2.checkTask);
    const workers = vi.fn((...inputs: Parameters<typeof directSolverModules.M5.workers>) =>
      directSolverModules.M5.workers(...inputs).map((worker, index) => index === 1 ? { ...worker, id: 'mathematician' } :
        index === 2 ? { ...worker, id: 'auditor', role: 'reviewer' as const } : worker));
    const reviewer = vi.fn(directSolverModules.M5.reviewer);
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
      M5: { ...directSolverModules.M5, workers, reviewer },
    })).toBe(0);
    expect(checkTask).toHaveBeenCalled(); expect(statement).toHaveBeenCalledTimes(2); expect(workers).toHaveBeenCalledOnce();
    expect(reviewer).toHaveBeenCalled(); expect(reviews).toEqual(['auditor', 'auditor', 'auditor']);
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
    host.verify.mockImplementationOnce(async request => failed(verified(request)));
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

  it.each(['sourceDeclarationHash', 'targetCommit', 'claim'])('rejects replacement M2 receipts with a mismatched %s', async field => {
    configureCooperation();
    const checkTask = async (...inputs: Parameters<typeof directSolverModules.M2.checkTask>) => {
      const proof = await directSolverModules.M2.checkTask(...inputs);
      return { ...proof, verification: { ...proof.verification, results: proof.verification.results.map(result =>
        ({ ...result, [field]: field === 'claim' ? 'negation' : 'incorrect-identity' })) } };
    };
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '3'], directory,
      { ...directSolverModules, M2: { ...directSolverModules.M2, checkTask } })).toBe(4);
    const tasks = cooperationState().tasks;
    expect(tasks.some((node: any) => node.feedback === 'math_task_check_identity_changed')).toBe(true);
    expect(tasks.some((node: any) => node.status === 'integrated')).toBe(false);
    expect(host.officialGate).not.toHaveBeenCalled();
  });


  it('keeps adopted research scoped in route prompts and cooperation journals while Lead can inspect both routes', () => {
    const visible = { ...planTasks()[0], groupId: 'public' }, hidden = { ...planTasks()[1], groupId: 'private', sharing: 'group' as const };
    const sources: CooperativeTask[] = [visible, hidden].map((task, index) => ({ id: `investigation_${index}`, kind: 'research',
      objective: index ? 'PRIVATE_ADOPTION_FINDING' : 'Find a public bridge', dependsOn: [], revision: 0,
      groupId: task.groupId, sharing: task.sharing }));
    const archive: any = { canonicalCommit: problem.baseCommit,
      tasks: [...sources.map(task => ({ task, status: 'completed', attempts: 1 })),
        ...[visible, hidden].map(task => ({ task, status: 'pending', attempts: 0 }))],
      deliveries: sources.map((task, index) => ({ id: `proposal_${index}`, producer: 'researcher-2', taskId: task.id,
        taskDigest: taskVersion(task), kind: 'research', status: 'advisory', summary: task.objective,
        statement: '', premises: [], dependencies: [], remainingObligations: [], evidenceRefs: [], createdAt: 1,
        lemmaRequests: [[visible, hidden][index]] })) };
    archive.researchDecisions = resolveResearchHandoffs(archive, researchHandoffs(archive).map(item => item.id),
      archive.tasks.map((item: TaskRecord) => item.task), undefined);
    const lead = { id: 'solver', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles } as const;
    const peerRoot = path.join(directory, 'adoption-peer'); fs.mkdirSync(peerRoot);
    const peer = { id: 'researcher-1', role: 'researcher', worktree: peerRoot, ownedFiles: problem.ownedFiles } as const;
    const action = { kind: 'task' as const, task: visible, assignment: { taskId: visible.id, taskDigest: taskVersion(visible),
      workerId: peer.id, seedCommit: problem.baseCommit } };
    const state: any = { problem, runId: 'adoption-scope', turns: 0, phase: 'running', failures: [],
      environmentDigest: 'fixture', cooperation: archive };
    const cooperative = new CooperativeResearch({ state, workers: [lead, peer], access: new Map(),
      signal: new AbortController().signal, save: () => {}, emit: () => {}, modules: directSolverModules, exclusiveCheck: async check => check() });
    cooperative.activate(peer, action, async () => {}, async () => {});
    const scoped = cooperative.contextState(action);
    const bundle = directSolverModules.M4.build(problem, { ...state, cooperation: scoped }, {
      root: directory, worktree: peerRoot, taskText: 'Prove', environment: {}, retrievalRoot: workspace, assignment: action });
    const journal = JSON.parse(fs.readFileSync(path.join(peerRoot, 'COOPERATION.json'), 'utf8'));
    expect(journal.continuation.adoptedResearch.map((item: any) => item.taskId)).toEqual([visible.id]);
    expect(journal.continuation.adoptedResearch[0]).toMatchObject({ recordedProof: 'none', plannedGoalIds: [], referenceCoverage: 'unknown' });
    expect(bundle.message).toContain('"adoptedResearch"');
    expect(bundle.message).not.toContain('PRIVATE_ADOPTION_FINDING');
    expect(journal.continuation.adoptedResearch).not.toContainEqual(expect.objectContaining({ taskId: hidden.id }));
    expect(journal.continuation.unconnectedTasks).not.toContain(hidden.id);
    const leadJournal = JSON.parse(fs.readFileSync(path.join(workspace, 'COOPERATION.json'), 'utf8'));
    expect(leadJournal.continuation.adoptedResearch.map((item: any) => item.taskId)).toEqual([visible.id, hidden.id]);
    expect(buildRunInspection(state).continuation.adoptedResearch).toEqual(leadJournal.continuation.adoptedResearch);
    cooperative.deactivate(peer);
  });

  it('filters private statement reviews from both route prompts and cooperation journals', () => {
    const secret = { ...planTasks()[0], objective: 'PRIVATE_TASK_OBJECTIVE', groupId: 'private', sharing: 'group' as const };
    const publicTask = { ...planTasks()[1], groupId: 'public' };
    const shared = { ...planTasks()[2], groupId: 'private', sharing: 'problem' as const };
    const pending = { id: 'public-pending', kind: 'research' as const, objective: 'Explore a public route',
      groupId: 'private', sharing: 'problem' as const, dependsOn: [], revision: 0 };
    const progress = { id: 'public-progress', taskId: pending.id, taskDigest: taskVersion(pending), dependencies: [],
      producer: 'researcher-2', kind: 'progress', status: 'advisory', summary: 'PUBLIC_PENDING_PROGRESS' };
    const lead = { id: 'solver', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles } as const;
    const peerRoot = path.join(directory, 'peer'); fs.mkdirSync(peerRoot);
    const peer = { id: 'researcher-1', role: 'researcher', worktree: peerRoot, ownedFiles: problem.ownedFiles } as const;
    const assignment = { taskId: publicTask.id, taskDigest: taskVersion(publicTask), workerId: peer.id, seedCommit: problem.baseCommit };
    const action = { kind: 'task' as const, task: publicTask, assignment };
    const reviews = [secret, publicTask, shared].map(task => ({ id: task.id, taskId: task.id, taskDigest: taskVersion(task), status: 'accepted',
      leanStatement: `theorem ${task.id} : True`, intendedStatement: task.id === secret.id ? 'PRIVATE_ROUTE_MARKER' : 'VISIBLE_' + task.id,
      premises: [], dependencies: [], workspace: directory, files: [], commit: problem.baseCommit, snapshotDigest: 'fixture', environmentDigest: 'fixture' }));
    const archive: any = { tasks: [{ task: secret, status: 'integrated', attempts: 1 },
      { task: publicTask, status: 'running', attempts: 0, assignment }, { task: shared, status: 'integrated', attempts: 1 },
      { task: pending, status: 'running', attempts: 1 }], statementReviews: reviews,
      researchCheckpoints: {
        [secret.id]: { taskDigest: taskVersion(secret), inputDigest: 'PRIVATE_CHECKPOINT', outputDigest: 'private', count: 2, paused: true },
        [publicTask.id]: { taskDigest: taskVersion(publicTask), inputDigest: 'VISIBLE_CHECKPOINT', outputDigest: 'visible', count: 1, paused: false },
        [shared.id]: { taskDigest: 'stale', inputDigest: 'STALE_CHECKPOINT', outputDigest: 'stale', count: 1, paused: false },
      }, deliveries: [progress,
        { ...progress, id: 'private-progress', taskId: secret.id, taskDigest: taskVersion(secret), summary: 'PRIVATE_PROGRESS' },
        { ...progress, id: 'stale-progress', taskDigest: 'stale', summary: 'STALE_PROGRESS' },
        { ...progress, id: 'superseded-progress', status: 'superseded', summary: 'SUPERSEDED_PROGRESS' },
        { ...progress, id: 'stale-dependency', dependencies: [{ taskId: publicTask.id, taskDigest: 'stale' }], summary: 'STALE_DEPENDENCY' }] };
    const hiddenRoute = { id: 'PRIVATE_ROUTE_MARKER', targetTaskId: shared.id,
      prerequisiteTaskIds: [], closingTaskId: secret.id };
    archive.tasks.find((node: TaskRecord) => node.task.id === shared.id).alternativeRoutes = [hiddenRoute];
    archive.proofRoutes = [hiddenRoute];
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
    expect(scoped.deliveries).toEqual([progress]);
    expect(Object.keys(scoped.researchCheckpoints ?? {})).toEqual([publicTask.id]);
    expect(JSON.stringify(scoped)).not.toContain('PRIVATE_CHECKPOINT'); expect(JSON.stringify(scoped)).not.toContain('STALE_CHECKPOINT');
    expect(bundle.message).toContain('PUBLIC_PENDING_PROGRESS');
    expect(bundle.message).not.toContain('PRIVATE_PROGRESS'); expect(bundle.message).not.toContain('STALE_PROGRESS');
    expect(bundle.message).not.toContain('SUPERSEDED_PROGRESS'); expect(bundle.message).not.toContain('STALE_DEPENDENCY');
    cooperative.activate(peer, action, async () => {}, async () => {});
    const journal = JSON.parse(fs.readFileSync(path.join(peerRoot, 'COOPERATION.json'), 'utf8'));
    expect(journal.statements.map((review: any) => review.taskId))
      .toEqual([publicTask.id, shared.id]);
    expect(journal.continuation.evidence).toBe('recorded-not-replayed');
    expect(journal.routePriority).toMatchObject({ count: 0, routes: [], digest: mathDigest(canonicalMathJson([])) });
    expect(journal.frontierFocus.digest).toBe(mathDigest(canonicalMathJson(journal.frontierFocus.taskIds)));
    expect(JSON.stringify(journal.routePriority)).not.toContain('PRIVATE_ROUTE_MARKER');
    expect(scoped.tasks.find(node => node.task.id === shared.id)?.alternativeRoutes).toEqual([]);
    const fullIndex = JSON.parse(fs.readFileSync(path.join(workspace, 'COOPERATION.json'), 'utf8')).routePriority;
    expect(fullIndex.count).toBe(1);
    expect(fullIndex.digest).toBe(mathDigest(canonicalMathJson(fullIndex.routes)));
    expect(fullIndex.routes[0].routeId).toBe(hiddenRoute.id);
    expect(journal.continuation.goals.map((goal: any) => goal.taskId)).toEqual([shared.id]);
    expect(JSON.stringify(journal.continuation)).not.toContain('PRIVATE_TASK_OBJECTIVE');
    expect(JSON.stringify(journal.continuation)).not.toContain('PRIVATE_ROUTE_MARKER');
    cooperative.deactivate(peer);
    expect(fs.readFileSync(path.join(peerRoot, 'COOPERATION.json'), 'utf8')).not.toContain('PRIVATE_ROUTE_MARKER');
    expect(cooperative.contextState(undefined, peer).statementReviews?.map(review => review.taskId)).toEqual([publicTask.id, shared.id]);
    expect(cooperative.contextState({ ...action, task: secret }).statementReviews?.map(review => review.taskId)).toContain(secret.id);
    expect(cooperative.contextState({ ...action, task: secret }).researchCheckpoints?.[secret.id]?.inputDigest).toBe('PRIVATE_CHECKPOINT');
    expect(cooperative.contextState(undefined, lead).statementReviews).toHaveLength(3);
  });

  it.each(['backtranslate', 'statement-review'] as const)('publishes a %s rejection with the complete failure state', async kind => {
    const task = planTasks()[0];
    const lead = { id: 'solver', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles } as const;
    const peerRoot = path.join(directory, 'peer'); fs.mkdirSync(peerRoot);
    const peer = { id: 'researcher-1', role: 'researcher', worktree: peerRoot, ownedFiles: problem.ownedFiles } as const;
    const review = { id: 'statement', taskId: task.id, taskDigest: taskVersion(task),
      status: kind === 'backtranslate' ? 'translating' : 'reviewing', workerId: peer.id,
      commit: problem.baseCommit, snapshotDigest: 'snapshot', workspace: peerRoot };
    const action = { kind, reviewId: review.id, taskId: task.id, taskDigest: review.taskDigest,
      seedCommit: review.commit, snapshotDigest: review.snapshotDigest, workspace: peerRoot };
    const state: any = { problem, runId: 'rejection', turns: 0, phase: 'running',
      cooperation: { tasks: [{ task, status: 'pending', attempts: 0 }],
        groups: [{ group: { id: 'main', status: 'active' }, turns: 0 }], statementReviews: [review] } };
    const saved: any[] = [];
    const notify = vi.fn(async () => {
      const snapshot = saved.at(-1);
      expect(snapshot.error).toBe('fixture_rejected');
      expect(snapshot.statementReviews[0]).toMatchObject({ status: 'changes_requested', summary: 'fixture_rejected' });
      expect(snapshot.deliveries.at(-1)).toMatchObject({ kind: 'failure', status: 'failed', summary: 'fixture_rejected' });
    });
    const cooperative = new CooperativeResearch({ state, workers: [lead, peer], access: new Map(),
      signal: new AbortController().signal, save: () => saved.push(JSON.parse(JSON.stringify(state.cooperation))),
      emit: () => {}, modules: directSolverModules, exclusiveCheck: async check => check() });
    cooperative.activate(lead, { kind: 'lead', seedCommit: problem.baseCommit }, async () => {}, notify);
    cooperative.rejected(action, 'fixture_rejected');
    await cooperative.stop();
    expect(notify).toHaveBeenCalledOnce();
    await expect(notify.mock.results[0].value).resolves.toBeUndefined();
  });

  it('preserves an unavailable task check for recovery without recording a mathematical failure', async () => {
    configureCooperation();
    const checkTask = async (...inputs: Parameters<typeof directSolverModules.M2.checkTask>) => {
      const proof = await directSolverModules.M2.checkTask(...inputs);
      return { ...proof, passed: false, verification: { ...proof.verification, status: 'unavailable' as const } };
    };
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '2'], directory,
      { ...directSolverModules, M2: { ...directSolverModules.M2, checkTask } })).toBe(1);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'runtime_error', reason: 'math_verifier_unavailable' });
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    const archived = state.cooperation;
    const pending = archived.tasks.find((node: any) => node.status === 'pending' &&
      node.feedback === 'math_verifier_unavailable' && node.proof.verification.status === 'unavailable');
    expect(pending).toBeDefined();
    for (const commit of [pending.proof.commit, pending.proof.verification.targetCommit])
      expect(git(state.worktree, ['rev-parse', `refs/math/${state.runId}/evidence/${commit}`])).toBe(commit);
    expect((archived.deliveries ?? []).filter((record: any) => record.taskId === pending.task.id &&
      (record.kind === 'failure' || record.status === 'failed'))).toEqual([]);
    expect(archived.failedTaskInputs ?? []).toEqual([]);
    expect(host.officialGate).not.toHaveBeenCalled();
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
        commitFixture(checkout, 'Alter context');
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
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace,
        planTasks().map(task => task.kind === 'goal' ? { ...task, conditional: false } : task));
      else finishAssignment(action, options);
      return 'completed';
    });
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
    if (failure) expect(state.workers.filter((worker: any) => ['researcher-1', 'engineer'].includes(worker.id))
      .reduce((turns: number, worker: any) => turns + worker.turns, 0)).toBe(2);
  });


  it('keeps preassigned peers available when another worker reserves the last turn', async () => {
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace,
        planTasks().map(task => task.kind === 'goal' ? { ...task, conditional: false } : task));
      else finishAssignment(action, options);
      return 'completed';
    });
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
      if (action.kind === 'lead') writePlan(options.workspace, tasks,
        [{ id: 'main', objective: 'Prove the original obligations', status: 'active', revision: 0, engineerId: 'engineer' }]);
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

  it.each(['math', 'json', 'plain', 'markdown'])('accepts %s responses for plans, research, backtranslation and reviews', async format => {
    const tasks: CooperativeTask[] = [{ id: 'question', kind: 'research', objective: 'Explore a route', dependsOn: [], revision: 0 }, ...planTasks()];
    tasks[3] = { ...tasks[3], statementReview: true, informalStatement: 'The proposition True holds.' };
    const mathematics = format === 'markdown' ? '# Mathematics\nThe proposition True holds.\n\n```math\n\\top\n```\n\n```math\nTrue\n```' : 'The proposition True holds.';
    const review = { verdict: 'accepted', ...(format === 'math' ? { summary: 'x'.repeat(3007), evidenceRefs: Array(17).fill('S'.repeat(1001)) } :
      format === 'json' ? { summary: 'The statement matches its intention.', evidenceRefs: [123, 'STATEMENT.json'] } :
      format === 'markdown' ? { evidenceRefs: 'STATEMENT.json' } : {}) };
    const write = (workspace: string, value: object) => fs.writeFileSync(path.join(workspace, 'RESEARCH.md'),
      ['math', 'json'].includes(format) ? '```' + format + '\n' + JSON.stringify(value) + '\n```' : JSON.stringify(value));
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') write(options.workspace, { tasks: tasks.map(({ revision: _revision, proofPath: _path, dependsOn, ...task }) =>
        ({ ...task, ...(dependsOn.length ? { dependsOn } : {}) })) });
      else if (action.kind === 'backtranslate' && format === 'markdown') fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), mathematics);
      else if (action.kind === 'backtranslate') write(options.workspace, { mathematics });
      else if (action.kind === 'statement-review' || action.kind === 'review') write(options.workspace, review);
      else if (action.kind === 'task' && action.task.kind === 'research' && format === 'markdown')
        fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), 'True.intro provides the needed proof.');
      else if (action.kind === 'task' && action.task.kind === 'research') write(options.workspace, { summary: 'True.intro provides the needed proof.' });
      else finishAssignment(action, options);
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '9'], directory)).toBe(0);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.cooperation.tasks.map((node: any) => node.task)).toEqual(tasks);
    expect(state.cooperation.statementReviews[0]).toMatchObject({ status: 'accepted', translation: {
      mathematics, assumptions: [], definitions: [], evidenceRefs: [] } });
    expect(state.cooperation.review).toMatchObject({ status: 'accepted', summary: deliveryDetails(review).summary });
    expect(state.cooperation.deliveries.find((record: any) => record.kind === 'review').evidenceRefs).toEqual(deliveryDetails(review).evidenceRefs);
    expect(state.cooperation.deliveries.find((record: any) => record.kind === 'research')).toMatchObject({ taskId: 'question', evidenceRefs: [] });
    expect(host.officialGate).toHaveBeenCalledOnce();
  });

  it.each(['math-result', 'json'])('keeps explicit response bindings for host validation and rejects ambiguous %s blocks', fence => {
    const file = path.join(workspace, 'RESEARCH.md');
    fs.writeFileSync(file, '```math\n{"summary":"first"}\n```\n```' + fence + '\n{"summary":"second"}\n```');
    expect(() => readMathResponse(workspace, 'math-result')).toThrow('requires_one_block');
    expect(() => readMathResponse(workspace, 'math-result', {}, 'summary')).toThrow('requires_one_block');
    fs.writeFileSync(file, '```math\n{"commit":"wrong-version","summary":"first"}\n```');
    expect(readMathResponse(workspace, 'math-review', { commit: 'assigned-version' }).commit).toBe('wrong-version');
  });

  it('does not parse an inherited plan fence as Markdown research findings', () => {
    writePlan(workspace, planTasks());
    expect(() => readMathResponse(workspace, 'math-result', {}, 'summary')).toThrow('requires_one_block');
    fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), '# Findings\nUse True.intro.\n\n```lean\nexact True.intro\n```');
    expect(readMathResponse(workspace, 'math-result', {}, 'summary').summary).toContain('Use True.intro.');
  });

  it('bounds a 3007-character advisory summary without discarding its verdict, evidence or raw response', () => {
    const value = { verdict: 'changes_requested', summary: 'x'.repeat(3007), evidenceRefs: ['STATEMENT.json'], remainingObligations: ['Resolve the coefficient'] };
    const raw = '```math\n' + JSON.stringify(value) + '\n```';
    fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), raw);
    const response = readMathResponse(workspace, 'math-statement-review');
    const details = deliveryDetails(response);
    expect(response.verdict).toBe('changes_requested'); expect(details.summary).toHaveLength(3000);
    expect(details.evidenceRefs).toEqual(value.evidenceRefs); expect(details.remainingObligations).toEqual(value.remainingObligations);
    expect(fs.readFileSync(path.join(workspace, 'RESEARCH.md'), 'utf8')).toBe(raw);
    expect(deliveryDetails({ ...value, evidenceRefs: [123, 'STATEMENT.json'] }).evidenceRefs).toEqual(['STATEMENT.json']);
    expect(() => deliveryDetails({ ...value, remainingObligations: [123] })).toThrow('math_delivery_invalid');
    fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), 'x'.repeat(64001));
    expect(readMathResponse(workspace, 'math-result', {}, 'summary').summary).toHaveLength(64001);
    fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), JSON.stringify({ ...value, summary: 'x'.repeat(100000) }));
    expect(deliveryDetails(readMathResponse(workspace, 'math-statement-review')).summary).toHaveLength(3000);
  });

  it('preserves long mathematical explanations, premises and obligations without field quotas', () => {
    const mathematics = 'x'.repeat(8001), assumptions = ['y'.repeat(2001), ...Array(32).fill('A')];
    const value = { mathematics, assumptions, definitions: assumptions, statement: mathematics, premises: assumptions,
      remainingObligations: assumptions, evidenceRefs: 'STATEMENT.json' };
    fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), JSON.stringify(value));
    const response = readMathResponse(workspace, 'math-backtranslation');
    expect(readBacktranslation(response)).toEqual({ mathematics, assumptions, definitions: assumptions, evidenceRefs: ['STATEMENT.json'] });
    expect(deliveryDetails(response)).toEqual({ summary: '', statement: mathematics, premises: assumptions,
      remainingObligations: assumptions, evidenceRefs: ['STATEMENT.json'] });
  });

  it('identifies changed inherited helper parameters and permits newly named helpers', () => {
    const file = path.join(project, 'Submission.lean');
    const seedSource = original.replace('end Submission', 'lemma kept : True := by trivial\nend Submission');
    fs.writeFileSync(file, seedSource);
    const seedCommit = commitSolverSources(problem, workspace);
    const task: CooperativeTask = { id: 'candidate', kind: 'lemma', objective: 'Prove a new helper', dependsOn: [], revision: 0,
      proofPath: 'Submission.lean', theoremName: 'Submission.candidate', type: 'True' };
    const edited = seedSource.replace('lemma kept : True := by trivial', 'lemma kept (h : True) : True := by exact h');
    fs.writeFileSync(file, edited);
    const rejectedCommit = commitSolverSources(problem, workspace);
    expect(() => taskChanges(problem, workspace, rejectedCommit, task, { seedCommit }))
      .toThrow(new RegExp('math_task_existing_declaration_changed[\\s\\S]*Submission\\.lean[\\s\\S]*kept[\\s\\S]*' + seedCommit));
    fs.writeFileSync(file, seedSource.replace('end Submission', 'lemma candidate : True := by trivial\nend Submission'));
    const acceptedCommit = commitSolverSources(problem, workspace);
    expect(taskChanges(problem, workspace, acceptedCommit, task, { seedCommit })).toMatchObject([
      { file: 'Submission.lean', name: 'candidate', after: 'lemma candidate : True := by trivial\n' },
    ]);
  });

  it('merges prerequisite moves before an original goal without discarding peer additions', async () => {
    const file = path.join(project, 'Submission.lean');
    const helper = 'lemma prerequisite : True := by trivial\n';
    const seed = original.replace('end Submission', helper + 'end Submission');
    fs.writeFileSync(file, seed);
    const seedCommit = commitSolverSources(problem, workspace);
    const task: CooperativeTask = { id: 'first', kind: 'goal', objective: 'Prove the first target', dependsOn: [], revision: 0,
      proofPath: 'Submission.lean', theoremName: 'Submission.first' };
    const candidate = original.replace('theorem first', helper + 'theorem first').replace('first : True := by sorry', 'first : True := by exact prerequisite');
    fs.writeFileSync(file, candidate);
    const changes = taskChanges(problem, workspace, commitSolverSources(problem, workspace), task, { seedCommit });
    await withSolverWorktree(workspace, seedCommit, async checkout => {
      const mergedFile = path.join(checkout, problem.projectRelative, 'Submission.lean');
      fs.writeFileSync(mergedFile, seed.replace('end Submission', 'lemma peer : True := by trivial\nend Submission'));
      applyTaskChanges(problem, checkout, changes);
      const merged = fs.readFileSync(mergedFile, 'utf8');
      expect(merged.indexOf('lemma prerequisite')).toBeLessThan(merged.indexOf('theorem first'));
      expect(merged).toContain('first : True := by exact prerequisite');
      expect(merged).toContain('lemma peer : True := by trivial');
      applyTaskChanges(problem, checkout, changes);
      expect(fs.readFileSync(mergedFile, 'utf8')).toBe(merged);
    });
  });

  it('merges independent helpers inside an initially empty namespace', async () => {
    const helper = 'Submission/Helpers.lean';
    const empty = 'import Mathlib.Data.Nat.Basic\n\nnamespace Submission.Helpers\n\nend Submission.Helpers\n';
    fs.mkdirSync(path.join(project, 'Submission'));
    fs.writeFileSync(path.join(project, helper), empty);
    const receipt = JSON.parse(fs.readFileSync(problem.activeProblemPath, 'utf8'));
    receipt.solverOwnedFiles.push(helper);
    fs.writeFileSync(problem.activeProblemPath, JSON.stringify(receipt));
    git(workspace, ['add', '--', `generated/p/${helper}`]);
    commitFixture(workspace, 'Owned helper module');
    problem = readSolverProblem(workspace, problem.activeProblemPath);
    const task: CooperativeTask = { id: 'first', kind: 'goal', objective: 'Prove the first target', dependsOn: [], revision: 0,
      proofPath: 'Submission.lean', theoremName: 'Submission.first' };
    const changes = ['lemma a : True := by trivial\nlemma b : True := by trivial\n', 'lemma peer : True := by trivial\n'].map(proof => {
      fs.writeFileSync(path.join(project, helper), empty.replace('end Submission.Helpers', proof + 'end Submission.Helpers'));
      return taskChanges(problem, workspace, commitSolverSources(problem, workspace), task, { seedCommit: problem.baseCommit });
    });
    await withSolverWorktree(workspace, problem.baseCommit, async checkout => {
      for (const change of changes) applyTaskChanges(problem, checkout, change);
      const file = path.join(checkout, problem.projectRelative, helper);
      const source = fs.readFileSync(file, 'utf8');
      expect(inspectScopedLeanDeclarations(source).map(item => item.qualifiedName))
        .toEqual(['Submission.Helpers.a', 'Submission.Helpers.b', 'Submission.Helpers.peer']);
      expect(leanDeclarationContextCommands(source, 'Submission.Helpers.a').before).toEqual(['namespace Submission.Helpers']);
      expect(source).toContain('import Mathlib.Data.Nat.Basic');
      for (const change of changes) applyTaskChanges(problem, checkout, change);
      expect(fs.readFileSync(file, 'utf8')).toBe(source);
    });
  });

  it('checks and merges proof-only repairs and new helpers across owned files while protecting statements', async () => {
    const helper = 'Submission/Helpers.lean', module = 'Mathlib.Data.Nat.Basic';
    const seed = 'namespace Submission.Helpers\ndef generatedValue : Nat := 2\nlemma kept : True := by trivial\nend Submission.Helpers\n';
    fs.mkdirSync(path.join(project, 'Submission'));
    fs.writeFileSync(path.join(project, helper), 'namespace Submission.Helpers\nend Submission.Helpers\n');
    const receipt = JSON.parse(fs.readFileSync(problem.activeProblemPath, 'utf8'));
    receipt.solverOwnedFiles.push(helper);
    fs.writeFileSync(problem.activeProblemPath, JSON.stringify(receipt));
    git(workspace, ['add', '--', `generated/p/${helper}`]);
    commitFixture(workspace, 'Owned helper module');
    problem = readSolverProblem(workspace, problem.activeProblemPath);
    configureCooperation();
    fs.writeFileSync(path.join(project, helper), seed);
    const seedCommit = commitSolverSources(problem, workspace);
    const task = planTasks()[0], assignment = { taskId: task.id, taskDigest: taskVersion(task), workerId: 'researcher', seedCommit };
    const source = `import ${module}\n` + seed.replace('kept : True := by trivial', 'kept : True := by exact True.intro')
      .replace('end Submission.Helpers', 'lemma support : True := by trivial\nend Submission.Helpers');
    fs.writeFileSync(path.join(project, helper), source);
    fs.writeFileSync(path.join(project, 'Submission.lean'), original.replace('theorem first', 'lemma a : True := by trivial\ntheorem first'));
    const commit = commitSolverSources(problem, workspace);
    const proof = await checkTaskProof(problem, workspace, commit, task, assignment, [], {}, new AbortController().signal);
    expect(proof.passed).toBe(true);
    expect(proof.changes.map(change => [change.file, change.name])).toEqual([
      ['Submission.lean', 'a'], [helper, 'kept'], [helper, 'support'],
    ]);
    await withSolverWorktree(workspace, seedCommit, async checkout => {
      applyTaskChanges(problem, checkout, proof.changes, proof.imports);
      expect(fs.readFileSync(path.join(checkout, problem.projectRelative, helper), 'utf8')).toBe(source);
    });
    for (const modified of [source.replace('lemma kept : True', 'lemma kept (h : True) : True'),
      source.replace('generatedValue : Nat := 2', 'generatedValue : Nat := 3'),
      source.replace('lemma kept : True := by exact True.intro\n', '')]) {
      fs.writeFileSync(path.join(project, helper), modified);
      expect(() => taskChanges(problem, workspace, commitSolverSources(problem, workspace), task, assignment))
        .toThrow(/math_task_existing_declaration_(?:changed|removed)/u);
    }
    fs.writeFileSync(path.join(project, helper), source);
    fs.writeFileSync(path.join(project, 'Submission.lean'), original.replace('second : True := by sorry', 'second : True := by trivial'));
    expect(() => taskChanges(problem, workspace, commitSolverSources(problem, workspace), task, assignment))
      .toThrow('math_task_existing_declaration_changed');
  });

  it('removes orphan wrapper chains when a conditional task abstracts a saved dependency', () => {
    const file = path.join(project, 'Submission.lean');
    const source = original.replace('theorem first',
      'lemma dependency₂ : True := by trivial\nlemma dependency_wrapper : True := dependency₂\n' +
      'lemma wrapper_chain : True := dependency_wrapper\nlemma parent : True := Submission.dependency₂\n' +
      'lemma parent_wrapper : True := parent\ntheorem first');
    fs.writeFileSync(file, source);
    const commit = commitSolverSources(problem, workspace);
    const dependency: CooperativeTask = { id: 'dependency', kind: 'lemma', objective: 'Prove the premise', dependsOn: [],
      revision: 0, proofPath: 'Submission.lean', theoremName: 'Submission.dependency₂', type: 'True' };
    const task: CooperativeTask = { id: 'parent', kind: 'lemma', objective: 'Prove the connection', dependsOn: ['dependency'],
      revision: 0, proofPath: 'Submission.lean', theoremName: 'Submission.parent', type: 'True', conditional: true };
    const unconditional = createTaskSourceProjector(problem, workspace, commit)(task, []).get('Submission.lean')!;
    expect(unconditional).toContain('lemma dependency₂ : True');
    expect(unconditional).toContain('lemma dependency_wrapper : True');
    const projected = createTaskSourceProjector(problem, workspace, commit)(task, [], [dependency]).get('Submission.lean')!;
    expect(projected).toContain('lemma parent (dependency₂ : True) : True := dependency₂');
    expect(projected).not.toContain('Submission.dependency₂');
    for (const name of ['dependency₂', 'dependency_wrapper', 'wrapper_chain', 'parent_wrapper'])
      expect(projected).not.toMatch(new RegExp(`lemma ${name} :`));
    expect(fs.readFileSync(file, 'utf8')).toBe(source);
  });

  it.each(['sorry', 'admit'])('isolates unfinished peer proofs without assuming a required %s dependency', placeholder => {
    const file = path.join(project, 'Submission.lean');
    const source = original.replace('theorem first',
      `lemma unfinished : True := by ${placeholder}\nlemma wrapper : True := unfinished\n` +
      'lemma valid : True := by trivial\nlemma consumer : True := unfinished\ntheorem first');
    fs.writeFileSync(file, source);
    const commit = commitSolverSources(problem, workspace);
    const task: CooperativeTask = { id: 'consumer', kind: 'lemma', objective: 'Check the consumer', dependsOn: [],
      revision: 0, proofPath: 'Submission.lean', theoremName: 'Submission.consumer', type: 'True' };
    const projected = createTaskSourceProjector(problem, workspace, commit)(task, []).get('Submission.lean')!;
    expect(projected).not.toContain('lemma unfinished');
    expect(projected).not.toContain('lemma wrapper');
    expect(projected).toContain('lemma valid : True := by trivial');
    expect(projected).toContain('lemma consumer : True := unfinished');
    const targeted = createTaskSourceProjector(problem, workspace, commit)(
      { ...task, theoremName: 'Submission.unfinished' }, []).get('Submission.lean')!;
    expect(targeted).toContain(`lemma unfinished : True := by ${placeholder}`);
    expect(fs.readFileSync(file, 'utf8')).toBe(source);
  });

  it('removes the complete noncomputable declaration prefix from an invalidated peer wrapper', () => {
      const file = path.join(project, 'Submission.lean');
      const source = original.replace('theorem first',
        'lemma premise : True := by trivial\n' +
        'noncomputable def wrapper : True := premise\n' +
        'theorem helper : True := by trivial\n' +
        'theorem consumer : True := helper\ntheorem first');
      fs.writeFileSync(file, source);
      const commit = commitSolverSources(problem, workspace);
      const dependency: CooperativeTask = { id: 'premise', kind: 'lemma', objective: 'Prove the premise', dependsOn: [],
        revision: 0, proofPath: 'Submission.lean', theoremName: 'Submission.premise', type: 'True' };
      const task: CooperativeTask = { id: 'consumer', kind: 'lemma', objective: 'Check the conditional consumer',
        dependsOn: ['premise'], revision: 0, proofPath: 'Submission.lean', theoremName: 'Submission.consumer',
        type: 'True', conditional: true };
      const projected = createTaskSourceProjector(problem, workspace, commit)(task, [], [dependency]).get('Submission.lean')!;
      expect(projected).not.toContain('def wrapper');
      expect(projected).not.toContain('noncomputable');
      expect(projected).toContain('\ntheorem helper : True := by trivial\n');
      expect(projected).toContain('theorem consumer (premise : True) : True := helper');
      expect(projected).not.toContain('lemma premise');
      expect(fs.readFileSync(file, 'utf8')).toBe(source);
    });

  it('retains added Mathlib imports when checking and merging a helper proof', async () => {
    configureCooperation();
    const task = planTasks()[0], module = 'Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv';
    const assignment = { taskId: task.id, taskDigest: taskVersion(task), workerId: 'researcher', seedCommit: problem.baseCommit };
    fs.writeFileSync(path.join(project, 'Submission.lean'), `import ${module}\n` +
      original.replace('theorem first', 'lemma a : True := by trivial\ntheorem first'));
    const commit = commitSolverSources(problem, workspace);
    const proof = await checkTaskProof(problem, workspace, commit, task, assignment, [], {}, new AbortController().signal);
    expect(proof.passed).toBe(true);
    expect(proof.imports).toEqual([{ file: 'Submission.lean', module }]);
    await withSolverWorktree(workspace, problem.baseCommit, async checkout => {
      const file = path.join(checkout, problem.projectRelative, 'Submission.lean');
      fs.writeFileSync(file, original.replace('theorem first', 'lemma peer : True := by trivial\ntheorem first'));
      applyTaskChanges(problem, checkout, proof.changes, proof.imports);
      const source = fs.readFileSync(file, 'utf8');
      expect(source).toContain(`import ${module}`);
      expect(source).toContain('lemma a : True := by trivial');
      expect(source).toContain('lemma peer : True := by trivial');
      expect(source).toContain('theorem first : True := by sorry');
      applyTaskChanges(problem, checkout, proof.changes, proof.imports);
      expect(fs.readFileSync(file, 'utf8')).toBe(source);
    });
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
    const bothStarted = deferred();
    const checking = new Set<string>();
    const bothChecking = deferred();
    const checkTask = async (...inputs: Parameters<typeof directSolverModules.M2.checkTask>) => {
      const task = inputs[3];
      if (task.kind === 'lemma' && !checking.has(task.id)) {
        checking.add(task.id);
        if (checking.size === 2) bothChecking.resolve();
        await bothChecking.promise;
      }
      return directSolverModules.M2.checkTask(...inputs);
    };
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') { writePlan(options.workspace, waitingPlanTasks()); return 'completed'; }
      if (action.kind === 'task' && action.task.kind === 'lemma') {
        expect(fs.readFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), 'utf8')).toBe(original);
        if (++started === 2) bothStarted.resolve();
        await bothStarted.promise;
      }
      finishAssignment(action, options); return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '6'], directory,
      { ...directSolverModules, M2: { ...directSolverModules.M2, checkTask } })).toBe(0);
    expect(started).toBe(2);
    expect(checking.size).toBe(2);
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

  it('discards a proof superseded by an edit while its independent check is running', async () => {
    configureCooperation(undefined, waitingPlanTasks);
    let edited = false;
    const checkTask = async (...inputs: Parameters<typeof directSolverModules.M2.checkTask>) => {
      const proof = await directSolverModules.M2.checkTask(...inputs);
      if (inputs[3].id === 'a' && !edited) {
        edited = true;
        const journal = JSON.parse(fs.readFileSync(path.join(inputs[1], 'COOPERATION.json'), 'utf8'));
        fs.appendFileSync(path.join(`${output}.runtime`, 'edits.jsonl'), JSON.stringify({
          id: 'during-check', baseVersion: journal.planVersion,
          tasks: waitingPlanTasks().map(task => task.id === 'a' ? { ...task, revision: 1 } : task),
        }) + '\n');
        await vi.waitFor(() => expect(cooperationState().edits?.some((edit: any) =>
          edit.id === 'during-check' && edit.status === 'applied')).toBe(true));
      }
      return proof;
    };
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '8'], directory,
      { ...directSolverModules, M2: { ...directSolverModules.M2, checkTask } })).toBe(0);
    const state = cooperationState();
    expect(state.deliveries.some((delivery: any) => delivery.taskId === 'a' && delivery.status === 'superseded')).toBe(true);
    expect(state.tasks.find((node: any) => node.task.id === 'a')).toMatchObject({ task: { revision: 1 }, status: 'integrated' });
  });

  it('does not accept checked partial proofs as a solution and rechecks integrated evidence on resume', async () => {
    configureCooperation(undefined, waitingPlanTasks);
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
    const sessions = host.createSession.mock.calls.length;
    expect(await runSolver([...parallelArgs, '--resume', '--max-turns', '6'], directory)).toBe(0);
    expect(host.verify.mock.calls[checks][0].items.map(item => item.theoremName)).toEqual(['Submission.a', 'Submission.b']);
    expect(host.verify.mock.calls[checks][1].expectedDeclarationTypes).toEqual({ 'Submission.a': 'True', 'Submission.b': 'True' });
    for (const [options] of host.createSession.mock.calls.slice(sessions)) expect(options.threadId).toBe(
      options.environment.DEEPSCIENTIST_MATH_WORKER_ID === 'solver' ? 'thread-solver' : undefined);
    expect(host.officialGate).toHaveBeenCalledOnce();
  });

  it('keeps per-target receipts and closed types when batching identical proof projections', async () => {
    fs.writeFileSync(path.join(project, 'Submission.lean'), original.replace('theorem first',
      'lemma a : True := by trivial\nlemma b : True → True := by intro h; exact h\ntheorem first'));
    const commit = commitSolverSources(problem, workspace);
    const tasks = planTasks().slice(0, 2).map(task => task.id === 'b' ? { ...task, type: 'True → True' } : task);
    const proofs = await checkTaskProofs(problem, workspace, commit, tasks.map(task => ({ task, retainedGoals: [],
      assignment: { taskId: task.id, taskDigest: taskVersion(task), workerId: 'solver', seedCommit: commit } })),
      {}, new AbortController().signal);
    expect(host.verify).toHaveBeenCalledOnce();
    expect(host.verify.mock.calls[0][1].expectedDeclarationTypes).toEqual({ 'Submission.a': 'True', 'Submission.b': 'True → True' });
    expect(proofs.map(proof => ({ passed: proof.passed, taskDigest: proof.taskDigest,
      targets: proof.verification.results.map(result => result.theoremName) }))).toEqual(tasks.map(task => ({
        passed: true, taskDigest: taskVersion(task), targets: [task.theoremName] })));
  });

  it('rejects batching different source projections before invoking Lean', async () => {
    fs.writeFileSync(path.join(project, 'Submission.lean'), original.replaceAll('by sorry', 'by trivial')
      .replace('theorem first', 'lemma a : True := by trivial\ntheorem first'));
    const commit = commitSolverSources(problem, workspace);
    const tasks = [planTasks()[0], planTasks()[2]];
    await expect(checkTaskProofs(problem, workspace, commit, tasks.map(task => ({ task, retainedGoals: [],
      assignment: { taskId: task.id, taskDigest: taskVersion(task), workerId: 'solver', seedCommit: commit } })),
      {}, new AbortController().signal)).rejects.toThrow('math_task_batch_projection_mismatch');
    expect(host.verify).not.toHaveBeenCalled();
  });

  it('preserves restoration progress after an opaque batch failure without expanding verifier retries', async () => {
    configureCooperation(undefined, waitingPlanTasks);
    const parallelArgs = [...args, '--workers', '4', '--max-turns', '3'];
    expect(await runSolver(parallelArgs, directory)).toBe(4);
    const verify = host.verify.getMockImplementation()!;
    const progress: number[] = [];
    host.verify.mockImplementation(async (request, options) => {
      const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
      progress.push(state.cooperation.recheck?.completed ?? -1);
      const result = await verify(request, options);
      return request.items.length > 1 && request.items[0].theoremName === 'Submission.a' ? failed(result) : result;
    });
    const before = host.verify.mock.calls.length, sessions = host.createSession.mock.calls.length;
    expect(await runSolver([...parallelArgs, '--resume', '--max-turns', '6'], directory)).toBe(1);
    expect(host.verify.mock.calls.slice(before).map(([request]) => request.items.map(item => item.theoremName)))
      .toEqual([['Submission.a', 'Submission.b']]);
    expect(progress).toEqual([0]);
    expect(cooperationState().tasks.slice(0, 2).map((node: TaskRecord) => node.status)).toEqual(['integrated', 'integrated']);
    expect(cooperationState().recheck.completed).toBe(0);
    expect(host.createSession).toHaveBeenCalledTimes(sessions);
    expect(host.officialGate).not.toHaveBeenCalled();
    host.verify.mockImplementation(verify);
    expect(await runSolver([...parallelArgs, '--resume', '--max-turns', '6'], directory)).toBe(0);
    expect(host.officialGate).toHaveBeenCalledOnce();
  });

  it.each(['partial', 'shared-source', 'infrastructure'])('retains attributable results after a %s restoration batch without individual recompilation', async mode => {
    configureCooperation(undefined, waitingPlanTasks);
    const parallelArgs = [...args, '--workers', '4', '--max-turns', '3'];
    expect(await runSolver(parallelArgs, directory)).toBe(4);
    const before = host.verify.mock.calls.length, sessions = host.createSession.mock.calls.length;
    host.verify.mockImplementation(async (request: MathematicsVerifierBatchRequest) => {
      const batch = verified(request);
      if (request.items.length === 2) {
        batch.status = 'failed';
        for (const [index, result] of batch.results.entries()) if (index === 1 || mode !== 'partial')
          Object.assign(result, mode === 'infrastructure' && index === 1 ? { status: 'unavailable', error: 'Lean is unavailable.' } :
            { status: 'failed', error: 'Lean exited with status 1.', stdoutPreview: 'Submission.lean:3:1: error: unsolved goals' });
      }
      return batch;
    });
    expect(await runSolver([...parallelArgs, '--resume'], directory)).toBe(mode === 'infrastructure' ? 1 : 4);
    expect(host.verify.mock.calls.slice(before).map(([request]) => request.items.map(item => item.theoremName)))
      .toEqual([['Submission.a', 'Submission.b']]);
    expect(host.createSession).toHaveBeenCalledTimes(sessions);
    const saved = cooperationState();
    expect(saved.tasks.slice(0, 2).map((node: TaskRecord) => node.status)).toEqual(mode === 'partial' ? ['integrated', 'blocked'] :
      mode === 'shared-source' ? ['blocked', 'blocked'] : ['integrated', 'integrated']);
    expect(saved.recheck.completed).toBe(mode === 'infrastructure' ? 0 : 2);
    expect(host.officialGate).not.toHaveBeenCalled();
  });

  it('keeps restored proof receipts reachable through evidence refs', async () => {
    configureCooperation(undefined, waitingPlanTasks);
    const parallelArgs = [...args, '--workers', '4', '--max-turns', '3'];
    expect(await runSolver(parallelArgs, directory)).toBe(4);
    const before = cooperationState().tasks[0].integratedCheck.verification.targetCommit;
    const sessions = host.createSession.mock.calls.length;
    expect(await runSolver([...parallelArgs, '--resume'], directory)).toBe(4);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    const proofs = state.cooperation.tasks.slice(0, 2).map((node: any) => node.integratedCheck);
    expect(proofs[0].verification.targetCommit).not.toBe(before);
    for (const proof of proofs) for (const commit of [proof.commit, proof.verification.targetCommit])
      expect(git(state.worktree, ['rev-parse', `refs/math/${state.runId}/evidence/${commit}`])).toBe(commit);
    expect(state.cooperation.recheck).toMatchObject({ total: 2, completed: 2 });
    expect(host.createSession).toHaveBeenCalledTimes(sessions);
    expect(host.officialGate).not.toHaveBeenCalled();
  });

  it.each(['batch', 'individual'].flatMap(phase => ['reject', 'return'].map(settlement => ({ phase, settlement }))))
  ('preserves integrated proofs and unfinished progress when cancelling a restored $phase check ($settlement)', async ({ phase, settlement }) => {
    configureCooperation(undefined, waitingPlanTasks);
    const modules = phase === 'individual' ? { ...directSolverModules, M2: { ...directSolverModules.M2,
      version: directSolverModules.M2.version + '/individual-recovery-fixture',
      checkTask: (...input: Parameters<typeof checkTaskProof>) => checkTaskProof(...input) } } : directSolverModules;
    const parallelArgs = [...args, '--workers', '4', '--max-turns', '3'];
    expect(await runSolver(parallelArgs, directory, modules)).toBe(4);
    const before = cooperationState(), sessions = host.createSession.mock.calls.length;
    const verify = host.verify.getMockImplementation()!;
    host.verify.mockImplementation(async (request, options) => {
      if (request.items.length > 1 && request.items[0].theoremName === 'Submission.a') {
        if (phase === 'batch') {
          process.emit('SIGTERM');
          if (settlement === 'reject') options.signal.throwIfAborted();
        }
        const result = await verify(request, options);
        return failed(result);
      }
      if (phase === 'individual' && request.items[0].theoremName === 'Submission.b') {
        process.emit('SIGTERM');
        if (settlement === 'reject') options.signal.throwIfAborted();
        const result = await verify(request, options);
        return failed(result);
      }
      return verify(request, options);
    });
    expect(await runSolver([...parallelArgs, '--resume', '--max-turns', '6'], directory, modules)).toBe(4);
    const interrupted = cooperationState(), taskId = phase === 'batch' ? 'a' : 'b';
    expect(interrupted.tasks.slice(0, 2).map((node: any) => node.status)).toEqual(['integrated', 'integrated']);
    for (const node of interrupted.tasks.slice(0, 2)) {
      const previous = before.tasks.find((item: any) => item.task.id === node.task.id);
      expect(node.proof).toEqual(previous.proof);
      expect(node.feedback).toBe(previous.feedback);
      if (phase === 'batch' || node.task.id === 'b') expect(node.integratedCheck).toEqual(previous.integratedCheck);
    }
    expect(interrupted.recheck).toMatchObject({ total: 2, completed: phase === 'batch' ? 0 : 1, taskId });
    expect(host.createSession).toHaveBeenCalledTimes(sessions);
    expect(host.officialGate).not.toHaveBeenCalled();

    host.verify.mockImplementation(verify);
    const checks = host.verify.mock.calls.length;
    expect(await runSolver([...parallelArgs, '--resume', '--max-turns', '6'], directory, modules)).toBe(0);
    expect(host.verify.mock.calls[checks][0].items.map(item => item.theoremName))
      .toEqual(phase === 'batch' ? ['Submission.a', 'Submission.b'] : ['Submission.a']);
    expect(cooperationState().tasks.map((node: any) => node.attempts)).toEqual([1, 1, 1, 1]);
    expect(host.officialGate).toHaveBeenCalledOnce();
  });

  it('keeps cooperative partial checks unlimited when the total solving limit is disabled', async () => {
    configureCooperation();
    const exitCode = await runSolver([...args, '--workers', '4', '--max-turns', '0', '--max-run-seconds', '0'], directory);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(exitCode, JSON.stringify({ result: JSON.parse(fs.readFileSync(output, 'utf8')),
      tasks: state.cooperation.tasks.map((node: any) => ({ id: node.task.id, status: node.status, feedback: node.feedback })),
      workers: state.workers.map((worker: any) => ({ id: worker.id, error: worker.error })),
      events: vi.mocked(console.log).mock.calls.map(([event]) => JSON.parse(event))
        .filter(event => /error|failed|blocked|idle/u.test(event.event)) }, null, 2)).toBe(0);
    const partialChecks = host.verify.mock.calls.filter(([request]) => request.items.length === 1);
    expect(partialChecks).toHaveLength(6);
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
      if (action.kind === 'lead') writePlan(options.workspace, groupedTasks().map(task =>
        task.kind === 'goal' ? { ...task, conditional: false } : task), routeGroups());
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
      if (action.kind === 'lead') writePlan(options.workspace, waitingPlanTasks(), groups);
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
    writePlan(state.worktree, waitingPlanTasks(), [{ ...groups[0], maxTurns: 4 }]);
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

  it.each([false, true])('proves ready original goals concurrently with idle Researchers (explicit owner: %s)', async pinned => {
    const tasks = planTasks().slice(2).map((task, index) => ({ ...task, dependsOn: [],
      ...(pinned ? { ownerId: index === 0 ? 'researcher-1' : 'engineer' } : {}) }));
    const assignments: { taskId: string; workerId: string }[] = [];
    const bothStarted = deferred();
    configureCooperation(async (action, options, message) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'task') {
        expect(action.task.kind).toBe('goal');
        expect(message).toContain('Your role: engineer');
        assignments.push({ taskId: action.task.id, workerId: action.assignment.workerId });
        if (assignments.length === 2) bothStarted.resolve();
        await bothStarted.promise;
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace(
          `${action.task.id} : True := by sorry`, `${action.task.id} : True := by trivial`));
      } else finishAssignment(action, options);
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '4'], directory)).toBe(0);
    expect(assignments).toHaveLength(2);
    expect(new Set(assignments.map(item => item.workerId)).size).toBe(2);
    expect(assignments.some(item => item.workerId.startsWith('researcher-'))).toBe(true);
    if (pinned) expect(assignments).toEqual(expect.arrayContaining([
      { taskId: 'first', workerId: 'researcher-1' }, { taskId: 'second', workerId: 'engineer' },
    ]));
    expect(cooperationState().tasks.every((node: any) => node.status === 'integrated')).toBe(true);
    expect(host.officialGate).toHaveBeenCalledOnce();
  });

  it('lets the Engineer prove an independent goal while both Researchers work on helpers', async () => {
    let started = 0;
    const threeStarted = deferred();
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') {
        writePlan(options.workspace, planTasks().map(task => task.id === 'second' ? { ...task, dependsOn: [] } : task));
      } else if (action.kind === 'task' && action.task.id !== 'first') {
        if (++started === 3) threeStarted.resolve();
        await threeStarted.promise;
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

  it('shares blocking helpers concurrently across all three proof workers with critical-path scheduling', async () => {
    const tasks = planTasks();
    tasks.splice(2, 0, { ...tasks[0], id: 'c', theoremName: 'Submission.c' });
    tasks[3] = { ...tasks[3], dependsOn: ['a', 'b', 'c'] };
    const assignments: { taskId: string; workerId: string; worktree: string }[] = [];
    const threeStarted = deferred();
    configureCooperation(async (action, options, message) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else {
        if (action.kind === 'task' && action.task.kind === 'lemma') {
          expect(message).toContain('Your role: researcher');
          assignments.push({ taskId: action.task.id, workerId: action.assignment.workerId, worktree: options.workspace });
          if (assignments.length === 3) threeStarted.resolve();
          await threeStarted.promise;
        }
        finishAssignment(action, options);
      }
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--scheduler', 'critical-path', '--max-turns', '7'], directory)).toBe(0);
    expect(assignments).toHaveLength(3);
    expect(new Set(assignments.map(item => item.taskId)).size).toBe(3);
    expect(new Set(assignments.map(item => item.workerId)).size).toBe(3);
    expect(new Set(assignments.map(item => item.worktree)).size).toBe(3);
    expect(assignments.some(item => item.workerId === 'engineer')).toBe(true);
    expect(cooperationState().tasks.every((record: any) => record.status === 'integrated')).toBe(true);
    expect(host.officialGate).toHaveBeenCalledOnce();
  });

  it('applies a local mathematical task revision on resume, invalidates consumers and keeps unrelated checked work', async () => {
    configureCooperation(undefined, waitingPlanTasks);
    const parallelArgs = [...args, '--workers', '4', '--max-turns', '3'];
    expect(await runSolver(parallelArgs, directory)).toBe(4);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    writePlan(state.worktree, waitingPlanTasks().map(task => task.id === 'a'
      ? { ...task, revision: 1, premises: ['Revised mathematical premise'] } : task));
    expect(await runSolver([...parallelArgs, '--resume', '--max-turns', '7'], directory)).toBe(0);
    const resumed = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(resumed.cooperation.tasks.slice(0, 2).map(node => node.attempts)).toEqual([2, 1]);
    expect(resumed.cooperation.history.map(node => node.task.id)).toEqual(['a', 'first', 'second']);
    expect(resumed.cooperation.tasks[0].task.revision).toBe(1);
  });

  it('rechecks modified canonical helpers and prevents consumers from using invalid evidence on resume', async () => {
    configureCooperation(undefined, waitingPlanTasks);
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

  it.each(['missing', 'lean', 'sorry'].flatMap(failure => [false, true].map(repaired => ({ failure, repaired }))))
  ('allows one local task repair before Lead escalation ($failure, repaired: $repaired)', async ({ failure, repaired }) => {
    let leadTurns = 0, helperTurns = 0;
    let firstAssignment: Extract<CooperativeAction, { kind: 'task' }>['assignment'] | undefined;
    let firstWorkspace: string | undefined;
    configureCooperation(async (action, options, message) => {
      if (action.kind === 'lead') {
        leadTurns++;
        finishAssignment(action, options);
        if (action.recovery) fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify({
          tasks: cooperationState().tasks.map((node: TaskRecord) => node.task),
          groups: cooperationState().groups.map((route: RouteRecord) => route.group),
          recovery: { status: 'awaiting-input', reason: 'The repeated failed helper needs a distinct construction.' },
        }) + '\n```');
      } else if (action.kind === 'task' && action.task.id === 'a') {
        helperTurns++;
        if (firstAssignment) {
          expect(action.assignment).toEqual(firstAssignment);
          expect(options.workspace).toBe(firstWorkspace);
          expect(message).toContain(failure === 'missing' ? 'math_task_missing_declaration' :
            failure === 'sorry' ? 'Proof source contains sorry or admit.' : 'Unknown identifier LOCAL_REPAIR_GAP');
        } else { firstAssignment = { ...action.assignment }; firstWorkspace = options.workspace; }
        if (helperTurns === 1 || !repaired) {
          if (failure !== 'missing' && helperTurns === 1) {
            const file = path.join(options.workspace, 'generated/p/Submission.lean');
            const source = fs.readFileSync(file, 'utf8');
            fs.writeFileSync(file, source.replace('theorem first',
              `lemma a : True := by ${failure === 'sorry' ? 'sorry' : 'exact LOCAL_REPAIR_GAP'}\ntheorem first`));
          }
        } else {
          const file = path.join(options.workspace, 'generated/p/Submission.lean');
          fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('by exact LOCAL_REPAIR_GAP', 'by trivial'));
          finishAssignment(action, options);
        }
      } else finishAssignment(action, options);
      return 'completed';
    });
    const verify = host.verify.getMockImplementation()!;
    host.verify.mockImplementation(async (request, options) => {
      const source = fs.readFileSync(path.join(request.projectRoot, 'Submission.lean'), 'utf8');
      if (source.includes('LOCAL_REPAIR_GAP') || /lemma a : True := by sorry/u.test(source)) {
        const checked = verified(request);
        return failed(checked, { error: failure === 'sorry' ? 'Proof source contains sorry or admit.' : 'Lean exited with status 1.',
          sorryCount: failure === 'sorry' ? 1 : 0,
          stderrPreview: failure === 'lean' ? 'Submission.lean:3:1: error: Unknown identifier LOCAL_REPAIR_GAP' : undefined });
      }
      return verify(request, options);
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '8'], directory)).toBe(repaired ? 0 : 4);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(helperTurns).toBe(2);
    expect(leadTurns).toBe(repaired ? 1 : 3);
    expect(state.turns).toBeLessThanOrEqual(8);
    expect(state.cooperation.tasks[0]).toMatchObject({ attempts: 2, status: repaired ? 'integrated' : 'blocked' });
    if (!repaired) {
      expect(host.officialGate).not.toHaveBeenCalled();
      expect(state.cooperation.frontierRecoveries).toEqual([expect.objectContaining({
        taskIds: ['a'], status: 'awaiting-input', reason: 'The repeated failed helper needs a distinct construction.',
      })]);
    }
  });

  it.each([false, true])('keeps an unchanged rejected helper blocked after a Lead decision (revision: %s)', async revise => {
    let leadTurns = 0, helperTurns = 0;
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') {
        const tasks = planTasks().filter(task => task.id !== 'b')
          .map(task => task.id === 'first' ? { ...task, dependsOn: ['a'] } : task);
        if (++leadTurns > 1) {
          expect(cooperationState().tasks[0].status).toBe('blocked');
          if (revise) tasks[0] = { ...tasks[0], revision: 1 };
        }
        writePlan(options.workspace, tasks);
        if (action.recovery) fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify({
          tasks, recovery: { status: 'awaiting-input', reason: 'The same failed declaration needs a new proof, not another revision.' },
        }) + '\n```');
      } else if (action.kind === 'task' && action.task.id === 'a') {
        if (++helperTurns === 1) fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'),
          original.replace('theorem first', 'lemma a : False := by trivial\ntheorem first'));
      } else finishAssignment(action, options);
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '8'], directory)).toBe(4);
    expect(leadTurns).toBeGreaterThanOrEqual(2);
    expect(helperTurns).toBe(2);
    expect(cooperationState().tasks[0]).toMatchObject({ status: 'blocked', task: { revision: revise ? 1 : 0, type: 'True' } });
    expect(cooperationState().failedTaskInputs).toHaveLength(1);
    expect(cooperationState().frontierRecoveries).toEqual([expect.objectContaining({ status: 'awaiting-input' })]);
    expect(host.officialGate).not.toHaveBeenCalled();
  });

  it.each([false, true])('reopens a rejected helper only after its saved proof changes (changed: %s)', async changed => {
    let leadTurns = 0, helperTurns = 0;
    let draftWorktree: string | undefined, savedProofChanged = false;
    configureCooperation(async (action, options, message) => {
      if (action.kind === 'lead') {
        const tasks = planTasks().filter(task => task.id !== 'b')
          .map(task => task.id === 'first' ? { ...task, dependsOn: ['a'] } : task);
        if (++leadTurns > 1) {
          expect(message).toContain('task type mismatch');
          if (changed && !savedProofChanged) {
            if (!draftWorktree) throw new Error('missing_saved_helper_draft');
            const file = path.join(draftWorktree, 'generated/p/Submission.lean');
            fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('lemma a : False := by trivial', 'lemma a : True := by trivial'));
            commitSolverSources(problem, draftWorktree); savedProofChanged = true;
          }
        }
        writePlan(options.workspace, tasks);
        if (action.recovery) fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify({
          tasks, recovery: { status: 'awaiting-input', reason: 'The unchanged rejected helper still needs a new saved proof.' },
        }) + '\n```');
      } else if (action.kind === 'task' && action.task.id === 'a') {
        draftWorktree = options.workspace;
        if (++helperTurns === 1) fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'),
          original.replace('theorem first', 'lemma a : False := by trivial\ntheorem first'));
      } else if (action.kind === 'task' && action.task.id === 'first') {
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('first : True := by sorry', 'first : True := by exact a'));
      } else finishAssignment(action, options);
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '12'], directory)).toBe(changed ? 0 : 4);
    expect(helperTurns).toBe(changed ? 3 : 2);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.cooperation.tasks[0]).toMatchObject({ status: changed ? 'integrated' : 'blocked', task: { revision: 0, type: 'True' } });
    expect(host.verify.mock.calls.filter(([, options]) => options.expectedDeclarationType).length).toBeGreaterThan(0);
    expect(host.verify.mock.calls.filter(([, options]) => options.expectedDeclarationType)
      .every(([, options]) => options.expectedDeclarationType === 'True')).toBe(true);
    expect(host.officialGate).toHaveBeenCalledTimes(changed ? 1 : 0);
  });

  it.each(['cycle', 'missing', 'duplicate', 'coverage', 'target'])('rejects a %s plan before dispatch', flaw => {
    const tasks = planTasks();
    if (flaw === 'cycle') tasks[0] = { ...tasks[0], dependsOn: ['first'] };
    if (flaw === 'missing') tasks[0] = { ...tasks[0], dependsOn: ['unknown'] };
    if (flaw === 'duplicate') tasks.push({ ...tasks[2], id: 'duplicate' });
    if (flaw === 'coverage') tasks.pop();
    if (flaw === 'target') tasks[2] = { ...tasks[2], theoremName: 'Submission.changed' };
    writePlan(workspace, tasks);
    expect(() => readCooperationPlan(problem, workspace)).toThrow(/math_plan/u);
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
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.dispatchCounts).toEqual({ planning: 1, research: 1, proof: 2, review: 1 });
    expect(host.verify.mock.calls.some(([request]) => request.items.some(item => item.theoremName === 'route'))).toBe(false);
  });

  it('uses fresh reviewer sessions for early checks of different inputs after ordinary research', async () => {
    const warmup: CooperativeTask = { id: 'warmup', kind: 'research', ownerId: 'researcher-1',
      objective: 'Locate the doubtful core estimates.', dependsOn: [], revision: 0 };
    const checks: CooperativeTask[] = ['a', 'b'].map(id => ({ id: `check_${id}`, kind: 'research',
      objective: `Independently test the proposed input ${id}.`, dependsOn: [id], revision: 0,
      reviewScope: 'feasibility', ownerId: 'researcher-1', status: 'paused' }));
    const proofs = planTasks().map(task => ({ ...task, status: 'paused' as const,
      ...(task.kind === 'lemma' ? { ownerId: 'researcher-2' } : {}) }));
    let plans = 0;
    const reviewed: string[] = [];
    configureCooperation(async (action, options, message) => {
      if (action.kind === 'lead') {
        plans++;
        fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify({
          tasks: [warmup, ...proofs, ...checks.map(task => ({ ...task,
            status: plans > 1 ? 'active' as const : 'paused' as const }))],
          challengeDecisions: action.challengeIds?.map(id => ({ id, status: 'revised',
            reason: 'Activate check_a and check_b as distinct independent feasibility reviews of the two requested inputs.' })),
        }) + '\n```');
      } else if (action.kind === 'task' && action.task.id === warmup.id) {
        fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), JSON.stringify({
          summary: 'The inputs a and b need distinct feasibility checks.', conclusion: 'inconclusive', needsDecision: true }));
      } else if (action.kind === 'task' && action.task.reviewScope === 'feasibility') {
        reviewed.push(action.task.id);
        expect(action.assignment.workerId).toBe('researcher-1');
        expect(message).toContain('Your role: reviewer');
        expect(message).toContain('"stage":"feasibility-review"');
        expect(message).toContain('"acceptance":"advisory-only"');
        fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), JSON.stringify({
          summary: `The input ${action.task.dependsOn[0]} still requires a substantive proof.`, conclusion: 'inconclusive' }));
      } else throw new Error('unexpected_early_review_fixture_assignment');
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '5'], directory)).toBe(4);
    expect(plans).toBe(2);
    expect(reviewed).toEqual(['check_a', 'check_b']);
    const openings = host.createSession.mock.calls.map(([options]) => options as MathAgentOptions)
      .filter(options => options.environment?.DEEPSCIENTIST_MATH_WORKER_ID === 'researcher-1');
    expect(openings).toHaveLength(3);
    expect(openings.map(options => options.threadId)).toEqual([undefined, undefined, undefined]);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.workers.find((worker: any) => worker.id === 'researcher-1'))
      .toMatchObject({ sessionRole: 'reviewer', sessionTaskId: 'check_b', previousThreadIds: [expect.any(String), expect.any(String)] });
    expect(state.cooperation.tasks.filter((node: TaskRecord) => node.task.reviewScope === 'feasibility')
      .every((node: TaskRecord) => node.status === 'completed' && !node.integratedCheck)).toBe(true);
    expect(fs.readFileSync(path.join(state.worktree, 'generated/p/Submission.lean'), 'utf8')).toBe(original);
    expect(host.officialGate).not.toHaveBeenCalled();
  });

  it.each(['checkpoint', 'replacement', 'legacy'] as const)
  ('restores early review sessions by assignment identity (%s)', async mode => {
    const task: CooperativeTask = { id: 'route_check', kind: 'research', reviewScope: 'feasibility',
      objective: 'Independently test the doubtful core input.', dependsOn: ['a'], revision: 0, ownerId: 'researcher-1' };
    const tasks = [...planTasks().map(task => ({ ...task, status: 'paused' as const,
      ...(task.kind === 'lemma' ? { ownerId: 'researcher-2' } : {}) })), task];
    const assignments: string[] = [];
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'task' && action.task.id === task.id) {
        assignments.push(action.assignment.assignmentId ?? 'legacy');
        fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), JSON.stringify({
          summary: `Discriminating evidence checkpoint ${assignments.length}.`, conclusion: 'inconclusive' }));
        return assignments.length < 3 ? 'checkpoint' : 'completed';
      } else throw new Error('unexpected_review_identity_fixture_assignment');
      return 'completed';
    });
    const parallelArgs = [...args, '--workers', '4'];
    expect(await runSolver([...parallelArgs, '--max-turns', '2'], directory)).toBe(4);
    const stateFile = `${output}.runtime/state.json`;
    const before = readSolverRunState(stateFile);
    const reviewer = before.workers!.find(worker => worker.id === 'researcher-1')!;
    const node = before.cooperation!.tasks.find(node => node.task.id === task.id)!;
    expect(reviewer.sessionAssignmentId).toBe(node.assignment!.assignmentId);
    if (mode === 'replacement') node.assignment!.assignmentId = 'replacement-review-assignment';
    if (mode === 'legacy') {
      delete node.assignment!.assignmentId;
      delete reviewer.sessionAssignmentId;
    }
    fs.writeFileSync(stateFile, JSON.stringify(before));
    expect(await runSolver([...parallelArgs, '--resume', '--max-turns', '3'], directory)).toBe(4);
    const resumed = readSolverRunState(stateFile);
    expect(resumed.workers!.find(worker => worker.id === reviewer.id)!.sessionAssignmentId)
      .toBe(node.assignment!.assignmentId ?? `legacy-task:${node.assignment!.seedCommit}`);
    expect(await runSolver([...parallelArgs, '--resume', '--max-turns', '4'], directory)).toBe(4);
    const openings = host.createSession.mock.calls.map(([options]) => options as MathAgentOptions)
      .filter(options => options.environment?.DEEPSCIENTIST_MATH_WORKER_ID === reviewer.id);
    expect(openings.map(options => options.threadId))
      .toEqual([undefined, mode === 'checkpoint' ? reviewer.threadId : undefined, reviewer.threadId]);
    expect(assignments).toEqual([assignments[0], mode === 'checkpoint' ? assignments[0] :
      mode === 'legacy' ? 'legacy' : 'replacement-review-assignment', assignments[1]]);
    expect(cooperationState().tasks.find((node: TaskRecord) => node.task.id === task.id))
      .toMatchObject({ status: 'completed', attempts: 3 });
    expect(host.officialGate).not.toHaveBeenCalled();
  });

  it.each(['markdown', 'json'] as const)('passes a complete %s research argument to its proof consumers', async format => {
    const tasks: CooperativeTask[] = [{ id: 'route', kind: 'research', objective: 'Find the closing inference', dependsOn: [], revision: 0 },
      ...planTasks().slice(2).map(task => ({ ...task, dependsOn: ['route'] }))];
    const argument = 'A reusable mathematical argument. '.repeat(300) + 'EXACT_CLOSING_INFERENCE: use True.intro.';
    let consumers = 0;
    configureCooperation(async (action, options, message) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'task' && action.task.kind === 'research') {
        fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), format === 'markdown' ? argument :
          '```math-result\n' + JSON.stringify({ summary: 'A complete route is available.', argument, conclusion: 'supporting' }) + '\n```');
      } else if (action.kind === 'review') finishAssignment(action, options);
      else if (action.kind === 'task') {
        consumers++;
        expect(message).toContain('EXACT_CLOSING_INFERENCE');
        expect(message).toContain('"summarySource":"finding:route"');
        const finding = JSON.parse(message.split('Advisory finding for route:\n')[1].split('\n\n')[0]);
        const research = cooperationState().deliveries.find((item: any) => item.taskId === 'route' && item.kind === 'research');
        expect(finding.savedSource).toMatchObject({ deliveryId: research.id, commit: research.commit, notesPath: 'RESEARCH.md' });
        expect(research.findingDigest).toBe(mathDigest(finding.finding));
        expect(JSON.parse(finding.finding)[format === 'markdown' ? 'summary' : 'argument']).toBe(argument);
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace(`${action.task.id} : True := by sorry`,
          `${action.task.id} : True := by trivial`));
      }
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '6'], directory)).toBe(0);
    expect(consumers).toBe(2);
    const state = cooperationState(), finding = state.tasks.find((item: TaskRecord) => item.task.id === 'route');
    expect(finding.status).toBe('completed');
    expect(finding.integratedCheck).toBeUndefined();
    expect(finding.finding).toContain('EXACT_CLOSING_INFERENCE');
    const restored = readSolverRunState(`${output}.runtime/state.json`);
    expect(restored.dispatchCounts).toEqual({ planning: 1, research: 1, proof: 2, review: 1 });
    expect(restored.cooperation!.tasks.find(item => item.task.id === 'route')!.finding).toBe(finding.finding);
    const restoredDelivery = restored.cooperation!.deliveries!.find(item => item.taskId === 'route' && item.kind === 'research')!;
    expect(restoredDelivery.findingDigest).toBe(mathDigest(finding.finding));
    const restoredContext = directSolverModules.M4.build(problem, restored, { root: directory, worktree: restored.worktree,
      environment: {}, taskText: 'Prove both targets', retrievalRoot: project,
      assignment: { kind: 'lead', seedCommit: restored.cooperation!.canonicalCommit! } });
    expect(restoredContext.message).toContain('EXACT_CLOSING_INFERENCE');
    const restoredSource = JSON.parse(restoredContext.message.split('Advisory finding for route:\n')[1].split('\n\n')[0]).savedSource;
    expect(restoredSource).toMatchObject({ deliveryId: restoredDelivery.id, commit: restoredDelivery.commit, notesPath: 'RESEARCH.md' });
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
        if (action.kind === 'lead') { writePlan(options.workspace, waitingPlanTasks()); return 'completed'; }
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

  const cooperationState = () => JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8')).cooperation;
  const appendDelivery = (options: MathAgentOptions, action: Extract<CooperativeAction, { kind: 'task' }>, value: Record<string, unknown>) =>
    fs.appendFileSync(path.join(options.workspace, 'DELIVERIES.jsonl'), JSON.stringify({ taskId: action.task.id,
      taskDigest: action.assignment.taskDigest, evidenceRefs: [], ...value }) + '\n');

  const statementTasks = () => {
    const tasks = planTasks();
    tasks[0] = { ...tasks[0], statementReview: true, informalStatement: 'INTENT_SECRET: the proposition True holds.' };
    return tasks;
  };

  const configureStatementReferenceReports = () => {
    const prepare = host.prepare.getMockImplementation()!;
    host.prepare.mockImplementation(async input => {
      const result = await prepare(input);
      for (const file of input.files) if (/^StatementContext[0-9a-f]+\.lean$/u.test(file)) {
        const report = path.join(input.projectRoot, '.lake', file.replace('StatementContext', 'statement-context-').replace('.lean', '.json'));
        const contexts = JSON.parse(fs.readFileSync(report, 'utf8'));
        for (const context of contexts) Object.assign(context.context, { references: { statement: [], proof: [] } });
        fs.writeFileSync(report, JSON.stringify(contexts));
      }
      return result;
    });
  };

  it('accepts empty sandbox metadata directories throughout independent statement review', async () => {
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, statementTasks());
      else {
        if (isStatementAction(action)) for (const name of ['.git', '.codex', '.agents', '.aws'])
          fs.mkdirSync(path.join(options.workspace, name), { recursive: true });
        finishAssignment(action, options);
      }
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '8'], directory)).toBe(0);
    expect(cooperationState().statementReviews[0].status).toBe('accepted');
    expect(host.officialGate).toHaveBeenCalledOnce();
  });

  it.each(['disable', 'intent'])('updates review configuration without restarting checked proofs or active consumers (%s)', async change => {
    const tasks = statementTasks(); let translations = 0, edited = false;
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') { writePlan(options.workspace, tasks); return 'completed'; }
      if (action.kind === 'backtranslate') translations++;
      if (action.kind === 'task' && action.task.id === 'first' && !edited) {
        edited = true;
        await expect.poll(() => cooperationState().statementReviews[0].status).toBe('accepted');
        const before = cooperationState(), checked = before.tasks.find((node: any) => node.task.id === 'a').integratedCheck.commit;
        tasks[0] = { ...tasks[0], ...(change === 'disable'
          ? { statementReview: false, informalStatement: undefined }
          : { informalStatement: 'A revised interpretation of True.' }) };
        fs.appendFileSync(`${output}.runtime/edits.jsonl`, JSON.stringify({ id: 'review-policy', baseVersion: before.planVersion, tasks }) + '\n');
        await expect.poll(() => cooperationState().edits?.[0]?.status).toBe('applied');
        const after = cooperationState();
        expect(after.planVersion).not.toBe(before.planVersion);
        expect(after.edits[0].affectedTasks).toEqual([]);
        expect(after.tasks.find((node: any) => node.task.id === 'a')).toMatchObject({ status: 'integrated', integratedCheck: { commit: checked } });
        expect(after.tasks.find((node: any) => node.task.id === 'first')).toMatchObject({ status: 'running', assignment: action.assignment });
      }
      finishAssignment(action, options); return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '10'], directory)).toBe(0);
    const state = cooperationState();
    expect(edited).toBe(true);
    expect(state.tasks.map((node: any) => node.attempts)).toEqual([1, 1, 1, 1]);
    expect(state.deliveries.filter((record: any) => record.kind === 'proof' && record.status === 'superseded')).toEqual([]);
    expect(translations).toBe(change === 'disable' ? 1 : 2);
    expect(state.statementReviews.map((review: any) => review.status)).toEqual(change === 'disable' ? ['superseded'] : ['superseded', 'accepted']);
    expect(host.officialGate).toHaveBeenCalledOnce();
  });

  it.each(['nonempty-metadata', 'linked-metadata', 'unexpected-directory'])('rejects unsafe or unexpected statement snapshot entries (%s)', entry => {
    const task = statementTasks()[0], reviewWorkspace = path.join(directory, 'blind');
    const snapshot = statementSnapshot(problem, task, workspace, problem.baseCommit, 'fixed-env', []);
    const review = { workspace: reviewWorkspace, files: writeStatementSnapshot(reviewWorkspace, snapshot) } as any;
    if (entry === 'linked-metadata') fs.symlinkSync(path.join(reviewWorkspace, 'definitions'), path.join(reviewWorkspace, '.codex'));
    else {
      const extra = path.join(reviewWorkspace, entry === 'nonempty-metadata' ? '.codex' : 'extra');
      fs.mkdirSync(extra);
      if (entry === 'nonempty-metadata') fs.writeFileSync(path.join(extra, 'unexpected.txt'), 'Unexpected content');
    }
    expect(() => assertStatementSnapshot(review)).toThrow('math_statement_snapshot_changed');
  });

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
    tasks[1] = { ...tasks[1], dependsOn: ['a'] };
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

  it.each(['meaning-rejected', 'snapshot-tampered', 'statement-wrong-binding', 'statement-invalid-verdict', 'proof-wrong-binding', 'proof-invalid-verdict'])
  ('withholds final acceptance for %s', async failure => {
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
        if ((action.kind === 'statement-review' && failure.startsWith('statement-')) || (action.kind === 'review' && failure.startsWith('proof-')))
          fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), JSON.stringify({
            verdict: failure.endsWith('invalid-verdict') ? 'probably accepted' : 'accepted',
            ...(failure.endsWith('wrong-binding') ? action.kind === 'statement-review' ? { snapshotDigest: 'wrong-snapshot' } : { commit: 'wrong-commit' } : {}),
          }));
      }
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '12'], directory)).toBe(4);
    expect(failure.startsWith('proof-') ? cooperationState().review.status : cooperationState().statementReviews[0].status).toBe('changes_requested');
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
    tasks[1] = { ...tasks[1], dependsOn: ['a'] };
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
    const savedReview = cooperationState().statementReviews[0];
    expect(savedReview.status).toBe('translated'); expect(host.officialGate).not.toHaveBeenCalled();
    expect(translations).toBe(1); expect(comparisons).toBe(1);
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '9', '--resume'], directory)).toBe(0);
    expect(translations).toBe(1); expect(comparisons).toBe(2);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.cooperation.statementReviews).toMatchObject([{ id: savedReview.id, snapshotDigest: savedReview.snapshotDigest, status: 'accepted' }]);
    expect(state.turns).toBe(9); expect(state.usage).toMatchObject({ inputTokens: 9000, totalTokens: 10800 });
  });

  it('retries a disconnected statement review without rejecting its statement or repeating the translation', async () => {
    const tasks = statementTasks(); let translations = 0, comparisons = 0;
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') { writePlan(options.workspace, tasks); return 'completed'; }
      if (action.kind === 'backtranslate') translations++;
      if (action.kind === 'statement-review' && ++comparisons === 1) return 'failed';
      finishAssignment(action, options); return 'completed';
    });
    const create = host.createSession.getMockImplementation()!;
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ ...await create(options),
      lastError: 'stream disconnected before completion: error sending request' }));
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '10'], directory)).toBe(0);
    expect(translations).toBe(1); expect(comparisons).toBe(2);
    expect(host.delay).toHaveBeenCalledOnce();
    expect(cooperationState().statementReviews[0].status).toBe('accepted');
    expect(host.officialGate).toHaveBeenCalledOnce();
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

  it('uses fresh pending-type references to preserve review across an unrelated definition integration before proof evidence exists', async () => {
    const tasks = statementTasks(); let translations = 0;
    configureCooperation(async (action, options) => {
      const file = path.join(options.workspace, 'generated/p/Submission.lean');
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'task' && action.task.id === 'a') {
        const state = cooperationState();
        expect(state.statementReviews.find((review: any) => review.status === 'accepted')?.references)
          .toMatchObject({ scope: 'statement', statementType: 'True', statement: [] });
        expect(state.tasks.find((node: any) => node.task.id === 'a').integratedCheck).toBeUndefined();
        finishAssignment(action, options);
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('theorem first', 'def unrelated : Nat := 10\ntheorem first'));
      } else {
        if (action.kind === 'backtranslate') translations++;
        finishAssignment(action, options);
      }
      return 'completed';
    });
    configureStatementReferenceReports();
    const exit = await runSolver([...args, '--workers', '2', '--max-turns', '12'], directory);
    const details = JSON.stringify({ reviews: cooperationState().statementReviews.map((review: any) => ({ status: review.status,
      translated: !!review.translation, references: review.references, snapshotDigest: review.snapshotDigest })),
      tasks: cooperationState().tasks.map((node: any) => ({ id: node.task.id, status: node.status, feedback: node.feedback })) });
    expect(exit, details).toBe(0);
    expect(translations, details).toBe(1);
    expect(cooperationState().statementReviews.filter((review: any) => review.translation).map((review: any) => review.status))
      .toEqual(['accepted']);
  });

  it('revalidates serialized pending-type references instead of trusting a forged empty closure after resume', async () => {
    const tasks = statementTasks();
    tasks[1] = { ...tasks[1], status: 'paused' };
    let translations = 0;
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else {
        if (action.kind === 'backtranslate') translations++;
        finishAssignment(action, options);
      }
      return 'completed';
    });
    configureStatementReferenceReports();
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '3'], directory)).toBe(4);
    const stateFile = `${output}.runtime/state.json`, state = JSON.parse(fs.readFileSync(stateFile, 'utf8'));
    const worktree = state.workers[0].worktree, file = path.join(worktree, 'generated/p/Submission.lean');
    tasks[1] = { ...tasks[1], status: 'active' };
    state.cooperation.tasks.find((node: TaskRecord) => node.task.id === 'b').task = tasks[1];
    writePlan(worktree, tasks);
    const review = state.cooperation.statementReviews.find((review: any) => review.status === 'accepted');
    expect(review, JSON.stringify(state.cooperation.statementReviews.map((item: any) => ({ status: item.status, references: item.references })))).toBeDefined();
    fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('theorem first', 'def unrelated : Nat := 10\ntheorem first'));
    const commit = commitSolverSources(problem, worktree);
    state.cooperation.canonicalCommit = commit;
    review.references = captureProofReferences(problem, worktree, commit,
      { name: tasks[0].theoremName!, file: tasks[0].proofPath! }, { statement: [], proof: [] }, state.environmentDigest, 'statement', tasks[0].type);
    fs.writeFileSync(stateFile, JSON.stringify(state));
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '12', '--resume'], directory)).toBe(0);
    expect(translations).toBe(2);
    expect(cooperationState().statementReviews.filter((review: any) => review.translation).map((review: any) => review.status)).toEqual(['superseded', 'accepted']);
  });

  it.each(['description', 'type', 'intent', 'premises', 'dependency', 'dependency-description', 'dependency-revision', 'dependency-type', 'dependency-premises'])('reuses an accepted helper review only for an identical formal snapshot (%s)', async change => {
    const tasks = statementTasks();
    if (change.startsWith('dependency-')) tasks[0] = { ...tasks[0], dependsOn: ['b'] };
    let translations = 0, edited = false, reviewId = '';
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') { writePlan(options.workspace, tasks); return 'completed'; }
      if (action.kind === 'backtranslate') translations++;
      if (action.kind === 'task' && action.task.id === 'first' && !edited) {
        edited = true;
        const before = cooperationState();
        expect(before.statementReviews[0].status).toBe('accepted');
        reviewId = before.statementReviews[0].id;
        if (change.startsWith('dependency-')) tasks[1] = { ...tasks[1],
          ...(change === 'dependency-description' ? { objective: 'Explain the same supporting fact more clearly.' } :
            change === 'dependency-revision' ? { revision: 1 } : change === 'dependency-type' ? { type: 'And True True' } :
              { premises: ['An explicit revised dependency premise.'] }) };
        else tasks[0] = { ...tasks[0], revision: 1,
            ...(change === 'description' ? { objective: 'Use the established True interface in the original goal.' } :
              change === 'type' ? { type: 'And True True' } : change === 'intent' ? { informalStatement: 'A revised meaning.' } :
              change === 'premises' ? { premises: ['An explicit revised premise.'] } : { dependsOn: ['b'] }) };
        fs.appendFileSync(`${output}.runtime/edits.jsonl`, JSON.stringify({ id: 'helper-review-change', baseVersion: before.planVersion, tasks }) + '\n');
        await expect.poll(() => cooperationState().edits?.[0]?.status).toBe('applied');
      }
      finishAssignment(action, options); return 'completed';
    });
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '16'], directory)).toBe(0);
    const state = cooperationState(), reusable = ['description', 'dependency-description', 'dependency-revision'].includes(change);
    expect(edited).toBe(true);
    expect(translations).toBe(reusable ? 1 : 2);
    expect(state.statementReviews.map((review: any) => review.status)).toEqual(reusable ? ['accepted'] : ['superseded', 'accepted']);
    const accepted = state.statementReviews.find((review: any) => review.status === 'accepted');
    expect(accepted.taskDigest).toBe(taskVersion(tasks[0]));
    expect(accepted.dependencies.map((dependency: any) => dependency.taskId)).toEqual(tasks[0].dependsOn);
    if (change.startsWith('dependency-')) expect(accepted.dependencies).toEqual([{ taskId: 'b', taskDigest: taskVersion(tasks[1]) }]);
    expect(state.deliveries.filter((record: any) => record.kind === 'statement-review' && record.status === 'accepted'))
      .toContainEqual(expect.objectContaining({ taskDigest: taskVersion(tasks[0]), statementReviewId: accepted.id,
        dependencies: accepted.dependencies }));
    if (reusable) {
      expect(accepted.id).toBe(reviewId);
      expect(state.deliveries.filter((record: any) => record.statementReviewId === reviewId && record.status !== 'superseded')
        .every((record: any) => record.taskDigest === taskVersion(tasks[0]))).toBe(true);
    }
  });

  it.each(['schedule', 'dependency', 'intent', 'premises', 'imports'])('reuses the original statement review only when mathematics is unchanged (%s)', async change => {
    const tasks = planTasks();
    tasks[2] = { ...tasks[2], statementReview: true, informalStatement: 'The first target is True.' };
    let translations = 0, edited = false;
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') { writePlan(options.workspace, tasks); return 'completed'; }
      if (action.kind === 'backtranslate') translations++;
      if (action.kind === 'task' && action.task.id === 'first' && !edited) {
        edited = true;
        expect(cooperationState().statementReviews[0].status).toBe('accepted');
        if (change === 'imports') {
          finishAssignment(action, options);
          const file = path.join(options.workspace, problem.projectRelative, 'Submission.lean');
          fs.writeFileSync(file, 'import Mathlib.Data.Nat.Basic\n' + fs.readFileSync(file, 'utf8'));
          return 'completed';
        }
        if (change === 'dependency') tasks[0] = { ...tasks[0], revision: 1, objective: 'Try a different proof method' };
        else tasks[2] = { ...tasks[2], revision: 1,
          ...(change === 'schedule' ? { objective: 'Assemble the checked helper proofs', dependsOn: ['b', 'a'] } :
            change === 'intent' ? { informalStatement: 'The first target holds under revised meaning.' } : { premises: ['A revised premise'] }) };
        fs.appendFileSync(`${output}.runtime/edits.jsonl`, JSON.stringify({ id: 'review-change', baseVersion: cooperationState().planVersion, tasks }) + '\n');
        await expect.poll(() => cooperationState().edits?.[0]?.status).toBe('applied');
      }
      finishAssignment(action, options); return 'completed';
    });
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '12'], directory)).toBe(0);
    const state = cooperationState(), reusable = change === 'schedule' || change === 'dependency';
    expect(translations).toBe(reusable ? 1 : 2);
    expect(state.statementReviews.map((review: any) => review.status)).toEqual(reusable ? ['accepted'] : ['superseded', 'accepted']);
    expect(state.deliveries.filter((record: any) => record.kind === 'statement-review' && record.status === 'accepted'))
      .toContainEqual(expect.objectContaining({ taskDigest: taskVersion(tasks[2]), dependencies: [] }));
  });

  it('builds formal-only snapshots that bind definitions and helper dependencies but ignore goal scheduling', () => {
    const tasks = statementTasks(), snapshot = () => statementSnapshot(problem, tasks[2], workspace, git(workspace, ['rev-parse', 'HEAD']), 'fixed-env',
      [{ task: tasks[0], taskDigest: taskVersion(tasks[0]) }]);
    const before = snapshot();
    expect(before.definitions.find(definition => definition.file === 'Submission.lean')!.source)
      .toContain('namespace Submission\ndef fixed : Nat := 2\ntheorem first : True\nend Submission');
    fs.writeFileSync(path.join(project, 'Submission.lean'), original.replaceAll('by sorry', 'by trivial /- PROOF_SECRET -/'));
    commitSolverSources(problem, workspace);
    expect(snapshot().snapshotDigest).toBe(before.snapshotDigest);
    expect(JSON.stringify(snapshot())).not.toContain('PROOF_SECRET'); expect(JSON.stringify(snapshot())).not.toContain('INTENT_SECRET');
    const helperSnapshot = () => statementSnapshot(problem, tasks[1], workspace, git(workspace, ['rev-parse', 'HEAD']), 'fixed-env',
      [{ task: tasks[0], taskDigest: taskVersion(tasks[0]) }]);
    const helperBefore = helperSnapshot();
    tasks[0] = { ...tasks[0], revision: 1 };
    expect(snapshot().snapshotDigest).toBe(before.snapshotDigest);
    expect(helperSnapshot().snapshotDigest).toBe(helperBefore.snapshotDigest);
    expect(helperSnapshot().input.dependencies[0]!.taskDigest).toBe(taskVersion(tasks[0]));
    tasks[0] = { ...tasks[0], revision: 0 };
    fs.writeFileSync(path.join(project, 'Submission.lean'), original.replace('theorem first', 'def additional : Nat := 3\ntheorem first'));
    commitSolverSources(problem, workspace); expect(snapshot().snapshotDigest).not.toBe(before.snapshotDigest);
  });

  it('binds Lean-resolved imported names and definitions to the blind snapshot and detects tampering', () => {
    const task = statementTasks()[2];
    const context = { type: 'NNReal.pi / NNReal.sqrt 2', constants: [
      { name: 'NNReal.pi', module: 'Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic', type: 'NNReal', definition: '⟨Real.pi, ⋯⟩' },
      { name: 'NNReal.sqrt', module: 'Mathlib.Analysis.Real.Sqrt', type: 'NNReal ≃o NNReal', definition: 'OrderIso.symm (OrderIso.pow 2 ⋯)' }], omitted: [] };
    const snapshot = statementSnapshot(problem, task, workspace, problem.baseCommit, 'fixed-env', [], context);
    expect(snapshot.input.elaboration).toEqual(context);
    expect(statementSnapshot(problem, task, workspace, problem.baseCommit, 'fixed-env', [], { ...context, type: 'Real.pi / Real.sqrt 2' }).snapshotDigest)
      .not.toBe(snapshot.snapshotDigest);
    const reviewWorkspace = path.join(directory, 'blind');
    const review = { workspace: reviewWorkspace, files: writeStatementSnapshot(reviewWorkspace, snapshot) } as any;
    expect(() => assertStatementSnapshot(review)).not.toThrow();
    fs.appendFileSync(path.join(reviewWorkspace, 'STATEMENT.json'), ' ');
    expect(() => assertStatementSnapshot(review)).toThrow('math_statement_snapshot_changed');
    expect(() => parseLeanStatementContexts(JSON.stringify([{ id: task.id, context }]), ['different-task'])).toThrow('math_statement_elaboration_invalid');
  });

  it('captures pending statement references before a helper declaration or proof exists', () => {
    const task = statementTasks()[0], context = { type: 'True', constants: [], omitted: [], references: { statement: [], proof: [] } };
    const snapshot = statementSnapshot(problem, task, workspace, problem.baseCommit, 'fixed-env', [], context);
    expect(snapshot.references).toMatchObject({ scope: 'statement', statementType: 'True', inputs: [] });
    expect(snapshot.definitions.find(definition => definition.file === task.proofPath)!.source).not.toContain('lemma a');
    fs.writeFileSync(path.join(project, 'Submission.lean'), original.replace('theorem first', 'def unrelated : Nat := 3\ntheorem first'));
    const commit = commitSolverSources(problem, workspace);
    expect(proofReferencesUnchanged(problem, workspace, commit, snapshot.references!, 'fixed-env')).toBe(true);
    expect(statementSnapshot(problem, task, workspace, commit, 'fixed-env', [], context).snapshotDigest).not.toBe(snapshot.snapshotDigest);
    expect(statementSnapshot(problem, { ...task, type: 'False' }, workspace, commit, 'fixed-env', [], { ...context, type: 'False' }).references?.statementType).toBe('False');
    expect(proofReferencesUnchanged(problem, workspace, commit, snapshot.references!, 'changed-env')).toBe(false);
  });

  it('binds the fresh local definition closure of a pending type and falls back for unknown declarations', () => {
    const file = path.join(project, 'Submission.lean');
    const source = original.replace('theorem first', 'def inner : Nat := 2\ndef selected : Nat := inner\ndef unrelated : Nat := 0\ntheorem first');
    fs.writeFileSync(file, source);
    const commit = commitSolverSources(problem, workspace), task = { ...statementTasks()[0], type: 'Submission.selected = 2' };
    const context = { type: 'Eq Nat Submission.selected 2', constants: [], omitted: ['imported definition traversal bound reached'],
      references: { statement: [{ name: 'Submission.selected', file: 'Submission.lean' }, { name: 'Submission.inner', file: 'Submission.lean' }], proof: [] } };
    const snapshot = statementSnapshot(problem, task, workspace, commit, 'fixed-env', [], context);
    expect(snapshot.references?.inputs.map(input => input.name)).toEqual(['inner', 'selected']);
    fs.writeFileSync(file, source.replace('unrelated : Nat := 0', 'unrelated : Nat := 1'));
    expect(proofReferencesUnchanged(problem, workspace, commitSolverSources(problem, workspace), snapshot.references!, 'fixed-env')).toBe(true);
    fs.writeFileSync(file, source.replace('inner : Nat := 2', 'inner : Nat := 3'));
    expect(proofReferencesUnchanged(problem, workspace, commitSolverSources(problem, workspace), snapshot.references!, 'fixed-env')).toBe(false);
    fs.writeFileSync(file, source);
    const unknown = statementSnapshot(problem, task, workspace, commit, 'fixed-env', [], { ...context,
      references: { statement: [{ name: '_private.Submission.0.generated', file: 'Submission.lean' }], proof: [] } }).references!;
    expect(unknown.inputs.some(input => input.file === 'Submission.lean' && !input.name)).toBe(true);
    fs.writeFileSync(file, source.replace('unrelated : Nat := 0', 'unrelated : Nat := 2'));
    expect(proofReferencesUnchanged(problem, workspace, commitSolverSources(problem, workspace), unknown, 'fixed-env')).toBe(false);
  });

  it.each(['import', 'notation', 'instance', 'structure'])('preserves pending statement context invalidation for %s changes', change => {
    const task = statementTasks()[0], context = { type: 'True', constants: [], omitted: [], references: { statement: [], proof: [] } };
    const references = statementSnapshot(problem, task, workspace, problem.baseCommit, 'fixed-env', [], context).references!;
    const additions: Record<string, string> = { import: 'import Mathlib.Data.Nat.Basic\n', notation: 'notation "truth" => True\n',
      instance: 'instance custom : Inhabited Nat := ⟨3⟩\n', structure: 'structure Extra where\n  value : Nat\n' };
    fs.writeFileSync(path.join(project, 'Submission.lean'), additions[change] + original);
    git(workspace, ['add', 'generated/p/Submission.lean']);
    commitFixture(workspace, 'Fingerprint context changes');
    expect(proofReferencesUnchanged(problem, workspace, git(workspace, ['rev-parse', 'HEAD']), references, 'fixed-env')).toBe(false);
  });

  it('does not infer an empty local closure from legacy or invalid statement exports', () => {
    const task = statementTasks()[0], context = { type: 'True', constants: [], omitted: [] };
    expect(statementSnapshot(problem, task, workspace, problem.baseCommit, 'fixed-env', [], context).references).toBeUndefined();
    const parse = (references: unknown) => parseLeanStatementContexts(JSON.stringify([{ id: task.id, context: { ...context, references } }]), [task.id]);
    expect(parse({ statement: [], proof: [] }).get(task.id)?.references).toEqual({ statement: [], proof: [] });
    expect(() => parse({ statement: [], proof: [{ name: 'proof', file: 'Submission.lean' }] })).toThrow('math_statement_elaboration_invalid');
    expect(() => parse({ statement: [{ name: '', file: 'Submission.lean' }], proof: [] })).toThrow('math_statement_elaboration_invalid');
    expect(() => parse({ statement: Array.from({ length: 257 }, () => ({ name: 'a', file: 'Submission.lean' })), proof: [] }))
      .toThrow('math_statement_elaboration_invalid');
    expect(statementSnapshot(problem, task, workspace, problem.baseCommit, 'fixed-env', [], { ...context,
      references: { statement: [{ name: 'outside', file: '../outside.lean' }], proof: [] } }).references).toBeUndefined();
    expect(captureProofReferences(problem, workspace, problem.baseCommit, { name: task.theoremName!, file: task.proofPath! },
      { statement: [], proof: [] }, 'fixed-env', undefined, 'True')).toBeUndefined();
  });

  it('elaborates pending types together without theorem proof bodies and releases the projection on failure', async () => {
    const tasks = statementTasks().filter(task => task.statementReview), prepare = host.prepare.getMockImplementation()!;
    fs.writeFileSync(path.join(project, 'lake-manifest.json'), JSON.stringify({ packages: [] }));
    git(workspace, ['add', 'generated/p/lake-manifest.json']);
    commitFixture(workspace, 'Pin package manifest');
    const receiptFile = path.join(workspace, 'active-problem.json'), receipt = JSON.parse(fs.readFileSync(receiptFile, 'utf8'));
    receipt.trustedFiles.push('lake-manifest.json');
    fs.writeFileSync(receiptFile, JSON.stringify(receipt));
    problem = readSolverProblem(workspace, receiptFile);
    let projection = '';
    host.prepare.mockImplementationOnce(async input => {
      projection = input.projectRoot;
      expect(projection).not.toBe(project);
      expect(JSON.parse(fs.readFileSync(path.join(projection, '.lake/package-overrides.json'), 'utf8'))).toEqual({ schemaVersion: '1.2.0', packages: [] });
      expect(fs.readFileSync(path.join(projection, 'Submission.lean'), 'utf8')).not.toContain('PROOF_SECRET');
      expect(fs.readFileSync(path.join(projection, 'Submission.lean'), 'utf8')).toContain('by sorry');
      const query = fs.readFileSync(path.join(projection, input.files[0]), 'utf8');
      expect(query).toContain('Lean.getConstInfo'); expect(query).toContain('Lean.Meta.ppExpr root.type');
      expect(query).not.toContain('root.value'); expect(query).not.toContain('INTENT_SECRET');
      return prepare(input);
    });
    fs.writeFileSync(path.join(project, 'Submission.lean'), original.replaceAll('by sorry', 'by trivial /- PROOF_SECRET -/'));
    const commit = commitSolverSources(problem, workspace);
    const contexts = await captureStatementContexts(problem, tasks, workspace, commit, {}, undefined, 1000);
    expect([...contexts.keys()]).toEqual(tasks.map(task => task.id)); expect(fs.existsSync(projection)).toBe(false);
    expect(fs.readFileSync(path.join(project, 'Submission.lean'), 'utf8')).toContain('PROOF_SECRET');
    host.prepare.mockImplementationOnce(async input => { projection = input.projectRoot; return { exitCode: 1, stderr: 'type mismatch' }; });
    await expect(captureStatementContexts(problem, tasks, workspace, commit, {}, undefined, 1000)).rejects.toThrow('math_statement_elaboration_failed');
    expect(fs.existsSync(projection)).toBe(false); expect(host.verify).not.toHaveBeenCalled();
  });

  it('preserves failed projection inputs and full diagnostics while showing the first error', async () => {
    const warnings = 'Submission.lean:1:1: warning: declaration uses `sorry`\n'.repeat(60);
    host.prepare.mockImplementationOnce(async () => ({ exitCode: 1, stdout: warnings +
      'Submission.lean:80:4: error: unexpected token\nexpected a term\n', stderr: 'additional diagnostics' }));
    await expect(captureStatementContexts(problem, statementTasks().filter(task => task.statementReview),
      workspace, problem.baseCommit, {}, undefined, 1000)).rejects.toThrow(
      'math_statement_elaboration_failed\nSubmission.lean:80:4: error: unexpected token\nexpected a term');
    const diagnosticsRoot = path.join(path.dirname(workspace), 'statement-diagnostics');
    const reportDirectory = path.join(diagnosticsRoot, fs.readdirSync(diagnosticsRoot)[0]);
    const manifest = JSON.parse(fs.readFileSync(path.join(reportDirectory, 'manifest.json'), 'utf8'));
    expect(manifest).toMatchObject({ status: 'advisory-unverified', problemReceiptDigest: problem.receiptDigest,
      commit: problem.baseCommit, exitCode: 1 });
    expect(fs.readFileSync(path.join(reportDirectory, 'stdout.log'), 'utf8')).toContain(warnings);
    expect(fs.readFileSync(path.join(reportDirectory, 'stderr.log'), 'utf8')).toBe('additional diagnostics');
    expect(fs.readFileSync(path.join(reportDirectory, 'project/Submission.lean'), 'utf8')).toContain('by sorry');
    expect(manifest.files.some((file: any) => file.path.endsWith(manifest.query))).toBe(true);
    for (const file of manifest.files)
      expect(mathDigest(fs.readFileSync(path.join(reportDirectory, file.path)))).toBe(file.digest);
    expect(host.verify).not.toHaveBeenCalled();
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

  it.each(['notes-only', 'changed-source'] as const)('keeps integrated evidence after an unused planned dependency is revised (%s completion)', async completion => {
    const tasks = planTasks(); tasks[3] = { ...tasks[3], status: 'paused' };
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'task' && action.task.id === 'first') {
        expect(action.assignment.connectionCheck).toBeDefined();
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('first : True := by sorry', 'first : True := by exact b'));
        appendDelivery(options, action, { id: 'first-ready', kind: 'proof', summary: 'Only b is used', commit: commitSolverSources(problem, options.workspace) });
        await expect.poll(() => cooperationState().tasks[2].status).toBe('integrated');
        tasks[0] = { ...tasks[0], revision: 1, premises: ['Revised mathematical input'], status: 'paused' }; tasks[3] = { ...tasks[3], status: 'active' };
        fs.appendFileSync(`${output}.runtime/edits.jsonl`, JSON.stringify({ id: 'unused-revision', baseVersion: cooperationState().planVersion, tasks }) + '\n');
        await expect.poll(() => cooperationState().edits?.some((edit: any) => edit.id === 'unused-revision' && edit.status === 'applied')).toBe(true);
        expect(cooperationState().tasks[2].status).toBe('integrated');
        const edit = cooperationState().edits.find((record: any) => record.id === 'unused-revision');
        expect(edit).toMatchObject({ status: 'applied', receivedAt: expect.any(Number), appliedAt: expect.any(Number),
          planVersion: cooperationState().planVersion, affectedTasks: ['a'],
          recheck: { status: 'pending', tasks: [{ taskId: 'a', taskDigest: taskVersion(tasks[0]), status: 'pending' }] } });
        expect(edit.recheck.tasks[0].lastCheck).toBeUndefined();
        fs.appendFileSync(path.join(options.workspace, 'RESEARCH.md'), '\nProof integrated; the revised a is unused.\n');
        if (completion === 'changed-source') fs.writeFileSync(file,
          fs.readFileSync(file, 'utf8').replace('first : True := by exact b', 'first : True := by sorry'));
      } else {
        if (action.kind === 'task' && ['a', 'b'].includes(action.task.id))
          await expect.poll(() => cooperationState().tasks[2].status).toBe('conditional');
        if (action.kind === 'task' && action.task.id === 'second') {
          expect(action.assignment.dependencies?.map(dependency => dependency.taskId)).toEqual(['first', 'b']);
          const context = JSON.parse(fs.readFileSync(path.join(options.workspace, 'COOPERATION.json'), 'utf8'));
          expect(context.deliveries.find((record: any) => record.taskId === 'first' && record.status === 'verified'))
            .toMatchObject({ dependencies: [{ taskId: 'b', taskDigest: taskVersion(tasks[1]) }] });
          expect(context.deliveries.some((record: any) => record.submissionId === 'first-ready')).toBe(false);
          expect(context.peers.find((peer: any) => peer.id === 'a').status).toBe('pending');
          expect(context.edits.find((record: any) => record.id === 'unused-revision').recheck.status).toBe('pending');
        }
        finishAssignment(action, options);
      }
      return 'completed';
    });
    configureReferenceReports({ first: ['b'], second: ['first', 'b'] });
    const parallelArgs = [...args, '--workers', '4', '--max-turns', '5'];
    const code = await runSolver(parallelArgs, directory);
    const before = cooperationState(), delivery = before.deliveries.find((record: any) => record.taskId === 'first' && record.status === 'verified');
    expect(before.history.map((node: any) => node.task.id)).toEqual(['a']);
    expect(delivery).toMatchObject({ status: 'verified', dependencies: [{ taskId: 'b', taskDigest: taskVersion(tasks[1]) }] });
    expect(before.deliveries.find((record: any) => record.submissionId === 'first-ready')).toMatchObject({ status: 'conditional',
      dependencies: [{ taskId: 'a' }, { taskId: 'b', taskDigest: taskVersion(tasks[1]) }] });
    expect(before.tasks[2].integratedCheck.conditions ?? []).toEqual([]);
    expect(before.tasks[2].integratedCheck.references.tasks).toEqual([{ taskId: 'b', taskDigest: taskVersion(tasks[1]) }]);
    expect(before.deliveries.some((record: any) => record.taskId === 'first' && record.status === 'superseded')).toBe(false);
    expect(host.officialGate).not.toHaveBeenCalled();
    if (completion === 'changed-source') {
      expect(code).toBe(1);
      expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ run_outcome: 'runtime_error', reason: 'math_task_condition_version_invalid' });
      expect(git(workspace, ['show', `${before.tasks[2].integratedCheck.commit}:generated/p/Submission.lean`]))
        .toContain('first : True := by exact b');
      return;
    }
    expect(code).toBe(4);
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

  it('revalidates checked sources without new model proof turns after descriptive plan revisions', async () => {
    const tasks = planTasks(), reviewStopped = deferred();
    let reviews = 0, reviewerWorkspace = '';
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'review' && ++reviews === 1) {
        reviewerWorkspace = options.workspace;
        tasks[0] = { ...tasks[0], objective: 'Clarify the same helper theorem', revision: 1 };
        fs.appendFileSync(`${output}.runtime/edits.jsonl`, JSON.stringify({ id: 'description-only',
          baseVersion: cooperationState().planVersion, tasks }) + '\n');
        await reviewStopped.promise;
        finishAssignment(action, options);
      } else finishAssignment(action, options);
      return 'completed';
    });
    configureReferenceReports();
    const create = host.createSession.getMockImplementation()!;
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ ...await create(options),
      interrupt: vi.fn(async () => { if (options.workspace === reviewerWorkspace) reviewStopped.resolve(); }) }));
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '9'], directory)).toBe(0);
    const state = cooperationState();
    expect(state.tasks.map((node: TaskRecord) => node.attempts)).toEqual([1, 1, 1, 1]);
    expect(state.edits[0]).toMatchObject({ status: 'applied', recheck: { status: 'passed' } });
    expect(state.tasks[0].integratedCheck.taskDigest).toBe(taskVersion(tasks[0]));
    expect(state.tasks[2].integratedCheck.references.tasks).toContainEqual({ taskId: 'a', taskDigest: taskVersion(tasks[0]) });
    expect(reviews).toBe(2);
    expect(host.officialGate).toHaveBeenCalledOnce();
  }, 20_000);

  it.each(['actual', 'missing', 'whole-module'] as const)('invalidates dependent proofs and archives their old deliveries after a live revision (%s references)', async trace => {
    const tasks = planTasks(), reviewStopped = deferred();
    let reviews = 0, reviewerWorkspace = '';
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'review' && ++reviews === 1) {
        reviewerWorkspace = options.workspace; tasks[0] = { ...tasks[0], revision: 1, premises: ['Revised mathematical input'] };
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
    for (const id of ['a', 'first', 'second']) {
      const statuses = state.deliveries.filter((record: any) => record.taskId === id && record.kind === 'proof')
        .map((record: any) => record.status);
      expect(statuses).toContain('superseded'); expect(statuses.at(-1)).toBe('verified');
      expect(statuses.filter((status: string) => status === 'verified')).toHaveLength(1);
      expect(statuses.slice(0, -1).every((status: string) => ['superseded', 'conditional'].includes(status))).toBe(true);
    }
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
    const tasks = waitingPlanTasks();
    // Save the unplanned input before its consumer becomes ready.
    [tasks[0], tasks[1]] = [tasks[1], tasks[0]];
    tasks[2] = { ...tasks[2], dependsOn: ['a'] };
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'task' && action.task.id === 'first') {
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('first : True := by sorry', 'first : True := by exact b'));
      } else finishAssignment(action, options);
      return 'completed';
    });
    configureReferenceReports({ first: ['b'], second: ['first', 'b'] });
    const verify = host.verify.getMockImplementation()!;
    host.verify.mockImplementation(async (request, options) => {
      if (request.items.some(item => item.theoremName === 'Submission.first'))
        expect(fs.readFileSync(path.join(request.projectRoot, 'Submission.lean'), 'utf8')).toContain('lemma b : True');
      return verify(request, options);
    });
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '6'], directory)).toBe(0);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    const first = state.cooperation.tasks[2];
    expect(first.task.dependsOn).toEqual(['a']);
    expect(first.integratedCheck.references.tasks).toEqual([{ taskId: 'b', taskDigest: taskVersion(tasks[0]) }]);
    expect(first.integratedCheck.references).toMatchObject({ sourceCommit: first.integratedCheck.commit, environmentDigest: state.environmentDigest });
    expect(first.integratedCheck.references.inputs.map((input: any) => input.name)).toEqual(['b', 'first']);
    const live = JSON.parse(fs.readFileSync(path.join(state.worktree, 'COOPERATION.json'), 'utf8'));
    expect(live.peers[2].actualReferences.tasks).toEqual(first.integratedCheck.references.tasks);
    for (const [index, peer] of live.peers.entries()) {
      expect(peer.taskDigest).toBe(taskVersion(state.cooperation.tasks[index].task));
      expect(peer.objectiveDigest).toBe(mathDigest(state.cooperation.tasks[index].task.objective));
    }
  });

  it('retains a supporting declaration fingerprint without inventing a whole producer-task dependency', async () => {
    const helper = 'Submission/Helpers.lean';
    fs.mkdirSync(path.join(project, 'Submission'));
    fs.writeFileSync(path.join(project, helper), 'namespace Submission.Helpers\nend Submission.Helpers\n');
    const receipt = JSON.parse(fs.readFileSync(problem.activeProblemPath, 'utf8'));
    receipt.solverOwnedFiles.push(helper);
    fs.writeFileSync(problem.activeProblemPath, JSON.stringify(receipt));
    git(workspace, ['add', '--', `generated/p/${helper}`]);
    commitFixture(workspace, 'Owned helper module');
    problem = readSolverProblem(workspace, problem.activeProblemPath);
    configureCooperation(async (action, options) => {
      finishAssignment(action, options);
      if (action.kind === 'task' && action.task.id === 'a') {
        fs.writeFileSync(path.join(options.workspace, problem.projectRelative, helper),
          'namespace Submission.Helpers\nlemma support : True := by trivial\nend Submission.Helpers\n');
      }
      return 'completed';
    });
    const verify = host.verify.getMockImplementation()!;
    host.verify.mockImplementation(async (request, options) => {
      const result = await verify(request, options);
      if (!options.collectDeclarationReferences) return result;
      return { ...result, results: result.results.map(item => ({ ...item, declarationReferences: { statement: [],
        proof: item.theoremName === 'Submission.first' ? [{ name: 'Submission.Helpers.support', file: helper }] : [] } })) };
    });
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '6'], directory)).toBe(0);
    const first = cooperationState().tasks.find((node: any) => node.task.id === 'first');
    expect(first.integratedCheck.references.tasks).toEqual([]);
    expect(first.integratedCheck.references.inputs).toContainEqual(expect.objectContaining({ file: helper, name: 'support' }));
  });

  it('rechecks a changed definition consumer while retaining the unrelated checked proof at its original receipt commit', async () => {
    const update: CooperativeTask = { id: 'update', kind: 'research', objective: 'Request a definition revision', dependsOn: ['a', 'b'], revision: 0 };
    const tasks = planTasks();
    tasks[2] = { ...tasks[2], dependsOn: [...tasks[2].dependsOn, update.id] };
    tasks.splice(2, 0, update); let leads = 0;
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') {
        fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify({ tasks,
          challengeDecisions: action.challengeIds?.map(id => ({ id, status: 'revised',
            reason: 'Revise selected from 2 to 3 and recheck its actual consumers; keep unrelated checked declarations.' })),
        }) + '\n```');
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
    for (const [name, count] of [['a', 2], ['b', 1]] as const)
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
    for (const id of ['a', 'b']) expect(host.verify.mock.calls.some(([request]) =>
      request.items.some(item => item.theoremName === `Submission.${id}`))).toBe(true);
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
      commitFixture(workspace, 'Fingerprint inputs', '--allow-empty');
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

  it('checks a conditional parent while its lemmas run and integrates it without another model turn once they close', async () => {
    const tasks = planTasks(); tasks[2] = { ...tasks[2], conditional: true };
    let parentTurns = 0, conditionalChecks = 0;
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'task' && action.task.kind === 'lemma') {
        await expect.poll(() => cooperationState().tasks[2].status).toBe('conditional');
        expect(host.officialGate).not.toHaveBeenCalled();
        const parent = cooperationState().tasks[2];
        expect(parent.integratedCheck).toBeUndefined();
        expect(parent.proof.conditions.map((condition: any) => condition.taskId)).toEqual(['a', 'b']);
        finishAssignment(action, options);
      } else if (action.kind === 'task' && action.task.id === 'first') {
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
        expect(source).not.toContain('-- Submission.a remains a reference in this comment.');
        expect(source).not.toMatch(/lemma [ab]/u);
        expect(source).not.toContain('sorry');
      }
      return verify(request, options);
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '6'], directory)).toBe(0);
    expect(parentTurns).toBe(1); expect(conditionalChecks).toBe(1);
    expect(cooperationState().tasks.every((node: any) => node.status === 'integrated')).toBe(true);
    const records = cooperationState().deliveries.filter((record: any) => record.taskId === 'first' && record.kind === 'proof');
    expect(records.map((record: any) => record.status)).toEqual(['conditional', 'verified']);
    expect(records[0].remainingObligations).toEqual(['a', 'b']);
    expect(records[1].remainingObligations).toEqual([]);
    const source = fs.readFileSync(path.join(project, 'Submission.lean'), 'utf8');
    expect(source).not.toContain('(a : True)');
    expect(source).toContain('-- Submission.a remains a reference in this comment.');
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
        ? failed(result, { error: 'Lean exited with status 1.', stdoutPreview: 'Submission.lean:1:0: error: fixture combined proof does not close the target' })
        : result;
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
    const projection = before.cooperation.tasks[2].proof.projection;
    expect(projection).toMatchObject({ environmentDigest: before.environmentDigest,
      problemReceiptDigest: expect.any(String), sourceDigest: expect.any(String) });
    host.createSession.mockClear(); host.verify.mockClear();
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '2', '--resume'], directory)).toBe(4);
    expect(host.createSession).not.toHaveBeenCalled();
    expect(cooperationState().tasks[2]).toMatchObject({ status: 'conditional', attempts: 1, proof: { projection, passed: true } });
    expect(cooperationState().tasks[0].task.status).toBe('paused');
    expect(cooperationState().tasks[1].task.status).toBe('paused');
    expect(host.verify).toHaveBeenCalledOnce();
    expect(host.officialGate).not.toHaveBeenCalled();
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
    const tasks: CooperativeTask[] = [{ id: 'question', kind: 'research', objective: 'Decide a mathematical route', dependsOn: [], revision: 0 }, ...waitingPlanTasks()];
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') {
        if (++leadTurns === 2) { leadBusy.resolve(); await consumerStarted.promise; }
        fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify({ tasks,
          challengeDecisions: action.challengeIds?.map(id => ({ id, status: 'deferred',
            reason: 'Continue the current a/b to first to second construction while its consumers are being checked.',
            reopenOn: 'A checked consumer failure showing that a and b cannot establish first, or first cannot establish second.' })),
        }) + '\n```');
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
      if (action.kind === 'lead') { writePlan(options.workspace, waitingPlanTasks()); return 'completed'; }
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
    const verify = host.verify.getMockImplementation()!;
    host.verify.mockImplementation(async (...inputs) => {
      const result: MathematicsVerifierBatchResult = await verify(...inputs);
      return { ...result, events: [{ event: 'diagnostic.emitted', details: { message: 'FULL_CHECK_TRACE' } }],
        results: result.results.map(receipt => ({ ...receipt, stdoutPreview: 'FULL_CHECK_OUTPUT' })) };
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '6'], directory)).toBe(0);
    expect(cooperationState().deliveries.find((record: any) => record.submissionId === 'early-a')).toMatchObject({
      kind: 'proof', status: 'verified', producer: 'researcher-1', commit: deliveredCommit,
      statement: 'True', remainingObligations: [], evidence: { passed: true } });
    const delivery = cooperationState().deliveries.find((record: any) => record.submissionId === 'early-a');
    const proof = cooperationState().tasks[0].proof;
    expect(delivery.evidence.verification).toMatchObject({ status: 'kernel_verified', targetCommit: proof.verification.targetCommit,
      results: expect.arrayContaining([expect.objectContaining({ receiptId: expect.any(String) })]) });
    expect(delivery.evidence.verification.results).toEqual(proof.verification.results.map((receipt: any) => ({ receiptId: receipt.receiptId })));
    expect(delivery.evidence.verification).not.toHaveProperty('events');
    expect(delivery.evidence.verification.results[0]).not.toHaveProperty('stdoutPreview');
    expect(proof.verification.events[0].details.message).toBe('FULL_CHECK_TRACE');
    expect(proof.verification.results[0].stdoutPreview).toBe('FULL_CHECK_OUTPUT');
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
        if (action.assignment.connectionCheck) expect(action.assignment.connectionCheck.inputs)
          .toEqual([{ taskId: 'a', taskDigest: taskVersion(tasks[0]) }]);
        else expect(cooperationState().tasks[0].status).toBe('integrated');
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
    const tasks = waitingPlanTasks();
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
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '7'], directory)).toBe(0);
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

  it('checks two independent early deliveries concurrently while both producers are still running', async () => {
    const entered = new Set<string>();
    const both = deferred();
    const checkTask = async (...input: Parameters<typeof checkTaskProof>) => {
      const task = input[3];
      if (['a', 'b'].includes(task.id) && input[1] !== path.join(`${output}.runtime`, 'worktree')) {
        entered.add(task.id); if (entered.size === 2) both.resolve(); await both.promise;
      }
      return checkTaskProof(...input);
    };
    configureCooperation(async (action, options) => {
      finishAssignment(action, options);
      if (action.kind === 'task' && ['a', 'b'].includes(action.task.id)) {
        const commit = commitSolverSources(problem, options.workspace);
        fs.appendFileSync(path.join(options.workspace, assignmentDeliveryFile(action.assignment)), JSON.stringify({ kind: 'proof', commit }) + '\n');
        await expect.poll(() => cooperationState().tasks.filter((node: any) => ['a', 'b'].includes(node.task.id))
          .every((node: any) => node.status === 'integrated')).toBe(true);
      }
      return 'completed';
    });
    try {
      expect(await runSolver([...args, '--workers', '4', '--max-turns', '8'], directory,
        { ...directSolverModules, M2: { ...directSolverModules.M2, checkTask } })).toBe(0);
      expect(entered.size).toBe(2);
    } finally { both.resolve(); }
  }, 30_000);

  it('continues polling human edits while an early proof check is waiting', async () => {
    const checking = deferred(), resume = deferred();
    const checkTask = async (...input: Parameters<typeof checkTaskProof>) => {
      if (input[3].id === 'a' && input[1] !== path.join(`${output}.runtime`, 'worktree')) {
        checking.resolve(); await resume.promise;
      }
      return checkTaskProof(...input);
    };
    configureCooperation(async (action, options) => {
      finishAssignment(action, options);
      if (action.kind === 'task' && action.task.id === 'a') {
        const commit = commitSolverSources(problem, options.workspace);
        appendDelivery(options, action, { id: 'waiting-proof', kind: 'proof', commit, summary: 'Ready' });
        await checking.promise;
        fs.appendFileSync(`${output}.runtime/edits.jsonl`, JSON.stringify({ id: 'during-check', baseVersion: 'stale' }) + '\n');
        try {
          await expect.poll(() => cooperationState().edits?.find((edit: any) => edit.id === 'during-check')?.status).toBe('rejected');
        } finally { resume.resolve(); }
      }
      return 'completed';
    });
    try {
      expect(await runSolver([...args, '--workers', '4', '--max-turns', '8'], directory,
        { ...directSolverModules, M2: { ...directSolverModules.M2, checkTask } })).toBe(0);
    } finally { resume.resolve(); }
  }, 30_000);

  it('keeps search stopping decisions separate from proof acceptance', async () => {
    const select = vi.fn((...inputs: Parameters<typeof directSolverModules.M3.select>) => {
      expect(inputs[2]).toMatchObject({ maxTurns: 1, aborted: false });
      return { operation: 'stop' as const, reason: 'no-operation' as const };
    });
    const modules = { ...directSolverModules, M3: { ...directSolverModules.M3, version: 'test-stop-v1', select } };
    expect(await runSolver(args, directory, modules)).toBe(4);
    expect(select).toHaveBeenCalledTimes(1);
    expect(host.createSession).not.toHaveBeenCalled();
    expect(host.verify).not.toHaveBeenCalled();
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'incomplete', turns: 0,
      solution_commit: null, completion_signal_valid: false });
  });

  it('keeps the host turn limit when a replacement search policy requests more work', async () => {
    host.verify.mockImplementation(async request => failed(verified(request)));
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
    host.verify.mockImplementationOnce(async request => failed(verified(request)));
    let turns = 0;
    host.createSession.mockImplementation(session('fixture-thread', async options => {
      turns++;
      clock.mockReturnValue(now + turns * 24 * 60 * 60 * 1000);
      fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'),
        original.replaceAll('by sorry', `by\n  -- attempt ${turns}\n  trivial`));
      return 'completed';
    }));
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

  it('gives final acceptance its own budget after solving finishes near the deadline', async () => {
    vi.useFakeTimers({ toFake: ['setTimeout', 'clearTimeout', 'Date'] });
    host.verify.mockImplementation(async request => {
      if (request.projectRoot !== project) await vi.advanceTimersByTimeAsync(900);
      return verified(request);
    });
    host.officialGate.mockImplementation(async ({ signal }) => {
      await vi.advanceTimersByTimeAsync(1500);
      signal.throwIfAborted();
      return { comparison: { status: 'official_verified' } };
    });
    expect(await runSolver([...args, '--max-run-seconds', '1', '--evaluator-timeout-seconds', '10'], directory)).toBe(0);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'evaluated_passed', solveWallMs: 900 });
    expect(vi.getTimerCount()).toBe(0);
  });

  it.each([1, 300, 3_000_000])('applies a finite %s-second evaluator budget to the integrated Lean recheck', async seconds => {
    vi.useFakeTimers({ toFake: ['setTimeout', 'clearTimeout', 'Date'] });
    host.officialGate.mockImplementation(async ({ signal }) => {
      await vi.advanceTimersByTimeAsync(10);
      signal.throwIfAborted();
      return { comparison: { status: 'official_verified' } };
    });
    expect(await runSolver([...args, '--evaluator-timeout-seconds', String(seconds)], directory)).toBe(0);
    const recheck = host.verify.mock.calls.find(([request]) => request.projectRoot === project);
    expect(recheck?.[0].timeoutMs).toBe(seconds * 1000);
    expect(vi.getTimerCount()).toBe(0);
  });

  it.each(['recheck', 'official'])('enforces the total evaluator budget when time runs out during %s', async phase => {
    vi.useFakeTimers({ toFake: ['setTimeout', 'clearTimeout', 'Date'] });
    host.verify.mockImplementation(async request => {
      if (request.projectRoot === project) await vi.advanceTimersByTimeAsync(phase === 'recheck' ? 1001 : 600);
      return verified(request);
    });
    host.officialGate.mockImplementation(async ({ signal }) => {
      expect(signal.aborted).toBe(false);
      await vi.advanceTimersByTimeAsync(401);
      expect(signal.aborted).toBe(true);
      return { comparison: { status: 'official_verified' } };
    });
    expect(await runSolver([...args, '--evaluator-timeout-seconds', '1'], directory)).toBe(1);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'runtime_error',
      completion_signal_valid: false, evaluator: { status: 'error', reason: 'math_evaluation_timeout', timedOut: true } });
    expect(host.officialGate).toHaveBeenCalledTimes(phase === 'recheck' ? 0 : 1);
    expect(vi.getTimerCount()).toBe(0);
  });

  it.each([false, true])('shares the evaluator budget with an external command (timeout: %s)', async timeout => {
    vi.useFakeTimers({ toFake: ['setTimeout', 'clearTimeout', 'Date'] });
    host.verify.mockImplementation(async request => {
      if (request.projectRoot === project) await vi.advanceTimersByTimeAsync(600);
      return verified(request);
    });
    const command = vi.spyOn(verifier, 'runMathematicsSandboxedCommand').mockImplementation(async input => {
      expect(input.timeoutMs).toBe(1000);
      expect(input.signal?.aborted).toBe(false);
      await vi.advanceTimersByTimeAsync(timeout ? 401 : 300);
      expect(input.signal?.aborted).toBe(timeout);
      return { started: true, exitCode: 0, signal: null, stdout: '', stderr: '', timedOut: false, aborted: false, durationMs: 300 };
    });
    expect(await runSolver([...args, '--evaluator-command', 'fixture-evaluator', '--evaluator-timeout-seconds', '1'], directory)).toBe(timeout ? 1 : 0);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject(timeout
      ? { status: 'runtime_error', evaluator: { status: 'error', reason: 'math_evaluation_timeout', timedOut: true } }
      : { status: 'evaluated_passed', evaluator: { status: 'passed', method: 'external-command', official: false } });
    expect(command).toHaveBeenCalledOnce();
    expect(host.officialGate).not.toHaveBeenCalled();
    expect(vi.getTimerCount()).toBe(0);
  });

  it.each(['SIGINT', 'SIGTERM'] as const)('still cancels unlimited final acceptance on %s', async interrupt => {
    host.officialGate.mockImplementation(async ({ signal }) => {
      process.emit(interrupt);
      signal.throwIfAborted();
    });
    expect(await runSolver([...args, '--evaluator-timeout-seconds', '0'], directory)).toBe(4);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'limit_reached', reason: 'math_run_stopped' });
    expect(host.officialGate).toHaveBeenCalledOnce();
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
    host.verify.mockImplementation(async request => failed(verified(request)));
    const check = async (...inputs: Parameters<typeof checkSolverProof>) => ({ ...await checkSolverProof(...inputs), passed: true });
    const modules = { ...directSolverModules, M2: { version: 'test-false-positive-v1', check } };
    expect(await runSolver(args, directory, modules)).toBe(1);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'runtime_error',
      reason: 'math_integrated_proof_mismatch', evaluator: { status: 'skipped' } });
    expect(host.verify).toHaveBeenCalledTimes(2);
    expect(host.officialGate).not.toHaveBeenCalled();
  });

  it.each(['failed', 'transport_closed', 'stream_disconnected'])('checks a saved proof after a %s turn before independent evaluation', async status => {
    const run = vi.fn();
    const close = vi.fn();
    host.createSession.mockImplementation(async (options: MathAgentOptions) => {
      run.mockImplementation(async () => {
        fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
        if (status === 'transport_closed') throw new Error('math_codex_transport_closed');
        return 'failed';
      });
      return { threadId: 'fixture-thread', lastError: status === 'stream_disconnected'
        ? 'stream disconnected before completion: error sending request' : undefined, run, close, interrupt: vi.fn() };
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
    host.verify.mockImplementationOnce(async request => failed(verified(request), { stdoutPreview: unsolved }));
    const run = vi.fn(async () => {
      if (status === 'transport_closed') throw new Error('math_codex_transport_closed');
      return status;
    });
    host.createSession.mockResolvedValueOnce({ threadId: 'fixture-thread', run, close: vi.fn(), interrupt: vi.fn() });
    expect(await runSolver([...args, '--max-turns', '1'], directory)).toBe(1);
    expect(run).toHaveBeenCalledTimes(1);
    expect(host.verify).toHaveBeenCalledTimes(1);
    expect(host.officialGate).not.toHaveBeenCalled();
    expect(git(workspace, ['rev-parse', 'HEAD'])).toBe(problem.baseCommit);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'runtime_error', turns: 1, reason: 'math_model_turn_failed' });
    const resumed = vi.fn();
    host.createSession.mockImplementation(async (options: MathAgentOptions) => {
      resumed.mockImplementation(async () => {
        fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
        return 'completed';
      });
      return { threadId: options.threadId!, run: resumed, close: vi.fn(), interrupt: vi.fn() };
    });
    expect(await runSolver([...args, '--resume', '--max-turns', '2'], directory)).toBe(0);
    expect(resumed.mock.calls[0][0]).toContain(unsolved);
    expect(host.createSession.mock.calls[1][0].threadId).toBe('fixture-thread');
    expect(host.verify).toHaveBeenCalledTimes(3);
  });

  it('reports a failed turn with invalid sources without retrying the closed session', async () => {
    const run = vi.fn();
    host.createSession.mockImplementation(async (options: MathAgentOptions) => {
      run.mockImplementation(async () => {
        fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replace('first : True', 'first : False'));
        return 'failed';
      });
      return { threadId: 'fixture-thread', run, close: vi.fn(), interrupt: vi.fn() };
    });
    expect(await runSolver([...args, '--max-turns', '3'], directory)).toBe(1);
    expect(run).toHaveBeenCalledTimes(1);
    expect(host.verify).not.toHaveBeenCalled();
    expect(host.officialGate).not.toHaveBeenCalled();
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'runtime_error', turns: 1,
      reason: expect.stringContaining('math_original_declaration_changed') });
  });

  it.each(['stream disconnected before completion: Concurrency limit exceeded for account, please retry later',
    'stream disconnected before completion: error sending request', 'math_codex_transport_closed', 'Service unavailable (503)'])
  ('automatically resumes a failed request with saved proof and Lean feedback (%s)', async error => {
    const partial = original.replace('theorem first : True := by sorry', 'theorem first : True := by trivial');
    host.verify.mockImplementationOnce(async request => failed(verified(request), { stdoutPreview: unsolved }));
    host.createSession.mockImplementationOnce(async (options: MathAgentOptions) => ({ threadId: 'fixture-thread',
      lastError: error,
      run: async () => {
        fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), partial);
        return 'failed';
      }, close: vi.fn(), interrupt: vi.fn() }));
    const resumed = vi.fn();
    host.createSession.mockImplementationOnce(session(options => options.threadId || 'resumed-thread', async (options, message) => {
      resumed(message);
      expect(fs.readFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), 'utf8')).toBe(partial);
      fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
      return 'completed';
    }));
    expect(await runSolver([...args, '--max-turns', '3'], directory)).toBe(0);
    expect(host.createSession.mock.calls[1][0].threadId).toBe(error.includes('Concurrency limit') ? 'fixture-thread' : undefined);
    expect(resumed.mock.calls[0][0]).toContain(unsolved);
    expect(host.delay).toHaveBeenCalledWith(10_000, undefined, { signal: expect.any(AbortSignal) });
    expect(host.verify).toHaveBeenCalledTimes(3);
    expect(host.officialGate).toHaveBeenCalledTimes(1);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'evaluated_passed', turns: 2 });
  });

  it('starts a fresh thread after the first request failure while retaining proof and feedback', async () => {
    const partial = original.replace('theorem first : True := by sorry', 'theorem first : True := by trivial');
    let turns = 0;
    host.verify.mockImplementation(async request => turns < 3 ? failed(verified(request), { stdoutPreview: unsolved }) : verified(request));
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({
      threadId: options.threadId || (turns ? 'fresh-thread' : 'fixture-thread'),
      lastError: 'stream disconnected before completion: error sending request',
      run: async (message: string) => {
        turns++;
        options.onUsage({ totalTokens: turns === 3 ? 15 : 10 });
        if (turns === 1) fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), partial);
        if (turns < 3) return 'failed';
        expect(options.threadId).toBe('fresh-thread');
        expect(fs.readFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), 'utf8')).toBe(partial);
        expect(message).toContain(unsolved);
        fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
        return 'completed';
      }, close: vi.fn(), interrupt: vi.fn(),
    }));
    expect(await runSolver([...args, '--max-turns', '4'], directory)).toBe(0);
    expect(host.createSession.mock.calls.map(call => call[0].threadId)).toEqual([undefined, undefined, 'fresh-thread']);
    expect(host.delay.mock.calls.map(call => call[0])).toEqual([10_000, 20_000]);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state).toMatchObject({ turns: 3, threadId: 'fresh-thread', previousThreadIds: ['fixture-thread'],
      usage: { totalTokens: 25 }, usageBeforeThread: { totalTokens: 10 }, lastFailure: { reason: 'math_model_request_failed' } });
    expect(host.officialGate).toHaveBeenCalledOnce();
  });

  it('reopens a disconnected startup without spending another turn or discarding saved proof', async () => {
    const partial = original.replace('first : True := by sorry', 'first : True := by trivial');
    host.createSession.mockImplementationOnce(async (options: MathAgentOptions) => {
      fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), partial);
      throw new Error('math_codex_transport_closed:process_exit:code=9:signal=none');
    });
    host.createSession.mockImplementationOnce(session('reopened', async options => {
      expect(fs.readFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), 'utf8')).toBe(partial);
      fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
      return 'completed';
    }));
    expect(await runSolver(args, directory)).toBe(0);
    expect(host.createSession).toHaveBeenCalledTimes(2);
    expect(host.delay).toHaveBeenCalledOnce();
    expect(JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8')).turns).toBe(1);
    expect(host.officialGate).toHaveBeenCalledOnce();
  });

  it('bounds disconnected session startup retries and releases its unstarted turn', async () => {
    host.createSession.mockRejectedValue(new Error('math_codex_transport_closed:process_exit:code=9:signal=none'));
    expect(await runSolver(args, directory)).toBe(1);
    expect(host.createSession).toHaveBeenCalledTimes(4);
    expect(host.delay.mock.calls.map(call => call[0])).toEqual([10_000, 20_000, 40_000]);
    expect(JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8')).turns).toBe(0);
  });

  it('avoids preparing or opening a spare session when selection stops after retry backoff', async () => {
    host.verify.mockImplementation(async request => failed(verified(request)));
    host.createSession.mockResolvedValue({ threadId: 'fixture-thread', lastError: 'Concurrency limit exceeded for account',
      run: vi.fn().mockResolvedValue('failed'), close: vi.fn(), interrupt: vi.fn() });
    const build = vi.fn(directSolverModules.M4.build);
    const select = vi.fn(directSolverModules.M3.select)
      .mockImplementationOnce(directSolverModules.M3.select)
      .mockReturnValue({ operation: 'stop', reason: 'no-operation' });
    expect(await runSolver([...args, '--max-turns', '3'], directory, {
      ...directSolverModules, M3: { ...directSolverModules.M3, select }, M4: { ...directSolverModules.M4, build },
    })).toBe(4);
    expect(host.delay).toHaveBeenCalledOnce();
    expect(select).toHaveBeenCalledTimes(2);
    expect(build).toHaveBeenCalledOnce();
    expect(host.createSession).toHaveBeenCalledOnce();
    expect(host.officialGate).not.toHaveBeenCalled();
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'incomplete', turns: 1 });
  });

  it.each([2, 10])('bounds request retries by both retry and turn limits (%s turns)', async maxTurns => {
    host.verify.mockImplementation(async request => failed(verified(request), { stdoutPreview: unsolved }));
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ threadId: options.threadId || 'fixture-thread',
      lastError: 'Concurrency limit exceeded for account', run: vi.fn().mockResolvedValue('failed'), close: vi.fn(), interrupt: vi.fn() }));
    expect(await runSolver([...args, '--max-turns', String(maxTurns)], directory)).toBe(1);
    const turns = Math.min(maxTurns, 4);
    expect(host.createSession).toHaveBeenCalledTimes(turns);
    expect(host.delay.mock.calls.map(call => call[0])).toEqual([10_000, 20_000, 40_000].slice(0, turns - 1));
    expect(host.officialGate).not.toHaveBeenCalled();
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'runtime_error', turns, reason: 'math_model_concurrency_limit' });
    expect(JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8')).error).toBe('math_model_concurrency_limit');
  });

  it('stops an aborted rate-limit backoff without creating another session', async () => {
    host.verify.mockImplementation(async request => failed(verified(request)));
    host.createSession.mockResolvedValueOnce({ threadId: 'fixture-thread', lastError: 'Concurrency limit exceeded for account',
      run: vi.fn().mockResolvedValue('failed'), close: vi.fn(), interrupt: vi.fn() });
    host.delay.mockImplementationOnce(async () => { process.emit('SIGTERM'); });
    expect(await runSolver([...args, '--max-turns', '3'], directory)).toBe(4);
    expect(host.createSession).toHaveBeenCalledTimes(1);
    expect(JSON.parse(fs.readFileSync(output, 'utf8')).status).toBe('limit_reached');
    expect(JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8')).check.passed).toBe(false);
  });

  it('resets the request retry count after successful turns', async () => {
    let turns = 0;
    host.verify.mockImplementation(async request => turns === 8 ? verified(request) : failed(verified(request)));
    host.createSession.mockImplementation(session(options => options.threadId || 'fixture-thread', async options => {
      if (++turns === 8) fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
      return turns % 2 ? 'failed' : 'completed';
    }, { lastError: 'stream disconnected before completion: error sending request' }));
    expect(await runSolver([...args, '--max-turns', '10'], directory)).toBe(0);
    expect(host.delay.mock.calls.map(call => call[0])).toEqual([10_000, 10_000, 10_000, 10_000]);
    expect(host.officialGate).toHaveBeenCalledOnce();
  });

  it('reports authentication failures without retrying them', async () => {
    host.verify.mockImplementation(async request => failed(verified(request)));
    host.createSession.mockResolvedValueOnce({ threadId: 'fixture-thread', lastError: 'Invalid authentication',
      run: vi.fn().mockResolvedValue('failed'), close: vi.fn(), interrupt: vi.fn() });
    expect(await runSolver([...args, '--max-turns', '3'], directory)).toBe(1);
    expect(host.createSession).toHaveBeenCalledTimes(1);
    expect(host.delay).not.toHaveBeenCalled();
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'runtime_error', reason: 'math_model_authentication_failed' });
  });

  it('reports a missing provider key before model work and does not retry', async () => {
    host.createSession.mockRejectedValueOnce(new Error('math_model_api_key_missing:DEEPSEEK_API_KEY'));
    expect(await runSolver([...args, '--max-turns', '3'], directory)).toBe(1);
    expect(host.createSession).toHaveBeenCalledOnce();
    expect(host.delay).not.toHaveBeenCalled();
    expect(host.verify).not.toHaveBeenCalled();
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'runtime_error', reason: 'math_model_api_key_missing:DEEPSEEK_API_KEY' });
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

  it.each([false, true])('blocks an unreachable provider before dependencies or a model, startup=%s', async startup => {
    host.connectivity.mockResolvedValue({ status: 'unavailable', diagnostics: 'Provider connection failed. Check the proxy on this host.' });
    expect(await runSolver([...args, ...(startup ? ['--startup-only'] : [])], directory)).toBe(1);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({
      status: 'runtime_error', reason: 'math_codex_provider_unreachable', turns: 0,
    });
    expect(host.freeze).not.toHaveBeenCalled();
    expect(host.prepare).not.toHaveBeenCalled();
    expect(host.createSession).not.toHaveBeenCalled();
    expect(JSON.parse(fs.readFileSync(`${output}.runtime/provider-connectivity.json`, 'utf8')).status).toBe('unavailable');
  });

  it.each([false, true])('blocks a missing pinned package cache before preparation or a model, startup=%s', async startup => {
    fs.writeFileSync(path.join(project, 'lake-manifest.json'), JSON.stringify({ packages: [
      { name: 'mathlib', rev: 'a'.repeat(40), type: 'git' },
    ] }));
    git(workspace, ['add', '--', 'generated/p/lake-manifest.json']);
    commitFixture(workspace, 'Pinned dependency');
    expect(await runSolver([...args, ...(startup ? ['--startup-only'] : [])], directory)).toBe(1);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({
      status: 'runtime_error', reason: 'math_lake_packages_unavailable', turns: 0,
    });
    expect(host.freeze).not.toHaveBeenCalled();
    expect(host.prepare).not.toHaveBeenCalled();
    expect(host.createSession).not.toHaveBeenCalled();
    expect(console.log).toHaveBeenCalledWith(expect.stringContaining('No manifest-compatible Lake package cache'));
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
    const peers = new Set<string>(), ready = deferred();
    host.prepare.mockClear().mockImplementation(async input => {
      expect(fs.realpathSync(path.join(input.projectRoot, '.lake/packages'))).toBe(host.packages);
      if (input.projectRoot !== path.join(state.worktree, problem.projectRelative)) {
        peers.add(input.projectRoot);
        if (peers.size === 3) ready.resolve();
        await ready.promise;
      }
      return { exitCode: 0, timedOut: false, phases: [] };
    });
    expect(await runSolver([...startup, '--resume'], directory)).toBe(0);
    expect(host.prepare).toHaveBeenCalledTimes(4);
    expect(peers.size).toBe(3);
    expect(host.freeze.mock.calls.at(-1)![2].deadlineAt).toBeGreaterThan(Date.now());
    expect(host.createSession).not.toHaveBeenCalled();
  });

  it('reuses every worker read-only corpus on resume and rejects changed copies', async () => {
    host.packages = path.join(directory, 'packages');
    const library = path.join(host.packages, 'mathlib/Mathlib/Algebra/Basic.lean');
    fs.mkdirSync(path.dirname(library), { recursive: true });
    fs.writeFileSync(library, 'lemma library_helper : True := by trivial\n');
    fs.writeFileSync(path.join(host.packages, 'mathlib/lakefile.toml'), 'name = "mathlib"\n');
    fs.writeFileSync(path.join(project, 'lake-manifest.json'), JSON.stringify({ packages: [
      { name: 'mathlib', rev: 'a'.repeat(40), url: 'https://github.com/leanprover-community/mathlib4' },
    ] }));
    git(workspace, ['add', '--', 'generated/p/lake-manifest.json']);
    commitFixture(workspace, 'Pinned library');
    const startup = [...args, '--workers', '4', '--startup-only'];
    expect(await runSolver(startup, directory)).toBe(0);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    const files = state.workers.slice(1).map(worker => path.join(worker.worktree, 'generated/p/.lake/retrieval-corpus.json'));
    const snapshots = files.map(file => ({ bytes: fs.readFileSync(file), stat: fs.statSync(file) }));
    const writes = vi.spyOn(fs, 'writeFileSync');
    expect(await runSolver([...startup, '--resume'], directory)).toBe(0);
    for (const [index, file] of files.entries()) {
      expect(fs.readFileSync(file)).toEqual(snapshots[index].bytes);
      expect(fs.statSync(file)).toMatchObject({ ino: snapshots[index].stat.ino, mtimeMs: snapshots[index].stat.mtimeMs });
      expect(fs.statSync(file).mode & 0o777).toBe(0o400);
      expect(writes.mock.calls.some(call => call[0] === file)).toBe(false);
    }
    fs.chmodSync(files[1], 0o600);
    fs.appendFileSync(files[1], '\n');
    fs.chmodSync(files[1], 0o400);
    expect(await runSolver([...startup, '--resume'], directory)).toBe(1);
    expect(JSON.parse(fs.readFileSync(output, 'utf8')).reason).toBe('math_corpus_identity_changed');
    expect(host.createSession).not.toHaveBeenCalled();
  });

  it('checks a timed checkpoint and resumes with host diagnostics', async () => {
    host.verify.mockImplementationOnce(async request => failed(verified(request), { stdoutPreview: 'Submission.lean:4:1: error: unsolved goals' }));
    const messages: string[] = [];
    host.createSession.mockImplementation(session('fixture-thread', async (options, message) => {
      messages.push(message);
      if (messages.length === 1) return 'checkpoint';
      fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
      return 'completed';
    }));
    expect(await runSolver([...args, '--max-turns', '2'], directory)).toBe(0);
    expect(messages).toHaveLength(2);
    expect(messages[1]).toContain('unsolved goals');
    expect(host.createSession).toHaveBeenCalledTimes(1);
    expect(host.verify).toHaveBeenCalledTimes(3);
  });

  it.each(['throw', 'reject'])('reports a %s session close failure after proof selection', async mode => {
    const close = vi.fn(() => {
      const error = new Error('fixture_close_failed');
      if (mode === 'throw') throw error;
      return Promise.reject(error);
    });
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ threadId: 'fixture-thread',
      run: async () => {
        fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
        return 'completed';
      }, close, interrupt: vi.fn() }));
    expect(await runSolver(args, directory)).toBe(1);
    expect(close).toHaveBeenCalledOnce();
    expect(host.verify).toHaveBeenCalledOnce();
    expect(host.officialGate).not.toHaveBeenCalled();
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'runtime_error', reason: 'fixture_close_failed' });
  });

  it('preserves unrelated session errors as runtime failures', async () => {
    host.createSession.mockResolvedValueOnce({ threadId: 'fixture-thread', run: vi.fn().mockRejectedValue(new Error('unexpected failure')),
      close: vi.fn(), interrupt: vi.fn() });
    expect(await runSolver(args, directory)).toBe(1);
    expect(host.verify).not.toHaveBeenCalled();
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'runtime_error', reason: 'unexpected failure' });
  });

  it('keeps repeated unchanged rejections incomplete without recompiling the same commit', async () => {
    host.verify.mockImplementation(async request => failed(verified(request), { error: 'Lean exited with status 1.', stdoutPreview: unsolved }));
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
      ? failed(verified(request), { error: 'Lean exited with status 1.', stdoutPreview: 'Submission.lean:1:1: warning: unused variable\n' + leanError })
      : verified(request));
    host.createSession.mockImplementation(session('fixture-thread', async (options, message) => {
      messages.push(message);
      fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry',
        changed || messages.length === 3 ? `by\n  -- attempt ${messages.length}\n  trivial` : 'by trivial'));
      return 'completed';
    }));
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
      ? failed(verified(request), { stdoutPreview: `Submission.lean:${messages.length + 3}:1: error: unsolved goals\n⊢ ${messages.length === 2 ? 'False' : 'True'}` })
      : verified(request));
    host.createSession.mockImplementation(session('fixture-thread', async (options, message) => {
      messages.push(message);
      fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'),
        original.replaceAll('by sorry', `by\n  -- attempt ${messages.length}\n  trivial`));
      return 'completed';
    }));
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
    host.verify.mockImplementationOnce(async request => failed(verified(request), { error: 'open goals', stdoutPreview: diagnostic }));
    expect(await runSolver(args, directory)).toBe(4);
    const messages: string[] = [];
    host.createSession.mockImplementation(session(options => options.threadId!, async (_options, message) => {
      messages.push(message);
      return 'completed';
    }));
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
    host.packages = path.join(project, '.lake/packages');
    const library = path.join(project, '.lake/packages/mathlib/Mathlib/Order/Basic.lean');
    fs.mkdirSync(path.dirname(library), { recursive: true });
    fs.writeFileSync(library, 'lemma library_helper : True := by trivial');
    fs.writeFileSync(path.join(project, 'lake-manifest.json'), JSON.stringify({ packages: [
      { name: 'mathlib', rev: 'a'.repeat(40), url: 'https://github.com/leanprover-community/mathlib4' },
    ] }));
    git(workspace, ['add', '--force', '--', 'generated/p/.lake/packages', 'generated/p/lake-manifest.json']);
    commitFixture(workspace, 'Pinned library fixture');
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
    commitFixture(workspace, 'Pinned library');
    host.verify.mockImplementationOnce(async request => failed(verified(request)));
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
      commitFixture(worktree, 'Changed proof');
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

  it('roundtrips alternative proof routes through human export, queued edit, resume and canonical checks', async () => {
    const bridge: CooperativeTask = { id: 'bridge', kind: 'lemma', objective: 'Close the B route', dependsOn: ['b'],
      proofPath: 'Submission.lean', theoremName: 'Submission.bridge', type: 'True → True', revision: 0 };
    const tasks = [
      { ...planTasks()[0], status: 'paused' as const }, planTasks()[1], bridge,
      { ...planTasks()[2], dependsOn: [] }, planTasks()[3],
    ];
    const proofRoutes = [
      { id: 'route_a', targetTaskId: 'first', prerequisiteTaskIds: [], closingTaskId: 'a' },
      { id: 'route_b', targetTaskId: 'first', prerequisiteTaskIds: ['b'], closingTaskId: 'bridge' },
    ];
    let currentProofRoutes = proofRoutes;
    const goalAssignments: Extract<CooperativeAction, { kind: 'task' }>[] = [];
    configureCooperation(async (action, options, message) => {
      const file = path.join(options.workspace, 'generated/p/Submission.lean');
      if (action.kind === 'lead') fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'),
        '```math-plan\n' + JSON.stringify({ tasks, proofRoutes: currentProofRoutes }) + '\n```\n');
      else if (action.kind === 'task' && action.task.id === 'bridge') {
        expect(action.assignment.dependencies).toEqual([{ taskId: 'b', taskDigest: taskVersion(tasks[1]) }]);
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('theorem first',
          'lemma bridge : True → True := by intro _; exact b\ntheorem first'));
      } else if (action.kind === 'task' && action.task.id === 'first') {
        // A queued edit may arrive after a resumed worker has reserved its old
        // assignment. Let the host cancel that version before exercising B again.
        if (action.assignment.routeId === 'route_b') {
          await expect.poll(() => cooperationState().edits?.some((edit: any) => edit.id === 'route_roundtrip' && edit.status === 'applied')).toBe(true);
          return 'interrupted';
        }
        goalAssignments.push(action);
        expect(action.task.dependsOn).toEqual([]);
        expect(action.assignment.routeId).toBe('preferred_b');
        expect(action.assignment.dependencies).toEqual([
          { taskId: 'b', taskDigest: taskVersion(tasks[1]) }, { taskId: 'bridge', taskDigest: taskVersion(bridge) },
        ]);
        expect(message).toContain('Submission.bridge');
        expect(message).toContain('True → True');
        expect(fs.readFileSync(file, 'utf8')).toContain('lemma bridge : True → True');
        expect(host.officialGate).not.toHaveBeenCalled();
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('first : True := by sorry', 'first : True := by exact bridge b'));
      } else finishAssignment(action, options);
      return 'completed';
    });
    configureReferenceReports({ bridge: ['b'], first: ['bridge', 'b'], second: ['first', 'bridge', 'b'] });
    const parallelArgs = [...args, '--workers', '4', '--max-turns', '3'];
    const initialExit = await runSolver(parallelArgs, directory);
    expect(initialExit, fs.readFileSync(output, 'utf8')).toBe(4);
    const before = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(before.cooperation.tasks.filter((item: any) => item.task.kind === 'goal').map((item: any) => item.status))
      .toEqual(['pending', 'pending']);
    expect(before.cooperation.tasks.filter((item: any) => ['b', 'bridge'].includes(item.task.id)).map((item: any) => item.status))
      .toEqual(['integrated', 'integrated']);
    expect(before.cooperation.error).toBeUndefined();
    expect(before.check).toBeUndefined(); expect(goalAssignments).toHaveLength(0);
    expect(host.officialGate).not.toHaveBeenCalled();
    const { exportRunPlan } = await import('../src/solver/inspection');
    const { queueRunEdit } = await import('../src/solver/humanEdit');
    const exported = exportRunPlan(before);
    expect(exported.proofRoutes).toEqual(proofRoutes);
    const revisedRoutes = proofRoutes.map(route => route.id === 'route_b' ? { ...route, id: 'preferred_b' } : route);
    expect(await queueRunEdit(output, { ...exported, id: 'route_roundtrip', proofRoutes: revisedRoutes })).toMatchObject({ status: 'queued' });
    currentProofRoutes = revisedRoutes;
    const checksBeforeResume = host.verify.mock.calls.length;
    const resumedExit = await runSolver([...parallelArgs, '--resume', '--max-turns', '8'], directory);
    expect(resumedExit, fs.readFileSync(output, 'utf8')).toBe(0);
    const after = cooperationState();
    expect(after.proofRoutes).toEqual(revisedRoutes);
    expect(after.edits.find((edit: any) => edit.id === 'route_roundtrip')).toMatchObject({ status: 'applied' });
    expect(goalAssignments).toHaveLength(1);
    const original = after.tasks.find((item: any) => item.task.id === 'first');
    expect(original.alternativeRoutes).toEqual(revisedRoutes);
    expect(original.integratedCheck.references.tasks).toEqual(expect.arrayContaining([
      { taskId: 'bridge', taskDigest: taskVersion(bridge) }, { taskId: 'b', taskDigest: taskVersion(tasks[1]) },
    ]));
    expect(original.integratedCheck.references.proof).toContainEqual({ name: 'Submission.bridge', file: 'Submission.lean' });
    const delivery = after.deliveries.find((item: any) => item.taskId === 'first' && item.status === 'verified');
    expect(delivery.dependencies).toEqual(goalAssignments[0].assignment.dependencies);
    for (const receipt of original.integratedCheck.verification.results)
      expect(receipt.targetCommit).toBe(original.integratedCheck.verification.targetCommit);
    expect(host.verify.mock.calls[checksBeforeResume][0].items.map((item: any) => item.theoremName)).toContain('Submission.b');
    expect(host.officialGate).toHaveBeenCalledOnce();
  }, 20_000);

  it('reassigns a pending A draft to fresh B inputs while preserving the committed draft and notes', async () => {
    configureCooperation(); configureReferenceReports({ closing_b: ['b'] });
    const { markTaskAcceptance } = await import('../src/solver/tasks');
    const source = original.replace('theorem first', 'lemma a : True := by sorry\nlemma b : True := by trivial\n' +
      'lemma closing_a : True → True := by intro _; exact a\n' +
      'lemma closing_b : True → True := by intro _; exact b\ntheorem first');
    fs.writeFileSync(path.join(project, 'Submission.lean'), source);
    const canonical = commitSolverSources(problem, workspace);
    const tasks: CooperativeTask[] = [planTasks()[0], planTasks()[1], ...['a', 'b'].map(id => ({
      id: `closing_${id}`, kind: 'lemma' as const, objective: `Close route ${id}`, dependsOn: [id], revision: 0,
      proofPath: 'Submission.lean', theoremName: `Submission.closing_${id}`, type: 'True → True',
    })), { ...planTasks()[2], dependsOn: [] }, { ...planTasks()[3], status: 'paused' }];
    const proofRoutes = ['a', 'b'].map(id => ({ id: `route_${id}`, targetTaskId: 'first', prerequisiteTaskIds: [id], closingTaskId: `closing_${id}` }));
    const plan = parseCooperationPlan(problem, { tasks, proofRoutes });
    const records: any[] = plan.tasks.map(task => ({ task, status: ['a', 'closing_a'].includes(task.id) ? 'blocked' : 'pending', attempts: 1 }));
    for (const id of ['b', 'closing_b']) {
      const node = records.find(item => item.task.id === id);
      const assignment = { taskId: id, taskDigest: taskVersion(node.task), workerId: 'researcher-1', seedCommit: canonical };
      const proof = await checkTaskProof(problem, workspace, canonical, node.task, assignment, [], {}, new AbortController().signal, Infinity, [], 'fixture');
      expect(proof.passed).toBe(true);
      proof.references!.tasks = id === 'b' ? [] : [{ taskId: 'b', taskDigest: taskVersion(records[1].task) }];
      markTaskAcceptance(proof); node.status = 'integrated'; node.integratedCheck = proof;
    }
    await withSolverWorktree(workspace, canonical, async peerRoot => {
      const lead = { id: 'solver', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles } as const;
      const peer = { id: 'researcher-1', role: 'researcher', worktree: peerRoot, ownedFiles: problem.ownedFiles } as const;
      const file = path.join(peerRoot, 'generated/p/Submission.lean');
      fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('theorem first', 'lemma saved_a_support : True := by trivial\ntheorem first'));
      fs.writeFileSync(path.join(peerRoot, 'RESEARCH.md'), 'Saved A draft: the missing inference remains open.');
      const draftCommit = commitSolverSources(problem, peerRoot);
      const root = records.find(item => item.task.id === 'first');
      const previousAssignment = root.assignment = { taskId: 'first', taskDigest: taskVersion(root.task), workerId: peer.id,
        seedCommit: canonical, canonicalCommit: canonical, routeId: 'route_a', dependencies: ['a', 'closing_a'].map(id => ({
          taskId: id, taskDigest: taskVersion(records.find(item => item.task.id === id).task),
        })) };
      const state: any = { problem, runId: 'resumed-route-choice', turns: 0, phase: 'running', environmentDigest: 'fixture',
        workers: [lead, peer].map(worker => ({ ...worker, turns: 0, failures: [] })), cooperation: {
          tasks: records, groups: plan.groups.map(group => ({ group, turns: 0 })), proofRoutes, canonicalCommit: canonical,
        } };
      const cooperative = new CooperativeResearch({ state, workers: [lead, peer], access: new Map(), signal: new AbortController().signal,
        save: () => {}, emit: () => {}, modules: directSolverModules, exclusiveCheck: async check => check() });
      const action = await cooperative.next(peer, { maxTurns: Infinity, remainingMs: Infinity });
      expect(action?.kind).toBe('task');
      if (action?.kind !== 'task') throw new Error('missing_replacement_assignment');
      expect(action.assignment).not.toBe(previousAssignment);
      expect(action.assignment.routeId).toBe('route_b');
      expect(action.assignment.canonicalCommit).toBe(canonical);
      expect(action.assignment.dependencies).toEqual(['b', 'closing_b'].map(id => ({
        taskId: id, taskDigest: taskVersion(records.find(item => item.task.id === id).task),
      })));
      expect(fs.readFileSync(file, 'utf8')).toContain('lemma closing_b : True → True');
      expect(fs.readFileSync(path.join(peerRoot, 'RESEARCH.md'), 'utf8')).toContain('Saved A draft');
      expect(git(peerRoot, ['show', `${draftCommit}:generated/p/Submission.lean`])).toContain('lemma saved_a_support : True');
      expect(git(peerRoot, ['merge-base', '--is-ancestor', draftCommit, 'HEAD'])).toBe('');
      expect(cooperative.current(action)).toBe(true);
      expect(host.createSession).not.toHaveBeenCalled(); expect(host.officialGate).not.toHaveBeenCalled();
      cooperative.interrupted(peer, action); await cooperative.stop();
    });
  }, 20_000);

  it('parks repeated local blockers across a revision, isolates groups and reopens after a fresh dependency check', async () => {
    configureCooperation();
    const { routeAllowsTask } = await import('../src/solver/modules/search');
    const groups = [{ id: 'main', objective: 'Main route' }, { id: 'private', objective: 'Independent route' }];
    const tasks: CooperativeTask[] = [
      { id: 'root_research', kind: 'research', objective: 'Find the missing inference', dependsOn: ['b'], revision: 0, ownerId: 'researcher-1' },
      { ...planTasks()[1], status: 'paused' },
      ...planTasks().slice(2).map(task => ({ ...task, dependsOn: [], status: 'paused' as const })),
      { id: 'private_research', kind: 'research', objective: 'PRIVATE_INFERENCE', dependsOn: [], revision: 0,
        groupId: 'private', sharing: 'group', ownerId: 'researcher-2' },
    ];
    const plan = parseCooperationPlan(problem, { tasks, groups });
    await withSolverWorktree(workspace, problem.baseCommit, async peerRoot => {
      await withSolverWorktree(workspace, problem.baseCommit, async privateRoot => {
        const lead = { id: 'solver', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles } as const;
        const peer = { id: 'researcher-1', role: 'researcher', worktree: peerRoot, ownedFiles: problem.ownedFiles } as const;
        const other = { id: 'researcher-2', role: 'researcher', worktree: privateRoot, ownedFiles: problem.ownedFiles } as const;
        const state: any = { problem, runId: 'blocker-lifecycle', turns: 0, phase: 'running', environmentDigest: 'fixture',
          workers: [lead, peer, other].map(worker => ({ ...worker, turns: 0, failures: [] })),
          cooperation: { tasks: plan.tasks.map(task => ({ task, status: 'pending', attempts: 0 })),
            groups: plan.groups.map(group => ({ group, turns: 0 })) } };
        const events: { event: string; [key: string]: unknown }[] = [];
        const cooperative = new CooperativeResearch({ state, workers: [lead, peer, other],
          access: new Map([[lead.id, { environment: {}, retrievalRoot: workspace }]]), signal: new AbortController().signal,
          save: () => {}, emit: (event, details) => events.push({ event, ...details }), modules: directSolverModules,
          exclusiveCheck: async check => check() });
        const budget = { maxTurns: Infinity, remainingMs: Infinity };
        const first = await cooperative.next(peer, budget);
        expect(first?.kind).toBe('task');
        if (first?.kind !== 'task') throw new Error('missing_root_assignment');
        cooperative.activate(peer, first, async () => {}, async () => {});
        const report = (action: Extract<CooperativeAction, { kind: 'task' }>, worktree: string, id: string, mechanism: string) =>
          fs.appendFileSync(path.join(worktree, assignmentDeliveryFile(action.assignment)), JSON.stringify({ id, kind: 'progress',
            summary: 'The local inference still needs its declared mathematical input.', blockers: [{ mechanism,
              scope: 'local-inference', reopenOn: [{ kind: 'dependency-checked', taskId: 'b' }] }] }) + '\n');
        report(first, peerRoot, 'first_report', 'same-missing-bridge');
        await cooperative.pulse(peer.id);
        expect(state.cooperation.blockers[0]).toMatchObject({ count: 1, status: 'open', evidenceStatus: 'advisory' });
        const blockerId = state.cooperation.blockers[0].id;
        const privateAction = await cooperative.next(other, budget);
        expect(privateAction?.kind).toBe('task');
        if (privateAction?.kind !== 'task') throw new Error('missing_private_assignment');
        cooperative.activate(other, privateAction, async () => {}, async () => {});
        fs.appendFileSync(path.join(privateRoot, assignmentDeliveryFile(privateAction.assignment)), JSON.stringify({ id: 'private_report',
          summary: 'PRIVATE_EVIDENCE', blockers: [{ mechanism: 'PRIVATE_BLOCKER', scope: 'private-inference' }] }) + '\n');
        await cooperative.pulse(other.id);
        expect(state.cooperation.blockers.find((blocker: any) => blocker.id === blockerId).count).toBe(1);
        const revisedTasks = plan.tasks.map(task => task.id === first.task.id ? { ...task, revision: 1 } : task);
        fs.appendFileSync(path.join(path.dirname(workspace), 'edits.jsonl'), JSON.stringify({ id: 'same_math_revision',
          baseVersion: state.cooperation.planVersion, tasks: revisedTasks, groups: plan.groups }) + '\n');
        await cooperative.pulse(); cooperative.deactivate(peer);
        const second = await cooperative.next(peer, budget);
        expect(second?.kind).toBe('task');
        if (second?.kind !== 'task') throw new Error('missing_revised_assignment');
        expect(second.task.revision).toBe(1);
        cooperative.activate(peer, second, async () => {}, async () => {});
        report(second, peerRoot, 'second_report', 'same-missing-bridge');
        await cooperative.pulse(peer.id);
        const obstruction = state.cooperation.blockers.find((blocker: any) => blocker.id === blockerId);
        expect(obstruction).toMatchObject({ count: 2, status: 'parked', taskDigest: taskVersion(second.task) });
        const root = state.cooperation.tasks.find((item: any) => item.task.id === second.task.id);
        expect(routeAllowsTask(root.task, state.cooperation.tasks, state.cooperation.groups)).toBe(false);
        expect(cooperative.contextState(privateAction).blockers?.map(blocker => blocker.mechanism)).toEqual(['PRIVATE_BLOCKER']);
        expect(cooperative.contextState(second).blockers?.map(blocker => blocker.mechanism)).toEqual(['same-missing-bridge']);
        expect(fs.readFileSync(path.join(peerRoot, 'COOPERATION.json'), 'utf8')).not.toContain('PRIVATE_BLOCKER');
        cooperative.interrupted(peer, second); cooperative.deactivate(peer);
        const activeTasks = revisedTasks.map(task => task.id === 'b' ? { ...task, status: 'active' as const } : task);
        fs.appendFileSync(path.join(path.dirname(workspace), 'edits.jsonl'), JSON.stringify({ id: 'prove_local_input',
          baseVersion: state.cooperation.planVersion, tasks: activeTasks, groups: plan.groups }) + '\n');
        await cooperative.pulse();
        expect(obstruction.status).toBe('parked');
        const dependency = await cooperative.next(peer, budget);
        expect(dependency?.kind === 'task' && dependency.task.id).toBe('b');
        if (dependency?.kind !== 'task') throw new Error('missing_dependency_assignment');
        cooperative.activate(peer, dependency, async () => {}, async () => {});
        finishAssignment(dependency, { workspace: peerRoot } as MathAgentOptions);
        await cooperative.deliver(peer, dependency, commitSolverSources(problem, peerRoot));
        cooperative.deactivate(peer);
        expect(obstruction).toMatchObject({ status: 'reopened', reopenedReason: 'dependency-checked', count: 2 });
        expect(root.routeParking).toEqual([]);
        expect(routeAllowsTask(root.task, state.cooperation.tasks, state.cooperation.groups)).toBe(true);
        expect(events).toContainEqual(expect.objectContaining({ event: 'route_parked', blockerId }));
        expect(events).toContainEqual(expect.objectContaining({ event: 'route_reopened', blockerId }));
        expect(state.cooperation.tasks.filter((item: any) => item.task.kind === 'goal').every((item: any) => item.status === 'pending')).toBe(true);
        expect(host.officialGate).not.toHaveBeenCalled();
        cooperative.interrupted(other, privateAction); cooperative.deactivate(other); await cooperative.stop();
      });
    });
  }, 20_000);
});
