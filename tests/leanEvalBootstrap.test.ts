import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import crypto from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { assertLeanEvalBootstrapEligibility, bootstrapLeanEvalProblem, readLeanEvalBootstrapReceipt, runLeanEvalOfficialGate,
  runPersistedLeanEvalOfficialGate, type LeanEvalBootstrapResult } from '../src/math/leanEvalBootstrap';
import { LEAN_EVAL_LEADERBOARD_URL, type LeanEvalCatalogProblem } from '../src/math/leanEvalCatalogAdapter';
import type { MathematicsVerifierBatchRequest } from '../src/math/verifier';

const host = vi.hoisted(() => ({ commit: '', catalog: {} as unknown, verify: vi.fn(), compare: vi.fn() }));
vi.mock('../src/math/leanEvalCatalogAdapter', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/leanEvalCatalogAdapter')>(),
  get LEAN_EVAL_BENCHMARK_COMMIT() { return host.commit; },
  readLeanEvalCatalog: () => host.catalog,
}));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify,
  runOfficialComparator: host.compare,
}));
vi.mock('../src/math/receiptAttestation', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/receiptAttestation')>(),
  readMathematicsReceiptSecret: () => 'fixture-secret',
}));

describe('Lean-Eval bootstrap without planning state', () => {
  let directory: string;
  let repositoryRoot: string;
  let bootstrapped: LeanEvalBootstrapResult;
  const declarations = ['def seed : Nat := by sorry', 'theorem first : True := by sorry',
    'theorem second : seed = seed := by sorry'];
  const git = (...args: string[]) => execFileSync('git', ['-C', repositoryRoot, ...args],
    { encoding: 'utf8', maxBuffer: 1024 * 1024 }).trim();
  beforeEach(async () => {
    vi.clearAllMocks();
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'lean-eval-bootstrap-')));
    repositoryRoot = path.join(directory, 'benchmark');
    const project = path.join(repositoryRoot, 'generated/p');
    fs.mkdirSync(project, { recursive: true });
    const files: Record<string, string> = {
      'Challenge.lean': `namespace Challenge\n${declarations.join('\n')}\nend Challenge\n`,
      'Submission.lean': `namespace Submission\n${declarations.join('\n')}\nend Submission\n`,
      'Solution.lean': 'protected reference solution',
      'WorkspaceTest.lean': '-- protected official test',
      'config.json': JSON.stringify({ challenge_module: 'Challenge', solution_module: 'Solution',
        theorem_names: ['first', 'second'], definition_names: ['seed'],
        permitted_axioms: ['Classical.choice', 'Quot.sound', 'propext'], enable_nanoda: true }),
      'holes.json': JSON.stringify({ id: 'p', module: 'Challenge', holes: declarations.map((body, index) => ({
        name: ['seed', 'first', 'second'][index], basename: ['seed', 'first', 'second'][index],
        kind: index === 0 ? 'def' : 'theorem', body })) }),
      'lakefile.toml': 'name = "p"\ntestDriver = "workspace_test"\ndefaultTargets = ["Challenge", "Solution", "Submission"]\n',
      'lean-toolchain': 'leanprover/lean4:v4.31.0',
      'Submission/Helper.lean': 'namespace Submission\ntheorem helper : True := by trivial\nend Submission\n',
      'Public/Support.lean': '-- public support',
      'Private/Solution.lean': 'protected nested reference solution',
      'Private/WorkspaceTest.lean': 'protected nested official test',
      'notes.txt': 'unneeded benchmark prose',
    };
    for (const [name, content] of Object.entries(files)) {
      fs.mkdirSync(path.dirname(path.join(project, name)), { recursive: true });
      fs.writeFileSync(path.join(project, name), content);
    }
    fs.writeFileSync(path.join(repositoryRoot, 'lake-manifest.json'), JSON.stringify({
      name: 'lean-eval', schemaVersion: '1.2.0', packages: [], pinnedRevision: 'fixture',
    }));
    git('init', '--quiet');
    git('remote', 'add', 'origin', 'https://github.com/leanprover/lean-eval');
    git('add', '.');
    git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--quiet', '-m', 'baseline');
    host.commit = git('rev-parse', 'HEAD');
    const problem = { id: 'p', title: 'Fixture', generatedPath: 'generated/p', statementRevision: 1,
      eligible: true, eligibilityReasons: [] } as unknown as LeanEvalCatalogProblem;
    host.catalog = { benchmarkCommit: host.commit, catalogHash: 'a'.repeat(64), problems: [problem] };
    host.verify.mockImplementation(async (request: MathematicsVerifierBatchRequest) => ({
      targetCommit: request.targetCommit, status: 'kernel_verified', results: request.items.map(item => ({
        ...item, targetCommit: request.targetCommit, status: 'kernel_verified', verifier: 'lean-kernel',
        receiptId: `local:${item.id}`, sourceDeclarationHash: item.expectedSourceDeclarationHash,
        theoremDeclarationHash: 'b'.repeat(64), proofHash: 'c'.repeat(64), goalsRemaining: 0,
        sorryCount: 0, admitCount: 0, axioms: [],
      })),
    }));
    host.compare.mockImplementation(async request => ({ status: 'official_verified',
      targetCommit: request.targetCommit, command: request.command, exitCode: 0, timedOut: false,
      stdoutSha256: 'd'.repeat(64), stderrSha256: 'e'.repeat(64), durationMs: 1, checkedAt: Date.now(),
      officialManifestId: request.officialManifest.manifestId, officialManifestHash: request.officialManifest.manifestHash,
      officialRepositoryUrl: request.officialManifest.repositoryUrl, officialBaselineCommit: host.commit,
      benchmarkAdapterId: 'lean-eval', benchmarkAdapterVersion: '1',
    }));
    bootstrapped = await bootstrapLeanEvalProblem({ repositoryRoot, problemId: 'p', credits: [],
      workspaceRoot: path.join(directory, 'solver') });
    const proof = path.join(bootstrapped.receipt.projectRoot, 'Submission.lean');
    fs.writeFileSync(proof, fs.readFileSync(proof, 'utf8').replace('by sorry', 'by exact 0')
      .replace('by sorry', 'by trivial').replace('by sorry', 'by rfl'));
  });
  afterEach(() => { fs.rmSync(directory, { recursive: true, force: true }); });

  function makeOfficialReceipt() {
    const leaderboard = { credits: [], generatedAt: 1 };
    const receipt = { ...bootstrapped.receipt, leaderboardSource: LEAN_EVAL_LEADERBOARD_URL,
      leaderboardHash: crypto.createHash('sha256').update('[]').digest('hex'), leaderboardGeneratedAt: 1 };
    fs.writeFileSync(receipt.activeProblemPath, JSON.stringify(receipt));
    return { activeProblemPath: receipt.activeProblemPath, repositoryRoot, fetchLeaderboard: async () => leaderboard };
  }

  it('allows archived introductory problems only in benchmark mode', () => {
    const problem = { eligible: false, eligibilityReasons: ['not_in_v1', 'inactive', 'hidden'] };
    expect(() => assertLeanEvalBootstrapEligibility(problem, 'benchmark')).not.toThrow();
    expect(() => assertLeanEvalBootstrapEligibility(problem, 'official')).toThrow('not eligible');
    expect(() => assertLeanEvalBootstrapEligibility({ eligible: false, eligibilityReasons: ['unknown'] }, 'benchmark'))
      .toThrow('not eligible');
  });

  it('resumes archived benchmark problems and still runs independent proof and comparator checks', async () => {
    const options = makeOfficialReceipt();
    const receipt = JSON.parse(fs.readFileSync(options.activeProblemPath, 'utf8'));
    const leaderboard = { credits: [{ problemId: 'p', statementRevision: 1 }], generatedAt: 2 };
    receipt.evaluationMode = 'benchmark';
    receipt.leaderboardHash = crypto.createHash('sha256').update(JSON.stringify(leaderboard.credits)).digest('hex');
    receipt.leaderboardGeneratedAt = leaderboard.generatedAt;
    fs.writeFileSync(options.activeProblemPath, JSON.stringify(receipt));
    Object.assign(bootstrapped.problem, { eligible: false, eligibilityReasons: ['not_in_v1', 'inactive', 'hidden'] });
    const result = await runPersistedLeanEvalOfficialGate({ ...options,
      fetchLeaderboard: async () => leaderboard,
    });
    expect(result.comparison.status).toBe('official_verified');
    expect(host.verify).toHaveBeenCalledOnce();
    expect(host.compare).toHaveBeenCalledOnce();
  });

  it('still rejects a credited problem in official mode', async () => {
    await expect(runLeanEvalOfficialGate({ ...bootstrapped, receipt: {
      ...bootstrapped.receipt, leaderboardSource: LEAN_EVAL_LEADERBOARD_URL,
    } }, { fetchLeaderboard: async () => ({ credits: [{ problemId: 'p', statementRevision: 1 }], generatedAt: 2 }) }))
      .rejects.toThrow('accepted leaderboard credit');
    expect(host.verify).not.toHaveBeenCalled();
    expect(host.compare).not.toHaveBeenCalled();
  });

  it('bootstraps and resumes every public obligation from the pinned binding', async () => {
    expect(bootstrapped.receipt).not.toHaveProperty('routeFingerprint');
    expect(bootstrapped.receipt).not.toHaveProperty('executionPolicy');
    expect(fs.existsSync(path.join(bootstrapped.receipt.projectRoot, 'Solution.lean'))).toBe(false);
    expect(bootstrapped.receipt.solverOwnedFiles).toEqual(['Submission.lean', 'Submission/Helper.lean']);
    expect(bootstrapped.receipt.trustedFiles).toContain('Public/Support.lean');
    for (const file of ['Private/Solution.lean', 'Private/WorkspaceTest.lean', 'notes.txt']) {
      expect(fs.existsSync(path.join(bootstrapped.receipt.projectRoot, file))).toBe(false);
    }
    expect(JSON.parse(fs.readFileSync(path.join(bootstrapped.receipt.projectRoot, 'lake-manifest.json'), 'utf8')))
      .toMatchObject({ name: 'p', version: '1.2.0', lakeDir: '.lake', packagesDir: '.lake/packages', pinnedRevision: 'fixture' });
    expect(bootstrapped.receipt.trustedFiles).toContain('lake-manifest.json');
    expect(execFileSync('git', ['-C', bootstrapped.receipt.workspaceRoot, 'show', 'HEAD:generated/p/lake-manifest.json'],
      { encoding: 'utf8' })).toContain('pinnedRevision');
    expect(bootstrapped.receipt.publicObligations?.map(item => item.name)).toEqual(['seed', 'first', 'second']);
    expect(readLeanEvalBootstrapReceipt(bootstrapped.receipt.activeProblemPath).publicObligations)
      .toEqual(bootstrapped.receipt.publicObligations);
    const result = await runPersistedLeanEvalOfficialGate(makeOfficialReceipt());
    expect(host.verify.mock.calls[0][0].projectRoot).toBe(path.join(bootstrapped.receipt.verifierProjectRoot!, 'generated/p'));
    expect(host.verify.mock.calls[0][0].items.map(item => item.proofPath)).toEqual(['Submission.lean', 'Submission.lean', 'Submission.lean']);
    expect(host.verify.mock.calls[0][1]).toMatchObject({ prepareLocalDependencies: true });
    expect(host.verify.mock.calls[0][0].items.map(item => item.theoremName)).toEqual(['Submission.seed', 'Submission.first', 'Submission.second']);
    expect(result.officialGateReceipt).toMatchObject({ status: 'official_verified', theoremName: 'Submission.second' });
    expect(result.officialGateReceipt).not.toHaveProperty('routeFingerprint');
    expect(host.compare).toHaveBeenCalledOnce();
    expect(host.compare.mock.calls[0][0].projectRoot).toBe(path.join(bootstrapped.receipt.verifierProjectRoot!, 'generated/p'));
    expect(host.compare.mock.calls[0][1]).toMatchObject({ prepareLocalDependencies: true });
    expect(JSON.parse(fs.readFileSync(path.join(bootstrapped.receipt.verifierProjectRoot!, 'generated/p/lake-manifest.json'), 'utf8')))
      .toMatchObject({ name: 'p', packagesDir: '.lake/packages', pinnedRevision: 'fixture' });
  });

  it('checks flattened candidate names while retaining the original obligation identities', async () => {
    const result = await runLeanEvalOfficialGate({ ...bootstrapped, binding: { ...bootstrapped.binding,
      publicObligations: bootstrapped.binding.publicObligations.map(hole => ({ ...hole,
        name: `LeanEval.Combinatorics.${hole.name}` })) } });
    expect(host.verify.mock.calls[0][0].items.map(item => [item.id, item.theoremName])).toEqual([
      ['LeanEval.Combinatorics.seed', 'Submission.seed'],
      ['LeanEval.Combinatorics.first', 'Submission.first'],
      ['LeanEval.Combinatorics.second', 'Submission.second'],
    ]);
    expect(result.officialGateReceipt).toMatchObject({ status: 'official_verified', theoremName: 'Submission.second' });
    expect(host.compare).toHaveBeenCalledOnce();
  });

  it.each(['trustedFiles', 'solverOwnedFiles'] as const)('rejects a changed %s list on resume', async field => {
    const options = makeOfficialReceipt();
    const receipt = JSON.parse(fs.readFileSync(options.activeProblemPath, 'utf8'));
    receipt[field].pop();
    fs.writeFileSync(options.activeProblemPath, JSON.stringify(receipt));
    await expect(runPersistedLeanEvalOfficialGate(options)).rejects.toThrow('file ownership');
    expect(host.verify).not.toHaveBeenCalled();
  });

  it.each(['symlink', 'hardlink'])('rejects a %s bootstrap receipt', kind => {
    const receipt = bootstrapped.receipt.activeProblemPath;
    const alias = path.join(directory, 'receipt-alias.json');
    if (kind === 'symlink') {
      fs.renameSync(receipt, alias);
      fs.symlinkSync(alias, receipt);
    } else fs.linkSync(receipt, alias);
    expect(() => readLeanEvalBootstrapReceipt(receipt)).toThrow();
  });

  it('rejects a detached worktree path through a directory symlink', () => {
    const receipt = bootstrapped.receipt;
    const verifier = receipt.verifierProjectRoot!;
    const alias = path.join(directory, 'verifier-alias');
    fs.renameSync(verifier, alias);
    fs.symlinkSync(alias, verifier, 'dir');
    expect(() => readLeanEvalBootstrapReceipt(receipt.activeProblemPath)).toThrow('math_path_invalid');
  });

  it.each(['missing', 'renamed', 'changed hash'])('rejects %s persisted obligations before verification', async change => {
    const options = makeOfficialReceipt();
    const receipt = JSON.parse(fs.readFileSync(options.activeProblemPath, 'utf8'));
    if (change === 'missing') receipt.publicObligations.pop();
    if (change === 'renamed') receipt.publicObligations[0].name = 'other';
    if (change === 'changed hash') receipt.publicObligations[0].declarationHash = 'f'.repeat(64);
    fs.writeFileSync(options.activeProblemPath, JSON.stringify(receipt));
    await expect(runPersistedLeanEvalOfficialGate(options)).rejects.toThrow('public obligations');
    expect(host.verify).not.toHaveBeenCalled();
    expect(host.compare).not.toHaveBeenCalled();
  });

  it('blocks official comparison if any independent obligation lacks a receipt', async () => {
    const complete = host.verify.getMockImplementation()!;
    host.verify.mockImplementation(async request => {
      const batch = await complete(request);
      return { ...batch, results: batch.results.filter(result => result.theoremName !== 'Submission.first') };
    });
    const result = await runLeanEvalOfficialGate(bootstrapped);
    expect(result.comparison.status).toBe('blocked');
    expect(host.compare).not.toHaveBeenCalled();
  });

  it('reconstructs obligations for receipts predating the public obligation list', async () => {
    const options = makeOfficialReceipt();
    const receipt = JSON.parse(fs.readFileSync(options.activeProblemPath, 'utf8'));
    delete receipt.publicObligations;
    receipt.routeFingerprint = 'lean-eval:legacy';
    receipt.executionPolicy = { obsolete: true };
    fs.writeFileSync(options.activeProblemPath, JSON.stringify(receipt));
    const result = await runPersistedLeanEvalOfficialGate(options);
    expect(host.verify.mock.calls[0][0].items).toHaveLength(3);
    expect(result.officialGateReceipt?.routeFingerprint).toBe('lean-eval:legacy');
  });
});
