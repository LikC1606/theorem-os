import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, describe, expect, it } from 'vitest';
import { bootstrapLeanTask, readLeanTaskReceipt, LEAN_TASK_SOURCE_MAX_BYTES } from '../src/math/leanTask';
import { LOCAL_EXAMPLE_TOOLCHAIN } from '../src/math/localExample';
import { getLeanTaskEnvironment, type LeanTaskEnvironment } from '../src/math/leanTaskEnvironment';
import { canonicalMathProblemStatementPayloads } from '../src/math/contracts';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { assertSolverSources, git, readSolverProblem } from '../src/solver/problem';

const source = [
  'namespace User',
  '',
  'def marker : Nat := 0',
  '',
  'theorem left (n : Nat) : n + 0 = n := by sorry',
  '',
  'namespace Nested',
  '',
  'lemma right (n : Nat) : 0 + n = n := by sorry',
  '',
  'end Nested',
  'end User',
  '',
].join('\n');
const task = 'Prove both addition identities.';
const roots: string[] = [];
afterEach(() => { for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });
function rootDirectory() {
  const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'theoremos-lean-task-')));
  roots.push(root);
  return root;
}
function fixture(environment?: LeanTaskEnvironment) {
  const root = rootDirectory();
  const receipt = bootstrapLeanTask(path.join(root, 'workspace'), { source, task, environment });
  const submission = path.join(receipt.projectRoot, 'Submission.lean');
  return { root, receipt, submission };
}
function saveReceipt(receipt: ReturnType<typeof bootstrapLeanTask>, changes: Record<string, unknown>) {
  fs.writeFileSync(receipt.activeProblemPath, JSON.stringify({ ...receipt, ...changes }));
}

describe('user-provided Lean task bootstrap', () => {
  it('freezes all named theorem and lemma targets, definitions, namespaces and a package-free toolchain', () => {
    const { receipt } = fixture();
    const reread = readLeanTaskReceipt(receipt.activeProblemPath);
    expect(reread).toEqual(receipt);
    expect(receipt.kind).toBe('lean-task');
    expect(receipt.environment).toBe('standard');
    expect(receipt.environmentDigest).toBe(getLeanTaskEnvironment('standard').dependencyDigest);
    expect(receipt.projectRoot).toBe(path.join(receipt.workspaceRoot, 'generated/problem'));
    expect(receipt.publicObligations.map(item => item.name)).toEqual(['User.left', 'User.Nested.right']);
    expect(receipt.declarations.map(item => [item.name, item.kind])).toEqual([
      ['User.marker', 'definition'], ['User.left', 'theorem'], ['User.Nested.right', 'theorem'],
    ]);
    expect(receipt.solverOwnedFiles).toEqual(['Submission.lean']);
    expect(fs.readFileSync(path.join(receipt.projectRoot, 'lean-toolchain'), 'utf8')).toBe(`${LOCAL_EXAMPLE_TOOLCHAIN}\n`);
    expect(JSON.parse(fs.readFileSync(path.join(receipt.projectRoot, 'lake-manifest.json'), 'utf8')).packages).toEqual([]);
    const problem = readSolverProblem(receipt.workspaceRoot, receipt.activeProblemPath);
    expect(problem.kind).toBe('lean-task');
    expect(problem.baseCommit).toBe(receipt.baseCommit);
    expect(problem.targets.map(item => item.theoremName)).toEqual(['User.left', 'User.Nested.right']);
    expect(() => assertSolverSources(problem, receipt.workspaceRoot)).not.toThrow();
  });

  it('does not execute source commands while preparing a task', () => {
    const root = rootDirectory();
    const sentinel = path.join(root, 'executed');
    const untrusted = `#eval IO.FS.writeFile ${JSON.stringify(sentinel)} "executed"\n\ntheorem proof : True := by sorry\n`;
    const receipt = bootstrapLeanTask(path.join(root, 'workspace'), { source: untrusted, task });
    expect(fs.existsSync(sentinel)).toBe(false);
    expect(readLeanTaskReceipt(receipt.activeProblemPath).contract.formalStatement).toBe(untrusted);
  });

  it('prepares Mathlib tasks with every dependency pinned in the trusted runtime environment', () => {
    const root = rootDirectory();
    const input = `import Mathlib\n\n${source}`;
    const receipt = bootstrapLeanTask(path.join(root, 'workspace'), { source: input, task, environment: 'mathlib' });
    const environment = getLeanTaskEnvironment('mathlib');
    const manifest = JSON.parse(fs.readFileSync(path.join(receipt.projectRoot, 'lake-manifest.json'), 'utf8'));
    expect(receipt.environment).toBe('mathlib');
    expect(receipt.environmentDigest).toBe(environment.dependencyDigest);
    expect(environment.mathlibRevision).toBe('db584cd6d46c92f209a44c0f1c829460d327499d');
    expect(environment.toolchain).toBe(LOCAL_EXAMPLE_TOOLCHAIN);
    expect(manifest.packages).toHaveLength(9);
    expect(manifest.packages.find((item: { name: string }) => item.name === 'mathlib')).toMatchObject({
      type: 'git', url: 'https://github.com/leanprover-community/mathlib4.git', rev: environment.mathlibRevision,
      inputRev: environment.mathlibRevision, inherited: false,
    });
    expect(manifest.packages.every((item: { rev: string }) => /^[0-9a-f]{40}$/u.test(item.rev))).toBe(true);
    expect(manifest.packages.filter((item: { inherited: boolean }) => item.inherited)).toHaveLength(8);
    for (const [relative, contents] of Object.entries(environment.files))
      expect(fs.readFileSync(path.join(receipt.projectRoot, relative), 'utf8')).toBe(contents);
    expect(fs.existsSync(path.join(receipt.projectRoot, '.lake/packages'))).toBe(false);
    expect(readLeanTaskReceipt(receipt.activeProblemPath)).toEqual(receipt);
    const problem = readSolverProblem(receipt.workspaceRoot, receipt.activeProblemPath);
    expect(problem.contract.formalStatement).toBe(input);
    expect(() => assertSolverSources(problem, receipt.workspaceRoot)).not.toThrow();
  });

  it.each(['standard', 'mathlib'] as const)('binds %s receipt selection and digest to the committed environment', environment => {
    const { receipt } = fixture(environment);
    const replacement = environment === 'standard' ? 'mathlib' : 'standard';
    saveReceipt(receipt, { environment: replacement,
      environmentDigest: getLeanTaskEnvironment(replacement).dependencyDigest,
      toolchain: getLeanTaskEnvironment(replacement).toolchain });
    expect(() => readLeanTaskReceipt(receipt.activeProblemPath)).toThrow('lean_task_environment_changed');
    saveReceipt(receipt, { environmentDigest: '0'.repeat(64) });
    expect(() => readLeanTaskReceipt(receipt.activeProblemPath)).toThrow('lean_task_environment_changed');
  });

  it('rejects replacing pinned Mathlib dependencies while preserving their config paths', () => {
    const { receipt } = fixture('mathlib');
    const manifestFile = path.join(receipt.projectRoot, 'lake-manifest.json');
    const manifest = JSON.parse(fs.readFileSync(manifestFile, 'utf8'));
    manifest.packages[0].rev = '0'.repeat(40);
    fs.writeFileSync(manifestFile, JSON.stringify(manifest));
    expect(() => readLeanTaskReceipt(receipt.activeProblemPath)).toThrow('lean_task_protected_file_changed:lake-manifest.json');
  });

  it('keeps legacy standard-library receipts verifiable against their original seed bytes', () => {
    const { receipt } = fixture();
    const message = 'TheoremOS Lean task seed\n\n' + JSON.stringify({ schema: 'theorem-os.lean-task-seed.v1',
      sourceHash: mathDigest(source), task });
    git(receipt.workspaceRoot, ['-c', 'user.name=Test', '-c', 'user.email=test@localhost',
      'commit', '--amend', '--no-gpg-sign', '--quiet', '--cleanup=verbatim', '-m', message]);
    const { environment: _environment, environmentDigest: _digest, ...legacy } = receipt;
    legacy.baseCommit = git(receipt.workspaceRoot, ['rev-parse', 'HEAD']);
    fs.writeFileSync(receipt.activeProblemPath, JSON.stringify(legacy));
    expect(readLeanTaskReceipt(receipt.activeProblemPath)).toEqual(legacy);
    expect(() => readSolverProblem(receipt.workspaceRoot, receipt.activeProblemPath)).not.toThrow();
  });

  it('does not let a new receipt drop or change its environment binding', () => {
    const { receipt } = fixture();
    const { environment: _environment, environmentDigest: _digest, ...unbound } = receipt;
    fs.writeFileSync(receipt.activeProblemPath, JSON.stringify(unbound));
    expect(() => readLeanTaskReceipt(receipt.activeProblemPath)).toThrow('lean_task_environment_changed');
    saveReceipt(receipt, { environmentDigest: '0'.repeat(64) });
    expect(() => readLeanTaskReceipt(receipt.activeProblemPath)).toThrow('lean_task_environment_changed');
    saveReceipt(receipt, { environment: 'mathlib' });
    expect(() => readLeanTaskReceipt(receipt.activeProblemPath)).toThrow('lean_task_environment_changed');
    saveReceipt(receipt, { toolchain: 'leanprover/lean4:v1.0.0' });
    expect(() => readLeanTaskReceipt(receipt.activeProblemPath)).toThrow('lean_task_environment_changed');
  });

  it('rejects caller-controlled dependency URLs and manifests before creating a workspace', () => {
    for (const extra of [{ environment: 'custom' }, { repositoryUrl: 'https://example.com/mathlib.git' },
      { manifest: { packages: [] } }, { toolchain: 'leanprover/lean4:v1.0.0' }]) {
      const workspace = path.join(rootDirectory(), 'workspace');
      expect(() => bootstrapLeanTask(workspace, { source, task, ...extra } as never)).toThrow();
      expect(fs.existsSync(workspace)).toBe(false);
    }
  });

  it.each([
    ['', task], ['def marker : Nat := 0\n', task], ['-- theorem hidden : True := by sorry\n', task],
    ['example : True := by sorry\n', task], ['theorem unfinished : True', task], [source, '  '],
    [`${source}\0`, task], [`${source}\ud800`, task], [' '.repeat(LEAN_TASK_SOURCE_MAX_BYTES + 1), task],
    ['namespace A\ntheorem same : True := by sorry\nend A\nnamespace B\nlemma same : True := by sorry\nend B\n', task],
  ])('rejects invalid, missing or ambiguous declarations without creating a workspace', (text, description) => {
    const workspace = path.join(rootDirectory(), 'workspace');
    expect(() => bootstrapLeanTask(workspace, { source: text, task: description })).toThrow();
    expect(fs.existsSync(workspace)).toBe(false);
  });

  it('refuses an existing or symlinked workspace', () => {
    const { root, receipt } = fixture();
    expect(() => bootstrapLeanTask(receipt.workspaceRoot, { source, task })).toThrow('already exists');
    const alias = path.join(root, 'alias');
    fs.symlinkSync(root, alias, 'dir');
    expect(() => bootstrapLeanTask(path.join(alias, 'workspace-2'), { source, task })).toThrow('math_path_invalid');
  });

  it.each(['workspaceRoot', 'projectRoot', 'activeProblemPath', 'trustedFiles', 'solverOwnedFiles', 'publicObligations', 'declarations'])(
    'rejects a changed receipt %s', key => {
      const { receipt } = fixture();
      saveReceipt(receipt, { [key]: key.endsWith('Root') || key.endsWith('Path') ? path.dirname(receipt.workspaceRoot) : [] });
      expect(() => readLeanTaskReceipt(receipt.activeProblemPath)).toThrow('lean_task_identity_changed');
    });

  it('rejects a modified statement or task even when replacement hashes are recomputed', () => {
    const { receipt } = fixture();
    const formalStatement = source.replace('n + 0 = n', 'True');
    const informalStatement = 'Prove a different and easier statement.';
    const payloads = canonicalMathProblemStatementPayloads({ informalStatement, formalStatement, assumptions: [] });
    saveReceipt(receipt, { contract: { ...receipt.contract, formalStatement, informalStatement,
      statementHash: mathDigest(payloads.informal), leanStatementHash: mathDigest(payloads.lean) } });
    expect(() => readLeanTaskReceipt(receipt.activeProblemPath)).toThrow('lean_task_identity_changed');
  });

  it.each(['Challenge.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json'])(
    'rejects a changed protected file %s', relative => {
      const { receipt } = fixture();
      fs.appendFileSync(path.join(receipt.projectRoot, relative), '\n');
      expect(() => readLeanTaskReceipt(receipt.activeProblemPath)).toThrow(`lean_task_protected_file_changed:${relative}`);
    });

  it('rejects symlinked protected files, solver files and receipts', () => {
    const { root, receipt, submission } = fixture();
    const original = path.join(root, 'original.lean');
    fs.writeFileSync(original, source);
    fs.unlinkSync(submission);
    fs.symlinkSync(original, submission);
    expect(() => readLeanTaskReceipt(receipt.activeProblemPath)).toThrow('math_path_invalid');
    fs.unlinkSync(submission);
    fs.writeFileSync(submission, source);
    const challenge = path.join(receipt.projectRoot, 'Challenge.lean');
    fs.unlinkSync(challenge);
    fs.symlinkSync(original, challenge);
    expect(() => readLeanTaskReceipt(receipt.activeProblemPath)).toThrow('math_path_invalid');
    const alias = path.join(root, 'receipt.json');
    fs.symlinkSync(receipt.activeProblemPath, alias);
    expect(() => readLeanTaskReceipt(alias)).toThrow('math_path_invalid');
  });

  it('rejects a newer commit substituted for the existing seed commit', () => {
    const { receipt, submission } = fixture();
    fs.writeFileSync(submission, source.replaceAll('by sorry', 'by rfl'));
    git(receipt.workspaceRoot, ['add', '--', 'generated/problem/Submission.lean']);
    git(receipt.workspaceRoot, ['-c', 'user.name=Test', '-c', 'user.email=test@localhost',
      'commit', '--no-gpg-sign', '--quiet', '-m', 'Candidate proof']);
    expect(readLeanTaskReceipt(receipt.activeProblemPath).baseCommit).toBe(receipt.baseCommit);
    saveReceipt(receipt, { baseCommit: git(receipt.workspaceRoot, ['rev-parse', 'HEAD']) });
    expect(() => readLeanTaskReceipt(receipt.activeProblemPath)).toThrow('lean_task_identity_changed');
  });

  it('allows proof bodies to change and keeps source guards anchored to the seed on reread', () => {
    const { receipt, submission } = fixture();
    const problem = readSolverProblem(receipt.workspaceRoot, receipt.activeProblemPath);
    fs.writeFileSync(submission, source.replace('by sorry', 'by rfl').replace('by sorry', 'by exact Nat.zero_add n'));
    expect(() => assertSolverSources(problem, receipt.workspaceRoot)).not.toThrow();
    expect(() => readSolverProblem(receipt.workspaceRoot, receipt.activeProblemPath)).not.toThrow();
    fs.writeFileSync(submission, source.replace('n + 0 = n', 'True'));
    expect(() => assertSolverSources(problem, receipt.workspaceRoot)).toThrow('math_original_declaration_changed');
    expect(() => readSolverProblem(receipt.workspaceRoot, receipt.activeProblemPath)).toThrow('math_problem_target_file_ambiguous');
  });

  it.each([
    ['def marker : Nat := 0', 'def marker : Nat := 1', 'math_original_declaration_changed'],
    ['def marker : Nat := 0', 'def marker : Bool := false', 'math_original_declaration_changed'],
    ['namespace User', 'namespace Other', 'math_original_context_changed'],
  ])('rejects a modified frozen declaration or context: %s', (before, after, error) => {
    const { receipt, submission } = fixture();
    const problem = readSolverProblem(receipt.workspaceRoot, receipt.activeProblemPath);
    fs.writeFileSync(submission, source.replace(before, after));
    expect(() => assertSolverSources(problem, receipt.workspaceRoot)).toThrow(error);
    expect(() => readSolverProblem(receipt.workspaceRoot, receipt.activeProblemPath)).toThrow(error);
  });
});
