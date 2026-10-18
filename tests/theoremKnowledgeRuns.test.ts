import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { afterEach, describe, expect, it } from 'vitest';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';
import { hashMathFormalSourceDeclaration } from '../src/math/leanSource';
import { writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import type { TaskProof } from '../src/solver/cooperativeProof';
import { taskVersion, type CooperativeTask } from '../src/solver/tasks';
import { buildTheoremKnowledge, locateKnowledgeDeclaration } from '../src/solver/theoremKnowledge';
import { importKnowledgeRuns } from '../src/solver/theoremKnowledgeRuns';

const roots: string[] = [];
afterEach(() => { for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });

function fixture() {
  const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'theorem-knowledge-runs-'))); roots.push(root);
  const repository = path.join(root, 'repository'), projectRelative = 'generated/fixture', project = path.join(repository, projectRelative);
  fs.mkdirSync(path.join(project, 'Submission'), { recursive: true });
  const git = (...args: string[]) => execFileSync('git', ['-C', repository, ...args], { encoding: 'utf8' }).trim();
  const original = 'namespace Submission\ntheorem original : True := by sorry\nend Submission\n';
  const helpers = 'namespace Submission.Helpers\nlemma reusable : True := by trivial\nend Submission.Helpers\n';
  const trusted: Record<string, string> = { 'Challenge.lean': 'def frozenNumber : Nat := 1\n',
    'lakefile.toml': 'name = "fixture"\n', 'lake-manifest.json': '{"packages":[]}\n', 'lean-toolchain': 'leanprover/lean4:v4.31.0\n',
    'config.json': '{"privateFixture":"omitted-config"}\n', 'Solution.lean': 'protected-fixture-never-imported\n',
    '.env': 'private-fixture-never-imported\n' };
  for (const [file, source] of Object.entries(trusted)) fs.writeFileSync(path.join(project, file), source);
  fs.writeFileSync(path.join(project, 'Submission.lean'), original);
  fs.writeFileSync(path.join(project, 'Submission/Helpers.lean'), helpers);
  git('init', '--quiet');
  const commit = () => {
    git('add', '--', '.'); git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost',
      'commit', '--quiet', '--no-gpg-sign', '-m', 'fixture'); return git('rev-parse', 'HEAD');
  };
  const sourceCommit = commit();
  fs.writeFileSync(path.join(project, 'Submission.lean'), '-- Receipt projection removes the unproved original.\n');
  const checkedCommit = commit();
  const task: CooperativeTask = { id: 'reusable', kind: 'lemma', objective: 'A reusable checked helper', dependsOn: [], revision: 0,
    proofPath: 'Submission/Helpers.lean', theoremName: 'Submission.Helpers.reusable', type: 'True', premises: ['Preserve the frozen context'] };
  const sourceAt = (commit: string, file: string) => execFileSync('git', ['-C', repository, 'show', `${commit}:${projectRelative}/${file}`], { encoding: 'utf8' });
  const ownedFiles = ['Submission.lean', 'Submission/Helpers.lean'];
  const proofFor = (target: CooperativeTask, source = sourceCommit, checked = checkedCommit): TaskProof => {
    const version = taskVersion(target);
    return { commit: source, sourceDigest: mathDigest(canonicalMathJson(ownedFiles.map(file => [file, mathDigest(sourceAt(source, file))]))),
      taskDigest: version, seedCommit: sourceCommit, changes: [], passed: true,
      verification: { schema: 'deepscientist.mathematics.verification-batch/v1', status: 'kernel_verified',
        targetCommit: checked, sessionId: 'fixture', events: [], startedAt: 1, checkedAt: 2, durationMs: 1,
        results: [{ status: 'kernel_verified', targetCommit: checked, receiptId: `receipt-${source}-${version}`,
          proofPath: target.proofPath, theoremName: target.theoremName, statementHash: version, leanStatementHash: version,
          claim: 'statement', sourceDeclarationHash: hashMathFormalSourceDeclaration(sourceAt(source, target.proofPath!), target.theoremName!),
        } as TaskProof['verification']['results'][number]] } };
  };
  const proof = proofFor(task);
  const state: SolverRunState = { schema: 'deepscientist.math.solver.v1', runId: 'fixture-run',
    worktree: path.join(root, 'unavailable-original-worktree'), model: 'none', effort: 'none', phase: 'finished', turns: 1,
    taskDigest: mathDigest('fixture run'), buildDigest: mathDigest('fixture build'), environmentDigest: mathDigest('fixture environment'),
    evaluatorDigest: mathDigest('fixture evaluator'), problem: { kind: 'example', workspace: repository, projectRelative,
      baseCommit: sourceCommit, receiptDigest: mathDigest('fixture problem receipt'), activeProblemPath: path.join(repository, 'active-problem.json'),
      ownedFiles, trustedFiles: Object.fromEntries(Object.entries(trusted).map(([file, text]) => [file, mathDigest(text)])),
      declarations: {}, sourceStructure: {}, targets: [{ proofPath: 'Submission.lean', theoremName: 'Submission.original',
        declarationHash: hashMathFormalSourceDeclaration(original, 'Submission.original')! }],
      contract: { problemId: 'fixture', informalStatement: 'Prove the original claim', formalStatement: original, assumptions: [],
        knownTraps: [], acceptanceCriteria: [], officialVerificationCommand: 'lake build', statementHash: mathDigest('original informal'),
        leanStatementHash: mathDigest('original formal') } },
    cooperation: { tasks: [{ task, status: 'integrated', attempts: 1, integratedCheck: proof }] } };
  const stateFile = path.join(root, 'state.json');
  const save = () => { writeSolverRunState(stateFile, state); return stateFile; };
  return { root, repository, project, task, proof, state, stateFile, save, sourceCommit, checkedCommit, helpers,
    commit, proofFor, sourceAt };
}

describe('recorded theorem run import', () => {
  it.each([false, true])('binds the exact original goal even when an earlier raw name collides (wrong receipt: %s)', wrongReceipt => {
    const f = fixture();
    const source = 'namespace Other\nlemma Submission.original : False → False := by exact id\nend Other\n' +
      'namespace Submission\ntheorem original : True := by trivial\nend Submission\n';
    fs.writeFileSync(path.join(f.project, 'Submission.lean'), source);
    const committed = f.commit();
    const goal: CooperativeTask = { id: 'goal', kind: 'goal', objective: 'Original goal', dependsOn: [], revision: 0,
      proofPath: 'Submission.lean', theoremName: 'Submission.original' };
    const proof = f.proofFor(goal, committed, committed);
    const exactHash = mathDigest(locateKnowledgeDeclaration(source, 'Submission.original').declarationType);
    const target = f.state.problem.targets[0]!;
    target.declarationHash = exactHash;
    if (!wrongReceipt) proof.verification.results[0]!.sourceDeclarationHash = exactHash;
    f.state.cooperation!.tasks = [{ task: goal, status: 'integrated', attempts: 1, integratedCheck: proof }];
    const imported = importKnowledgeRuns([f.save()]);
    if (wrongReceipt) {
      expect(imported.candidates).toEqual([]);
      expect(imported.skipped[0]!.reason).toBe('math_knowledge_run_declaration_receipt_mismatch');
    } else {
      expect(imported.skipped).toEqual([]);
      expect(imported.candidates[0]).toMatchObject({ name: 'Submission.original', type: 'original : True', typeKind: 'source-header' });
    }
  });

  it('captures immutable sources, separate checking provenance and unavailable dependency coverage', () => {
    const f = fixture();
    fs.writeFileSync(path.join(f.project, 'Submission/Helpers.lean'), 'mutable-content-must-not-be-imported\n');
    const imported = importKnowledgeRuns([f.save()]);
    expect(imported.skipped).toEqual([]); expect(imported.candidates).toHaveLength(1);
    const candidate = imported.candidates[0]!;
    expect(candidate).toMatchObject({ name: f.task.theoremName, type: 'True', typeKind: 'closed-task-type', kind: 'lemma',
      premises: f.task.premises, dependencies: { statement: [], proof: [], tasks: [], coverage: 'unavailable' },
      provenance: { kind: 'solver-check', runId: f.state.runId, taskId: f.task.id, taskDigest: taskVersion(f.task),
        source: f.stateFile, sourceDigest: mathDigest(fs.readFileSync(f.stateFile)), sourceCommit: f.sourceCommit,
        checkedCommit: f.checkedCommit, environmentDigest: f.state.environmentDigest, problemReceiptDigest: f.state.problem.receiptDigest } });
    expect(candidate.files['Submission/Helpers.lean']).toBe(f.helpers);
    expect(candidate.files['Challenge.lean']).toContain('frozenNumber');
    expect(Object.keys(candidate.files)).toEqual(['Challenge.lean', 'Submission.lean', 'Submission/Helpers.lean',
      'lake-manifest.json', 'lakefile.toml', 'lean-toolchain']);
    expect(JSON.stringify(imported)).not.toContain('private-fixture-never-imported');
    expect(JSON.stringify(imported)).not.toContain('protected-fixture-never-imported');
    expect(buildTheoremKnowledge(imported.candidates)).toMatchObject({ evidence: 'recorded-not-replayed', requiresFreshCheck: true });
  });

  it('retains historical proofs without scheduling fields and preserves versions sharing a theorem name', () => {
    const f = fixture(), revised = { ...f.task, revision: 1, type: 'True ∧ True' };
    fs.writeFileSync(path.join(f.project, 'Submission/Helpers.lean'),
      'namespace Submission.Helpers\nlemma reusable : True ∧ True := by constructor <;> trivial\nend Submission.Helpers\n');
    const newer = f.commit();
    f.state.cooperation!.history = [{ task: f.task, integratedCheck: f.proof }];
    f.state.cooperation!.tasks = [{ task: revised, attempts: 1, status: 'integrated', integratedCheck: f.proofFor(revised, newer, newer) }];
    const imported = importKnowledgeRuns([f.save()]);
    expect(imported.skipped).toEqual([]); expect(imported.candidates).toHaveLength(2);
    expect(imported.candidates.map(item => item.type).sort()).toEqual(['True', 'True ∧ True']);
    const base = buildTheoremKnowledge(imported.candidates);
    expect(base.entries).toHaveLength(2); expect(new Set(base.entries.map(item => item.contextDigest)).size).toBe(2);
  });

  it('preserves actual dependency metadata when available', () => {
    const f = fixture();
    f.proof.references = { sourceCommit: f.sourceCommit, environmentDigest: f.state.environmentDigest,
      contextDigest: mathDigest('context'), root: { name: f.task.theoremName!, file: f.task.proofPath! }, inputs: [],
      statement: [{ file: 'Challenge.lean', name: 'frozenNumber' }], proof: [{ file: 'Challenge.lean', name: 'frozenNumber' }],
      tasks: [{ taskId: 'prior-helper', taskDigest: mathDigest('prior helper') }] };
    const imported = importKnowledgeRuns([f.save()]);
    expect(imported.skipped).toEqual([]);
    expect(imported.candidates[0]!.dependencies).toEqual({ statement: f.proof.references.statement,
      proof: f.proof.references.proof, tasks: f.proof.references.tasks, coverage: 'recorded' });
  });

  it.each(['theoremName', 'proofPath', 'statementHash', 'leanStatementHash', 'claim', 'targetCommit'] as const)
  ('rejects a mismatched receipt %s', field => {
    const f = fixture();
    Object.assign(f.proof.verification.results[0]!, { [field]: 'mismatch' });
    const imported = importKnowledgeRuns([f.save()]);
    expect(imported.candidates).toEqual([]);
    expect(imported.skipped[0]!.reason).toMatch(/math_knowledge_run_(receipt_mismatch|proof_unverified)/u);
  });

  it.each(['source', 'header', 'trusted'] as const)('rejects a mismatched %s binding', binding => {
    const f = fixture();
    if (binding === 'source') f.proof.sourceDigest = mathDigest('different committed sources');
    if (binding === 'header') f.proof.verification.results[0]!.sourceDeclarationHash = mathDigest('different header');
    if (binding === 'trusted') f.state.problem = { ...f.state.problem,
      trustedFiles: { ...f.state.problem.trustedFiles, 'Challenge.lean': mathDigest('different frozen source') } };
    const imported = importKnowledgeRuns([f.save()]);
    expect(imported.candidates).toEqual([]);
    expect(imported.skipped[0]!.reason).toBe({ source: 'math_knowledge_run_source_digest_mismatch',
      header: 'math_knowledge_run_declaration_receipt_mismatch', trusted: 'math_knowledge_run_trusted_source_mismatch' }[binding]);
  });

  it.each(['conditional', 'stale'] as const)('rejects a %s proof', kind => {
    const f = fixture();
    if (kind === 'conditional') f.proof.conditions = [{ taskId: 'missing', taskDigest: mathDigest('missing') }];
    else f.state.cooperation!.tasks[0]!.task = { ...f.task, type: 'False' };
    const imported = importKnowledgeRuns([f.save()]);
    expect(imported.candidates).toEqual([]); expect(imported.skipped[0]!.reason).toBe(`math_knowledge_run_proof_${kind}`);
  });

  it.each(['Solution.lean', '../outside.lean', '.env', 'Submission/.private.lean'])
  ('refuses forbidden owned source %s before capturing context', file => {
    const f = fixture();
    f.state.problem = { ...f.state.problem, ownedFiles: [...f.state.problem.ownedFiles, file] };
    const imported = importKnowledgeRuns([f.save()]);
    expect(imported.candidates).toEqual([]); expect(imported.skipped[0]!.reason).toBe('math_knowledge_run_forbidden_source');
  });

  it('requires committed objects and does not fall back to mutable worktree files', () => {
    const f = fixture(); f.proof.commit = 'f'.repeat(40);
    const imported = importKnowledgeRuns([f.save()]);
    expect(imported.candidates).toEqual([]); expect(imported.skipped[0]!.reason).toBe('math_knowledge_run_source_unavailable');
  });

  it('can recover committed bytes from a worker repository when other repositories are unavailable', () => {
    const f = fixture();
    f.state.problem = { ...f.state.problem, workspace: path.join(f.root, 'unavailable-workspace') };
    f.state.workers = [{ id: 'worker', role: 'researcher', worktree: f.repository, phase: 'finished', turns: 1 }];
    const imported = importKnowledgeRuns([f.save()]);
    expect(imported.skipped).toEqual([]); expect(imported.candidates[0]!.files['Submission/Helpers.lean']).toBe(f.helpers);
  });

  it('uses the exact original goal header instead of claiming a closed task type', () => {
    const f = fixture(), source = f.sourceAt(f.sourceCommit, 'Submission.lean');
    const goal: CooperativeTask = { id: 'goal', kind: 'goal', objective: 'Original goal', dependsOn: [], revision: 0,
      proofPath: 'Submission.lean', theoremName: 'Submission.original' };
    fs.writeFileSync(path.join(f.project, 'Submission.lean'), source.replace('sorry', 'trivial'));
    const proved = f.commit();
    f.state.cooperation!.tasks = [{ task: goal, status: 'integrated', attempts: 1, integratedCheck: f.proofFor(goal, proved, proved) }];
    const imported = importKnowledgeRuns([f.save()]);
    expect(imported.skipped).toEqual([]);
    expect(imported.candidates[0]).toMatchObject({ kind: 'goal', typeKind: 'source-header', type: 'original : True' });
  });

  it('reports malformed explicit state files and continues with valid inputs', () => {
    const f = fixture(), other = path.join(f.root, 'invalid'); fs.mkdirSync(other);
    const invalid = path.join(other, 'state.json'); fs.writeFileSync(invalid, '{"schema":"unknown"}');
    const imported = importKnowledgeRuns([invalid, f.save()]);
    expect(imported.candidates).toHaveLength(1);
    expect(imported.skipped).toEqual([{ source: invalid, reason: 'math_knowledge_run_state_invalid' }]);
  });
});
