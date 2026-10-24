import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { applyTaskChanges, taskChanges } from '../src/solver/cooperativeProof';
import { committedSource, commitSolverSources, git, withSolverWorktree, type SolverProblem } from '../src/solver/problem';
import { taskVersion, type CooperativeTask } from '../src/solver/tasks';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState, type LocalExample } from './helpers/solver';
import { receiptBatch } from './helpers/verifier';

const host = vi.hoisted(() => ({ verify: vi.fn(), environment: vi.fn(), createSession: vi.fn() }));
vi.mock('../src/math/verifier', async original => ({
  ...await original<typeof import('../src/math/verifier')>(), checkManyFormalVerifications: host.verify,
  formalVerificationToolIdentity: () => 'exact-source-fixture-tools',
}));
vi.mock('../src/math/mathProofEnvironment', async original => ({
  ...await original<typeof import('../src/math/mathProofEnvironment')>(), resolveMathProofEnvironment: host.environment,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.createSession }));

describe('exact source task integration', () => {
  let example: LocalExample, directory: string, workspace: string, project: string, problem: SolverProblem;
  let seed: string, candidate: string, delivery: string, task: CooperativeTask;
  beforeEach(() => {
    example = localExample('exact-source-integration-');
    ({ directory, workspace, problem } = example); project = example.receipt.projectRoot;
    seed = fs.readFileSync(path.join(project, 'Submission.lean'), 'utf8');
    candidate = seed.replace('theorem add_zero',
      'def preservedText : String := "alpha\\n\\n  beta"\n\n\nlemma helper : True := by\n  trivial\n\n\ntheorem add_zero');
    task = { id: 'goal', kind: 'goal', objective: 'Prove the original target.', proofPath: problem.targets[0]!.proofPath,
      theoremName: problem.targets[0]!.theoremName, dependsOn: [], revision: 0 };
    host.verify.mockReset().mockImplementation(async request => receiptBatch(request,
      { sessionId: 'exact-source-fixture', receiptId: index => `fixture-${request.targetCommit}-${index}` }));
    host.environment.mockReset().mockReturnValue(undefined);
    host.createSession.mockReset().mockImplementation(() => { throw new Error('fixture_real_models_forbidden'); });
  });
  afterEach(() => {
    expect(host.createSession).not.toHaveBeenCalled();
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });
  const save = (seedCommit = problem.baseCommit) => {
    fs.writeFileSync(path.join(project, 'Submission.lean'), candidate);
    delivery = commitSolverSources(problem, workspace);
    return taskChanges(problem, workspace, delivery, task, { seedCommit });
  };

  it('keeps every source byte when the current owned sources equal the delivery seed', async () => {
    const changes = save();
    await withSolverWorktree(workspace, problem.baseCommit, async checkout => {
      const file = path.join(checkout, problem.projectRelative, 'Submission.lean');
      applyTaskChanges(problem, checkout, changes);
      expect(fs.readFileSync(file, 'utf8')).not.toBe(candidate);
      fs.writeFileSync(file, seed);
      applyTaskChanges(problem, checkout, changes, [], [], { commit: delivery, seedCommit: problem.baseCommit });
      expect(fs.readFileSync(file)).toEqual(Buffer.from(candidate));
    });
  });

  it('retains concurrent peer declarations through the original merge', async () => {
    const changes = save();
    await withSolverWorktree(workspace, problem.baseCommit, async checkout => {
      const file = path.join(checkout, problem.projectRelative, 'Submission.lean');
      fs.writeFileSync(file, seed.replace('theorem add_zero', 'lemma peer : True := by trivial\ntheorem add_zero'));
      applyTaskChanges(problem, checkout, changes, [], [], { commit: delivery, seedCommit: problem.baseCommit });
      const merged = fs.readFileSync(file, 'utf8');
      expect(merged).toContain('lemma peer : True := by trivial');
      expect(merged).toContain('lemma helper : True := by');
    });
  });

  it('checks all owned files before replacing the complete delivery', async () => {
    const helper = 'Helpers.lean', helperFile = path.join(project, helper);
    fs.writeFileSync(helperFile, 'def count : Nat := 1\n');
    problem = { ...problem, ownedFiles: [...problem.ownedFiles, helper] };
    const seedCommit = commitSolverSources(problem, workspace);
    const changes = save(seedCommit);
    await withSolverWorktree(workspace, seedCommit, async checkout => {
      fs.writeFileSync(path.join(checkout, problem.projectRelative, helper), 'def count : Nat := 2\n');
      applyTaskChanges(problem, checkout, changes, [], [], { commit: delivery, seedCommit });
      expect(fs.readFileSync(path.join(checkout, problem.projectRelative, helper), 'utf8')).toBe('def count : Nat := 2\n');
    });
  });

  it('does not import an omitted candidate change through the complete-source path', async () => {
    const changes = save().filter(change => change.name !== 'preservedText');
    await withSolverWorktree(workspace, problem.baseCommit, async checkout => {
      applyTaskChanges(problem, checkout, changes, [], [], { commit: delivery, seedCommit: problem.baseCommit });
      expect(fs.readFileSync(path.join(checkout, problem.projectRelative, 'Submission.lean'), 'utf8')).not.toContain('def preservedText');
    });
  });

  it('requires imported modules to match the authorized patch', async () => {
    const module = 'Mathlib.Data.Nat.Basic';
    candidate = `import ${module}\n` + candidate;
    const changes = save();
    await withSolverWorktree(workspace, problem.baseCommit, async checkout => {
      applyTaskChanges(problem, checkout, changes, [], [], { commit: delivery, seedCommit: problem.baseCommit });
      expect(fs.readFileSync(path.join(checkout, problem.projectRelative, 'Submission.lean'), 'utf8')).not.toContain(`import ${module}`);
    });
  });

  it('uses the original merge when discharging assumptions and preserves the checked dependency', async () => {
    const file = path.join(project, 'Submission.lean');
    seed = seed.replace('theorem add_zero', 'lemma dependency : True := by trivial\ntheorem add_zero');
    fs.writeFileSync(file, seed);
    const seedCommit = commitSolverSources(problem, workspace);
    candidate = seed.replace('dependency : True := by trivial', 'dependency : True := by sorry')
      .replace('theorem add_zero', 'lemma consumer : True := by exact dependency\n\n\ntheorem add_zero');
    const changes = save(seedCommit).filter(change => change.name !== 'dependency');
    const dependency: CooperativeTask = { id: 'dependency', kind: 'lemma', objective: 'Prove the premise.', type: 'True',
      proofPath: 'Submission.lean', theoremName: 'Tutorial.dependency', dependsOn: [], revision: 0 };
    await withSolverWorktree(workspace, seedCommit, async checkout => {
      applyTaskChanges(problem, checkout, changes, [], [dependency], { commit: delivery, seedCommit });
      const merged = fs.readFileSync(path.join(checkout, problem.projectRelative, 'Submission.lean'), 'utf8');
      expect(merged).toContain('lemma dependency : True := by trivial');
      expect(merged).not.toContain('dependency : True := by sorry');
      expect(merged).toContain('lemma consumer : True := by exact dependency');
    });
  });

  it.each(['statement', 'context', 'unowned'] as const)('retains the %s source guard on the complete-source path', async kind => {
    if (kind === 'statement') candidate = candidate.replace('n + 0 = n', 'n + 0 = 0');
    if (kind === 'context') candidate = candidate.replace('namespace Tutorial', 'namespace Tutorial\nopen Nat');
    fs.writeFileSync(path.join(project, 'Submission.lean'), candidate);
    git(workspace, ['add', '--', `${problem.projectRelative}/Submission.lean`]);
    git(workspace, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--quiet', '--no-gpg-sign', '-m', 'Untrusted source guard fixture']);
    delivery = git(workspace, ['rev-parse', 'HEAD']);
    const changes = taskChanges(problem, workspace, delivery, undefined, { seedCommit: problem.baseCommit });
    await withSolverWorktree(workspace, problem.baseCommit, async checkout => {
      if (kind === 'unowned') fs.writeFileSync(path.join(checkout, 'outside.txt'), 'outside ownership\n');
      expect(() => applyTaskChanges(problem, checkout, changes, [], [], { commit: delivery, seedCommit: problem.baseCommit }))
        .toThrow(kind === 'statement' ? 'math_original_declaration_changed' : kind === 'context' ? 'math_original_context_changed' : 'math_source_outside_ownership');
    });
  });

  it('preserves the delivery projection and receipt through the actual single-task integration caller', async () => {
    host.environment.mockReturnValue({ identity: 'sealed-fixture' });
    const worker = peerWorker(example, 'engineer'), lead = leadWorker(problem, workspace);
    const env = { PATH: '/usr/bin:/bin', DEEPSCIENTIST_MATH_ENV_FILE: path.join(directory, 'missing.env') };
    fs.writeFileSync(path.join(worker.worktree, problem.projectRelative, 'Submission.lean'), candidate);
    const lake = path.join(worker.worktree, problem.projectRelative, '.lake');
    fs.mkdirSync(lake, { recursive: true });
    fs.writeFileSync(path.join(lake, 'package-overrides.json'), '{"path":"/engineer/packages"}\n');
    delivery = commitSolverSources(problem, worker.worktree);
    const assignment = { taskId: task.id, taskDigest: taskVersion(task), workerId: worker.id, seedCommit: problem.baseCommit };
    const node = { task, assignment, status: 'running' as const, attempts: 1 };
    const state = solverState(problem, workspace, { runId: 'exact-source-fixture', phase: 'running',
      cooperation: { canonicalCommit: problem.baseCommit, tasks: [node] } });
    const controller = new AbortController();
    const cooperative = cooperativeResearch({ state, workers: [lead, worker], retrievalRoot: directory,
      signal: controller.signal, access: new Map([lead, worker].map(item => [item.id, { environment: env, retrievalRoot: directory }])) });
    const cacheChecks = vi.spyOn((cooperative as any).taskProofCache, 'check');
    try {
      const proof = await (cooperative as any).check(task, assignment, worker.worktree, delivery);
      Object.assign(node, { status: 'delivered', proof });
      await (cooperative as any).integrateNow(node);
      const integrated = state.cooperation!.tasks[0]!;
      expect(integrated.status).toBe('integrated');
      expect(committedSource(workspace, state.cooperation!.canonicalCommit!, `${problem.projectRelative}/Submission.lean`)).toBe(candidate);
      expect(host.verify).toHaveBeenCalledOnce();
      expect(integrated.integratedCheck!.verification).toEqual(proof.verification);
      expect(cacheChecks).toHaveBeenCalledTimes(2);
      expect(cacheChecks.mock.calls[1]![0]).toBe(cacheChecks.mock.calls[0]![0]);
      expect(integrated.integratedCheck!.projectionReuse).toMatchObject({ checkedProjectionCommit: proof.verification.targetCommit });
    } finally { controller.abort(); await cooperative.stop(); }
  });
});
