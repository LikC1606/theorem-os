import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { LEAN_EVAL_BENCHMARK_COMMIT } from '../src/math/leanEvalCatalogAdapter';
import type { MathematicsVerifierBatchRequest } from '../src/math/verifier';
import { inspectScopedLeanDeclarations } from '../src/math/leanSource';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import { readCooperationPlan, type CooperativeResearch } from '../src/solver/cooperation';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { committedSource, commitSolverSources, git, readSolverProblem, type SolverProblem } from '../src/solver/problem';
import type { CooperativeAction, CooperativeTask } from '../src/solver/tasks';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';
import { failedBatch, verifiedBatch } from './helpers/verifier';

const host = vi.hoisted(() => ({ verify: vi.fn(), createSession: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify,
  resolveMathematicsLakePackagesCache: () => undefined,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.createSession }));

describe('conditional proof declaration ownership', () => {
  let directory: string, workspace: string, problem: SolverProblem, state: SolverRunState;
  let workers: ResearchWorker[], instances: { cooperative: CooperativeResearch; controller: AbortController }[];
  let cooperative: CooperativeResearch;
  let requiredParentHelpers: { file: string; name: string }[];
  let projections: { theoremName: string; files: Record<string, string> }[];
  const budget = { maxTurns: Infinity, remainingMs: Infinity };
  type TaskAction = Extract<CooperativeAction, { kind: 'task' }>;

  const sourcePath = (worker: ResearchWorker) => path.join(worker.worktree, problem.projectRelative, 'Submission.lean');
  const source = (worker: ResearchWorker) => fs.readFileSync(sourcePath(worker), 'utf8');
  const canonicalSource = () => committedSource(workspace, state.cooperation!.canonicalCommit!,
    `${problem.projectRelative}/Submission.lean`);
  const node = (id: string) => state.cooperation!.tasks.find(node => node.task.id === id)!;
  const create = () => {
    const controller = new AbortController();
    const cooperative = cooperativeResearch({ state, workers, retrievalRoot: directory, signal: controller.signal });
    instances.push({ cooperative, controller });
    return cooperative;
  };
  const assigned = async (worker: ResearchWorker) => {
    const action = await cooperative.next(worker, budget);
    expect(action?.kind).toBe('task');
    if (action?.kind !== 'task') throw new Error('fixture_missing_task');
    expect(cooperative.started(worker, action)).toBe(true);
    return action;
  };
  const deliverParent = async (declaration = '', files: Record<string, string> = {}, helper = 'support', imports: string[] = []) => {
    const parent = await assigned(workers[2]);
    expect(parent.task.id).toBe('goal_0');
    node('goal_0').feedback = 'The previous parent proof failed.';
    fs.writeFileSync(sourcePath(workers[2]), imports.map(module => `import ${module}\n`).join('') + source(workers[2])
      .replace('theorem add_zero', declaration + 'lemma support : True := by trivial\ntheorem add_zero')
      .replace('n + 0 = n := by sorry', `n + 0 = n := by\n  have h : True := And.left (And.intro child ${helper})\n  rfl`));
    for (const [file, content] of Object.entries(files))
      fs.writeFileSync(path.join(workers[2].worktree, problem.projectRelative, file), content);
    await cooperative.deliver(workers[2], parent, commitSolverSources(problem, workers[2].worktree));
    expect(node('goal_0').status).toBe('conditional');
    expect(node('goal_0').feedback).toBeUndefined();
    return parent;
  };
  const deliverChild = async (child: TaskAction) => {
    fs.writeFileSync(sourcePath(workers[1]), source(workers[1])
      .replace('theorem add_zero', 'lemma child : True := by trivial\ntheorem add_zero'));
    await cooperative.deliver(workers[1], child, commitSolverSources(problem, workers[1].worktree));
    expect(node('child').status).toBe('integrated');
  };

  beforeEach(async () => {
    host.verify.mockReset().mockImplementation(async (request: MathematicsVerifierBatchRequest) => {
      const files = Object.fromEntries(problem.ownedFiles.filter(file => file.endsWith('.lean'))
        .map(file => [file, fs.readFileSync(path.join(request.projectRoot, file), 'utf8')]));
      for (const item of request.items) projections.push({ theoremName: item.theoremName, files });
      const result = verifiedBatch(request, { sessionId: 'conditional-fixture' });
      const parent = request.items.find(item => item.theoremName.endsWith('.add_zero'));
      const namespace = parent?.theoremName.split('.').slice(0, -1).join('.');
      const required = parent ? [{ file: 'Submission.lean', name: `${namespace}.support` }, ...requiredParentHelpers] : [];
      const missing = required.some(helper => !inspectScopedLeanDeclarations(files[helper.file] ?? '')
        .some(declaration => declaration.qualifiedName === helper.name));
      return missing || Object.values(files).some(source => /\b(?:sorry|admit)\b/u.test(source)) ? { ...result, status: 'failed',
        results: result.results.map(item => ({ ...item, status: 'failed', error: 'fixture_missing_local_declaration_or_unfinished_proof' })) } : result;
    });
    host.createSession.mockReset().mockImplementation(() => { throw new Error('fixture_real_models_forbidden'); });
    const example = localExample('solver-conditional-integration-');
    ({ directory, workspace, problem } = example);
    workers = [leadWorker(problem, workspace), ...(['researcher', 'engineer'] as const).map(id => peerWorker(example, id, { role: id }))];
    const tasks: CooperativeTask[] = [{ id: 'child', kind: 'lemma', objective: 'Prove a reusable child.',
      theoremName: 'Tutorial.child', proofPath: 'Submission.lean', type: 'True', dependsOn: [], revision: 0,
      ownerId: 'researcher' }, ...problem.targets.map((target, index) => ({
      id: `goal_${index}`, kind: 'goal' as const, objective: `Prove ${target.theoremName}.`,
      theoremName: target.theoremName, proofPath: target.proofPath, dependsOn: index === 0 ? ['child'] : [],
      revision: 0, ownerId: 'engineer', conditional: index === 0, status: index === 0 ? 'active' as const : 'paused' as const,
    }))];
    fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify({ tasks }) + '\n```');
    state = solverState(problem, workspace, { runId: 'conditional-fixture', phase: 'running', failures: [],
      cooperation: { canonicalCommit: problem.baseCommit, tasks: [] } });
    instances = []; requiredParentHelpers = []; projections = [];
    cooperative = create();
    await cooperative.restore();
  });
  afterEach(async () => {
    for (const instance of instances) { instance.controller.abort(); await instance.cooperative.stop(); }
    expect(host.createSession).not.toHaveBeenCalled();
    vi.restoreAllMocks();
    fs.rmSync(directory, { recursive: true, force: true });
  });

  it.each(['absent', 'placeholder', 'proved-draft'])
  ('integrates a parent with its child declaration %s and preserves its own helpers', async variant => {
    const child = await assigned(workers[1]);
    const declaration = variant === 'absent' ? '' : `lemma child : True := by ${variant === 'placeholder' ? 'sorry' : 'exact True.intro'}\n`;
    await deliverParent(declaration);
    expect(node('goal_0').proof!.conditions).toHaveLength(1);
    expect(node('goal_0').proof!.changes.map(change => change.name)).toEqual(['add_zero', 'support']);

    await deliverChild(child);

    expect(node('goal_0')).toMatchObject({ status: 'integrated', attempts: 1, integratedCheck: { passed: true } });
    expect(canonicalSource()).toContain('lemma child : True := by trivial');
    expect(canonicalSource()).toContain('lemma support : True := by trivial');
    expect(canonicalSource()).toContain('have h : True := And.left (And.intro child support)');
    const parentChecks = projections.filter(item => item.theoremName === 'Tutorial.add_zero')
      .map(item => item.files['Submission.lean']);
    expect(parentChecks).toHaveLength(2);
    expect(parentChecks[0]).toContain('theorem add_zero (child : True)');
    expect(parentChecks[1]).toContain('theorem add_zero (n : Nat)');
    expect(parentChecks[1]).toContain('lemma child : True := by trivial');
  });

  it.each(['Other.child', 'Tutorial.Other.child', '_root_.Tutorial.Other.child'])
  ('preserves a required helper sharing the assumed child\'s leaf name when referenced as %s', async reference => {
    const child = await assigned(workers[1]);
    requiredParentHelpers.push({ file: 'Submission.lean', name: 'Tutorial.Other.child' });
    const module = 'Mathlib.Data.Nat.Basic';
    await deliverParent('lemma Other.child : True := by trivial\n', {}, reference, [module]);
    expect(node('goal_0').proof!.changes.map(change => change.name)).toEqual(['add_zero', 'Other.child', 'support']);
    expect(node('goal_0').proof!.imports).toEqual([{ file: 'Submission.lean', module }]);

    await deliverChild(child);

    expect(node('goal_0').status).toBe('integrated');
    expect(canonicalSource()).toContain('lemma Other.child : True := by trivial');
    expect(canonicalSource()).toContain('lemma child : True := by trivial');
    expect(canonicalSource()).toContain(`And.intro child ${reference}`);
    expect(canonicalSource()).toContain(`import ${module}`);
  });

  it('preserves wrappers on a different qualified helper while removing wrappers on the actual assumption', async () => {
    const child = await assigned(workers[1]);
    requiredParentHelpers.push({ file: 'Submission.lean', name: 'Tutorial.Other.child' },
      { file: 'Submission.lean', name: 'Tutorial.Other.wrapper' });
    await deliverParent('lemma Other.child : True := by trivial\n' +
      'lemma Other.wrapper : True := Other.child\nlemma dependent : True := Tutorial.child\n', {}, 'Other.wrapper');
    const projected = projections.find(item => item.theoremName === 'Tutorial.add_zero')!.files['Submission.lean'];
    expect(projected).toContain('lemma Other.child : True := by trivial');
    expect(projected).toContain('lemma Other.wrapper : True := Other.child');
    expect(projected).not.toContain('lemma dependent');

    await deliverChild(child);

    expect(node('goal_0').status).toBe('integrated');
    expect(canonicalSource()).toContain('lemma dependent : True := Tutorial.child');
    expect(canonicalSource()).toContain('And.intro child Other.wrapper');
  });

  it('preserves a required helper whose local binder shadows the assumed child', async () => {
    const child = await assigned(workers[1]);
    requiredParentHelpers.push({ file: 'Submission.lean', name: 'Tutorial.independent' });
    await deliverParent('lemma independent (child : True) : True := by exact child\n', {}, '(independent support)');

    await deliverChild(child);

    expect(node('goal_0').status).toBe('integrated');
    expect(canonicalSource()).toContain('lemma independent (child : True) : True := by exact child');
    expect(canonicalSource()).toContain('And.intro child (independent support)');
  });

  it.each([false, true])('preserves the same declaration name in a different owned proof file (imported: %s)', async imported => {
    instances[0].controller.abort(); await cooperative.stop();
    const file = 'Helpers.lean';
    const plan = readCooperationPlan(problem, workspace);
    fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify({ ...plan,
      tasks: plan.tasks.map(task => ({ ...task, theoremName: task.theoremName?.replace('Tutorial.', 'Submission.') })),
    }) + '\n```');
    fs.writeFileSync(sourcePath(workers[0]), (imported ? 'import Helpers\n' : '') + source(workers[0]).replaceAll('Tutorial', 'Submission'));
    const namespace = imported ? 'Submission.Other' : 'Submission';
    fs.writeFileSync(path.join(workspace, problem.projectRelative, file), `namespace ${namespace}\nend ${namespace}\n`);
    const receipt = JSON.parse(fs.readFileSync(problem.activeProblemPath, 'utf8'));
    fs.writeFileSync(problem.activeProblemPath, JSON.stringify({ ...receipt,
      schema: 'deepscientist.mathematics.lean-eval-bootstrap-receipt.v1', receiptId: 'two-file-fixture',
      problemId: receipt.contract.problemId, benchmarkCommit: LEAN_EVAL_BENCHMARK_COMMIT,
      catalogHash: 'a'.repeat(64), leaderboardSource: 'disabled', createdAt: 1,
      solverOwnedFiles: [...receipt.solverOwnedFiles, file],
    }));
    git(workspace, ['add', '--', `${problem.projectRelative}/${file}`, `${problem.projectRelative}/Submission.lean`]);
    git(workspace, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--no-gpg-sign', '--quiet', '-m', 'Owned helper module']);
    problem = readSolverProblem(workspace, problem.activeProblemPath);
    workers = workers.map(worker => {
      const worktree = worker.role === 'lead' ? workspace : path.join(directory, `${worker.id}-two-files`);
      if (worker.role !== 'lead') git(workspace, ['worktree', 'add', '--quiet', '--detach', worktree, problem.baseCommit]);
      return { ...worker, worktree, ownedFiles: problem.ownedFiles };
    });
    state = { ...state, problem, cooperation: { canonicalCommit: problem.baseCommit, tasks: [] } };
    cooperative = create(); await cooperative.restore();
    const child = await assigned(workers[1]);
    if (imported) requiredParentHelpers.push({ file, name: `${namespace}.child` });
    await deliverParent('lemma child : True := by sorry\n', {
      [file]: `namespace ${namespace}\nlemma child : True := by exact True.intro\nend ${namespace}\n`,
    }, imported ? 'Other.child' : 'support');
    expect(node('goal_0').proof!.changes.map(change => [change.file, change.name])).toEqual([
      ['Submission.lean', 'add_zero'], ['Submission.lean', 'support'], [file, 'child'],
    ]);
    expect(projections.find(item => item.theoremName === 'Submission.add_zero')!.files[file])
      .toContain('lemma child : True := by exact True.intro');

    await deliverChild(child);

    expect(node('goal_0').status).toBe('integrated');
    expect(canonicalSource()).toContain('lemma child : True := by trivial');
    expect(committedSource(workspace, state.cooperation!.canonicalCommit!, `${problem.projectRelative}/${file}`))
      .toContain('lemma child : True := by exact True.intro');
  });

  it('rechecks an archived parent carrying an old child placeholder before integrating it', async () => {
    await assigned(workers[1]);
    await deliverParent('lemma child : True := by sorry\n');
    const proof = node('goal_0').proof!;
    // Older checkpoints captured the assumed declaration in the integration patch.
    proof.changes.push({ file: 'Submission.lean', name: 'child', after: 'lemma child : True := by sorry\n', beforeName: 'add_zero' });
    instances[0].controller.abort(); await cooperative.stop();
    const archive = path.join(directory, 'state.json');
    writeSolverRunState(archive, state); state = readSolverRunState(archive);
    cooperative = create(); await cooperative.restore();

    await deliverChild(await assigned(workers[1]));

    expect(node('goal_0')).toMatchObject({ status: 'integrated', attempts: 1, integratedCheck: { passed: true } });
    expect(node('goal_0').proof!.changes.some(change => change.name === 'child')).toBe(false);
    expect(canonicalSource()).toContain('lemma child : True := by trivial');
    expect(canonicalSource()).toContain('lemma support : True := by trivial');
  });

  it('keeps the canonical child when the combined parent fails its independent merged check', async () => {
    const child = await assigned(workers[1]);
    await deliverParent('lemma child : True := by sorry\n');
    const verify = host.verify.getMockImplementation()!;
    host.verify.mockImplementation(async (request: MathematicsVerifierBatchRequest) => {
      const result = await verify(request);
      const source = fs.readFileSync(path.join(request.projectRoot, 'Submission.lean'), 'utf8');
      return request.items[0].theoremName === 'Tutorial.add_zero' && !source.includes('(child : True)')
        ? failedBatch(result, { stdoutPreview: () => 'Submission.lean:1:0: error: fixture combined proof does not close the target' }) : result;
    });

    await deliverChild(child);

    expect(node('goal_0').status).toBe('blocked');
    expect(node('goal_0').feedback).toContain('math_task_merged_proof_failed');
    expect(canonicalSource()).toContain('lemma child : True := by trivial');
    expect(canonicalSource()).toContain('n + 0 = n := by sorry');
    expect(canonicalSource()).not.toContain('lemma support');
  });
});
