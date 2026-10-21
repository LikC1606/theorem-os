import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { LOCAL_EXAMPLE_PROOF } from '../src/math/localExample';
import type { LeanDeclarationReferences } from '../src/math/leanReferences';
import type { MathematicsVerifierBatchRequest } from '../src/math/verifier';
import type { SolverRunState } from '../src/solver/archive';
import type { CooperativeResearch } from '../src/solver/cooperation';
import { directSolverModules } from '../src/solver/modules';
import { checkSolverProof, hasFreshSolverCheck, type ProofCheck } from '../src/solver/modules/evidence';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { commitSolverSources, type SolverProblem } from '../src/solver/problem';
import { isStatementAction, statementSnapshot, writeStatementSnapshot, type StatementReview } from '../src/solver/statementReview';
import { taskVersion, type TaskRecord } from '../src/solver/tasks';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';
import { verifiedBatch } from './helpers/verifier';

const host = vi.hoisted(() => ({ verify: vi.fn(), createSession: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify,
  resolveMathematicsLakePackagesCache: () => undefined,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.createSession }));

describe('fixed-candidate statement review scope', () => {
  let directory: string, workspace: string, problem: SolverProblem, state: SolverRunState;
  let workers: ResearchWorker[], cooperative: CooperativeResearch, controller: AbortController, check: ProofCheck;
  let reports: Map<string, LeanDeclarationReferences | undefined>;
  let events: { event: string; details?: Record<string, unknown> }[];
  let pending: Promise<unknown>[];
  const budget = { maxTurns: Infinity, remainingMs: Infinity };

  const track = <T,>(promise: Promise<T>) => {
    pending.push(promise); void promise.catch(() => {}); return promise;
  };
  const review = (taskId: string) => state.cooperation!.statementReviews!.find(item => item.taskId === taskId)!;
  const task = (taskId: string) => state.cooperation!.tasks.find(item => item.task.id === taskId)!;
  const scope = () => events.findLast(item => item.event === 'final_statement_review_scope')!.details!;
  const freshCheck = async () => {
    check = await checkSolverProof(problem, workspace, {}, controller.signal);
    expect(hasFreshSolverCheck(check)).toBe(true);
    return check;
  };
  const create = () => cooperativeResearch({ state, workers, retrievalRoot: directory, signal: controller.signal,
    emit: (event, details) => events.push({ event, details }), modules: directSolverModules });
  const addReview = (node: TaskRecord) => {
    const snapshot = statementSnapshot(problem, node.task, workspace, check.commit, state.environmentDigest, []);
    const reviewWorkspace = path.join(directory, 'statements', node.task.id);
    const value: StatementReview = { id: `review-${node.task.id}`, taskId: node.task.id, taskDigest: taskVersion(node.task),
      snapshotDigest: snapshot.snapshotDigest, environmentDigest: state.environmentDigest, commit: check.commit,
      leanStatement: snapshot.input.leanStatement, intendedStatement: node.task.informalStatement!, premises: [], dependencies: [],
      workspace: reviewWorkspace, files: writeStatementSnapshot(reviewWorkspace, snapshot), status: 'pending' };
    (state.cooperation!.statementReviews ??= []).push(value);
  };
  const completeStatement = async (expectedTaskId: string) => {
    for (const kind of ['backtranslate', 'statement-review'] as const) {
      const action = await cooperative.next(workers[1]!, budget);
      expect(action).toMatchObject({ kind, taskId: expectedTaskId });
      if (!action || !isStatementAction(action)) throw new Error('missing_statement_assignment');
      expect(cooperative.current(action)).toBe(true);
      expect(cooperative.started(workers[1]!, action)).toBe(true);
      fs.writeFileSync(path.join(action.workspace, 'RESEARCH.md'), JSON.stringify({ reviewId: action.reviewId,
        snapshotDigest: action.snapshotDigest, ...(kind === 'backtranslate' ? { mathematics: 'The stated proposition holds.' } : { verdict: 'accepted' }) }));
      await cooperative.deliverStatement(workers[1]!, action);
    }
    expect(review(expectedTaskId).status).toBe('accepted');
  };
  const completeFinalReview = async () => {
    const action = await cooperative.next(workers[1]!, budget);
    expect(action).toMatchObject({ kind: 'review', seedCommit: check.commit });
    if (action?.kind !== 'review') throw new Error('missing_final_review');
    expect(cooperative.started(workers[1]!, action)).toBe(true);
    fs.writeFileSync(path.join(workers[1]!.worktree, 'RESEARCH.md'), JSON.stringify({ commit: action.seedCommit, verdict: 'accepted' }));
    await cooperative.deliver(workers[1]!, action, commitSolverSources(problem, workers[1]!.worktree));
    expect(state.cooperation!.review!.status).toBe('accepted');
  };

  beforeEach(async () => {
    events = []; pending = []; controller = new AbortController();
    host.createSession.mockReset().mockImplementation(() => { throw new Error('fixture_real_models_forbidden'); });
    host.verify.mockReset().mockImplementation(async (request: MathematicsVerifierBatchRequest, options) => {
      expect(options.collectDeclarationReferences).toBe(true);
      const result = verifiedBatch(request, { sessionId: 'final-review-scope-fixture', receipt: 'scope', checks: true });
      return { ...result, results: result.results.map(receipt => ({ ...receipt,
        ...(reports.get(receipt.theoremName) ? { declarationReferences: reports.get(receipt.theoremName) } : {}) })) };
    });
    const example = localExample('solver-final-review-scope-');
    ({ directory, workspace, problem } = example);
    fs.writeFileSync(path.join(workspace, problem.projectRelative, 'Submission.lean'), LOCAL_EXAMPLE_PROOF.replace('theorem add_zero',
      'lemma used : True := by trivial\nlemma transitive : True := by trivial\nlemma unused : True := by trivial\ntheorem add_zero'));
    const canonicalCommit = commitSolverSources(problem, workspace);
    workers = [leadWorker(problem, workspace), peerWorker(example, 'reviewer', { name: 'peer', commit: canonicalCommit })];
    reports = new Map(problem.targets.map(target => [target.theoremName, { statement: [], proof: [] }]));
    state = solverState(problem, workspace, { runId: 'final-review-scope-fixture', phase: 'running', failures: [],
      cooperation: { canonicalCommit,
        groups: [{ group: { id: 'main', objective: 'Prove the original problem.', status: 'active', revision: 0 }, turns: 0 }],
        tasks: [...['used', 'transitive', 'unused'].map(id => ({ task: { id, kind: 'lemma' as const,
          objective: `Establish ${id}.`, theoremName: `Tutorial.${id}`, proofPath: 'Submission.lean', type: 'True',
          dependsOn: [], revision: 0, statementReview: true, informalStatement: 'Truth holds.', status: 'paused' as const },
          status: 'pending' as const, attempts: 0 })), ...problem.targets.map((target, index) => ({ task: {
            id: `goal_${index}`, kind: 'goal' as const, objective: `Prove ${target.theoremName}.`,
            theoremName: target.theoremName, proofPath: target.proofPath, dependsOn: [], revision: 0 },
            status: 'integrated' as const, attempts: 1 }))] } });
    await freshCheck();
    for (const node of state.cooperation!.tasks.filter(node => node.task.statementReview)) addReview(node);
    cooperative = create();
  });

  afterEach(async () => {
    controller.abort();
    await Promise.allSettled(pending);
    await cooperative.stop();
    expect(host.createSession).not.toHaveBeenCalled();
    vi.restoreAllMocks();
    fs.rmSync(directory, { recursive: true, force: true });
  });

  it.each(['paused', 'stopped', 'parked'] as const)('accepts the fixed proof without an unused %s alternative review', async control => {
    if (control === 'parked') { task('unused').task = { ...task('unused').task, status: 'active' }; task('unused').routeParking = ['local-obstruction']; }
    else task('unused').task = { ...task('unused').task, status: control };
    cooperative.requireReview(check);
    expect(scope()).toMatchObject({ referenceCoverage: 'complete', requiredTaskIds: [], unusedTaskIds: ['used', 'transitive', 'unused'] });
    await completeFinalReview();
    expect(cooperative.reviewed(check)).toBe(true);
    expect(state.cooperation!.statementReviews!.every(item => item.status === 'pending')).toBe(true);
  });

  it.each(['paused', 'stopped', 'parked', 'group-paused', 'group-exhausted'] as const)
  ('dispatches both necessary review stages for a %s helper without reopening its proof work', async control => {
    reports.set(problem.targets[0]!.theoremName, { statement: [], proof: [{ name: 'Tutorial.used', file: 'Submission.lean' }] });
    await freshCheck();
    if (control === 'parked') { task('used').task = { ...task('used').task, status: 'active' }; task('used').routeParking = ['local-obstruction']; }
    else if (control.startsWith('group-')) {
      const group = state.cooperation!.groups![0]!;
      group.group = { ...group.group, ...(control === 'group-paused' ? { status: 'paused' as const } : { maxTurns: 0 }) };
    } else task('used').task = { ...task('used').task, status: control };
    const savedTask = task('used').task, groupTurns = state.cooperation!.groups![0]!.turns;
    cooperative.requireReview(check);
    expect(scope()).toMatchObject({ referenceCoverage: 'complete', requiredTaskIds: ['used'] });
    await completeStatement('used');
    expect(task('used').task).toBe(savedTask);
    expect(task('used').status).toBe('pending');
    expect(state.cooperation!.groups![0]!.turns).toBe(groupTurns);
    await completeFinalReview();
    expect(cooperative.reviewed(check)).toBe(true);
  });

  it('requires original goals and the union of statement and transitive proof references across all targets', async () => {
    task('goal_0').task = { ...task('goal_0').task, statementReview: true, informalStatement: 'Adding zero leaves a number unchanged.', status: 'paused' };
    addReview(task('goal_0'));
    reports.set(problem.targets[0]!.theoremName, { statement: [{ name: 'Tutorial.used', file: 'Submission.lean' }], proof: [] });
    reports.set(problem.targets[1]!.theoremName, { statement: [], proof: [{ name: 'Tutorial.used', file: 'Submission.lean' },
      { name: 'Tutorial.transitive', file: 'Submission.lean' }] });
    await freshCheck(); cooperative.requireReview(check);
    expect(scope()).toMatchObject({ referenceCoverage: 'complete', requiredTaskIds: ['used', 'transitive', 'goal_0'], unusedTaskIds: ['unused'] });
    for (const id of ['used', 'transitive', 'goal_0']) await completeStatement(id);
    await completeFinalReview();
    expect(cooperative.reviewed(check)).toBe(true);
  });

  it('conservatively completes every configured review if any original target lacks reference coverage', async () => {
    reports.delete(problem.targets[1]!.theoremName);
    await freshCheck(); cooperative.requireReview(check);
    expect(scope()).toMatchObject({ referenceCoverage: 'unknown', requiredTaskIds: ['used', 'transitive', 'unused'], unusedTaskIds: [] });
    for (const id of ['used', 'transitive', 'unused']) await completeStatement(id);
    await completeFinalReview();
    expect(cooperative.reviewed(check)).toBe(true);
  });

  it.each(['serialized', 'modified'] as const)('does not let %s verification metadata narrow the required reviews', async provenance => {
    const untrusted = provenance === 'serialized' ? JSON.parse(JSON.stringify(check)) as ProofCheck : check;
    if (provenance === 'modified') untrusted.verification.results[0]!.declarationReferences = {
      statement: [{ name: 'Tutorial.used', file: 'Submission.lean' }], proof: [] };
    expect(hasFreshSolverCheck(untrusted)).toBe(false);
    cooperative.requireReview(untrusted);
    state.cooperation!.review!.status = 'accepted';
    expect(scope()).toMatchObject({ referenceCoverage: 'unknown', requiredTaskIds: ['used', 'transitive', 'unused'] });
    expect(cooperative.reviewed(untrusted)).toBe(false);
  });

  it('waits for required statements before assembling after the fixed proof review was accepted', async () => {
    reports.set(problem.targets[0]!.theoremName, { statement: [], proof: [{ name: 'Tutorial.used', file: 'Submission.lean' }] });
    await freshCheck();
    cooperative.requireReview(check); state.cooperation!.review!.status = 'accepted';
    let settled = false;
    const nextLead = track(cooperative.next(workers[0]!, budget).then(action => { settled = true; return action; }));
    await Promise.resolve();
    expect(settled).toBe(false);
    await completeStatement('used');
    expect(await nextLead).toMatchObject({ kind: 'assemble', seedCommit: check.commit });
    expect(cooperative.reviewed(check)).toBe(true);
  });

  it.each([false, true])('retains only a necessary in-flight statement reviewer (used: %s)', async used => {
    task('used').task = { ...task('used').task, status: 'active' };
    const action = await cooperative.next(workers[1]!, budget);
    if (!action || !isStatementAction(action)) throw new Error('missing_active_statement');
    const interrupt = vi.fn(async () => {});
    cooperative.activate(workers[1]!, action, interrupt, async () => {});
    if (used) reports.set(problem.targets[0]!.theoremName, { statement: [],
      proof: [{ name: 'Tutorial.used', file: 'Submission.lean' }] });
    await freshCheck(); cooperative.requireReview(check);
    expect(cooperative.current(action)).toBe(used);
    expect(interrupt).toHaveBeenCalledTimes(used ? 0 : 1);
    expect(review('used').status).toBe(used ? 'translating' : 'pending');
    cooperative.deactivate(workers[1]!);
    if (!used) await completeFinalReview();
  });

  it.each(['environment', 'task-contract', 'candidate-source'] as const)('invalidates selective review scope after a changed %s', async change => {
    cooperative.requireReview(check); state.cooperation!.review!.status = 'accepted';
    expect(cooperative.reviewed(check)).toBe(true);
    if (change === 'environment') state.environmentDigest = 'new-environment';
    else if (change === 'task-contract') task('unused').task = { ...task('unused').task, type: 'True ∧ True' };
    else state.cooperation!.canonicalCommit = problem.baseCommit;
    expect(cooperative.reviewed(check)).toBe(false);
  });

  it('does not retain a selective scope when a cooperation archive is reconstructed', async () => {
    cooperative.requireReview(check); state.cooperation!.review!.status = 'accepted';
    expect(cooperative.reviewed(check)).toBe(true);
    await cooperative.stop(); state = JSON.parse(JSON.stringify(state)); cooperative = create();
    expect(cooperative.reviewed(check)).toBe(false);
    cooperative.requireReview(check);
    expect(cooperative.reviewed(check)).toBe(true);
  });
});
