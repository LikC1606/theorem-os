import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import type { SolverRunState } from '../src/solver/archive';
import { CooperativeResearch } from '../src/solver/cooperation';
import { ownedSourceDigest } from '../src/solver/cooperativeProof';
import { directSolverModules, type SolverModules } from '../src/solver/modules';
import type { ProofCheck } from '../src/solver/modules/evidence';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { commitSolverSources, type SolverProblem } from '../src/solver/problem';
import { runResearchWorkers } from '../src/solver/research';
import * as statementReview from '../src/solver/statementReview';
import { isStatementAction, statementSnapshot, writeStatementSnapshot, type StatementAction, type StatementReview } from '../src/solver/statementReview';
import { parseCooperationPlan, taskVersion, type CooperativeAction } from '../src/solver/tasks';
import { cooperativeResearch, workerAccess } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';

vi.mock('../src/math/mathBuildManifest', () => ({ readMathBuildManifest: vi.fn() }));

describe('failed turns superseded while their session closes', () => {
  let directory: string, problem: SolverProblem, state: SolverRunState, workers: ResearchWorker[];
  let cooperative: CooperativeResearch | undefined;
  let events: { event: string; details?: Record<string, unknown> }[];

  beforeEach(() => {
    const example = localExample('solver-stale-failure-', 'lead');
    ({ directory, problem } = example);
    workers = [leadWorker(problem, example.workspace), peerWorker(example, 'peer', { role: 'engineer' })];
    const plan = parseCooperationPlan(problem, { tasks: problem.targets.map((target, index) => ({
      id: `goal_${index}`, kind: 'goal', objective: `Prove ${target.theoremName}`,
      proofPath: target.proofPath, theoremName: target.theoremName,
    })) });
    state = solverState(problem, example.workspace, { runId: 'stale-failure-fixture', phase: 'prepared',
      evaluatorDigest: 'evaluation', model: 'fixture', effort: 'fixture',
      workers: workers.map(worker => ({ ...worker, phase: 'prepared', turns: 0 })),
      cooperation: { tasks: plan.tasks.map(task => ({ task, status: 'pending', attempts: 0 })),
        groups: plan.groups.map(group => ({ group, turns: 0 })) } });
    events = []; cooperative = undefined;
  });
  afterEach(() => { vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true }); });

  const budget = { maxTurns: Infinity, remainingMs: Infinity };
  const baseDigest = () => ownedSourceDigest(problem, workers[0].worktree, problem.baseCommit);
  const create = () => {
    const controller = new AbortController();
    cooperative = cooperativeResearch({ state, workers, retrievalRoot: directory, signal: controller.signal });
    return controller;
  };
  const restore = async () => {
    const controller = create();
    await cooperative!.restore();
    return controller;
  };
  const addStatementReview = (kind: StatementAction['kind']): StatementReview => {
    const node = state.cooperation!.tasks[0];
    node.task = { ...node.task, statementReview: true, informalStatement: 'The original arithmetic target holds.' };
    const snapshot = statementSnapshot(problem, node.task, workers[0].worktree, problem.baseCommit, state.environmentDigest, []);
    const workspace = path.join(directory, 'statement-review');
    const review: StatementReview = { id: 'statement-fixture', taskId: node.task.id, taskDigest: taskVersion(node.task),
      snapshotDigest: snapshot.snapshotDigest, environmentDigest: state.environmentDigest, commit: problem.baseCommit,
      leanStatement: snapshot.input.leanStatement, intendedStatement: node.task.informalStatement!, premises: [], dependencies: [],
      workspace, files: writeStatementSnapshot(workspace, snapshot), status: kind === 'backtranslate' ? 'pending' : 'translated',
      ...(kind === 'statement-review' ? { translation: { mathematics: 'The original arithmetic target holds.', assumptions: [],
        definitions: [], evidenceRefs: [] } } : {}) };
    state.cooperation!.statementReviews = [review];
    return review;
  };

  it.each((['task', 'lead', 'review', 'backtranslate', 'statement-review'] as const).flatMap(kind =>
    (['revise', 'remove', 'pause'] as const).map(change => ({ kind, change }))))
  ('preserves the new plan when an edit applies $change during a failed $kind session close', async ({ kind, change }) => {
    if (kind === 'lead') state.cooperation!.error = 'A new Lead assessment is requested.';
    if (kind === 'review') state.cooperation!.review = { commit: problem.baseCommit, sourceDigest: baseDigest(), status: 'pending' };
    if (kind === 'backtranslate' || kind === 'statement-review') {
      vi.spyOn(statementReview, 'captureStatementContexts').mockImplementation(async (_problem, tasks) =>
        new Map(tasks.map(task => [task.id, { type: 'Mock fixed arithmetic type.', constants: [], omitted: [] }])));
      const restore = CooperativeResearch.prototype.restore;
      vi.spyOn(CooperativeResearch.prototype, 'restore').mockImplementation(async function(...args) {
        const result = await restore.apply(this, args);
        addStatementReview(kind);
        return result;
      });
    }
    const target = state.cooperation!.tasks[0].task;
    const activate = CooperativeResearch.prototype.activate;
    vi.spyOn(CooperativeResearch.prototype, 'activate').mockImplementation(function(...args) {
      cooperative = this;
      return activate.apply(this, args);
    });
    let assigned: CooperativeAction | undefined;
    let edited = false;
    const retry = vi.fn().mockReturnValue(undefined);
    const close = vi.fn(async () => {
      if (edited || !assigned) return;
      edited = true;
      const failedTask = assigned.kind === 'task' ? assigned.task : target;
      const tasks = state.cooperation!.tasks.map(node => node.task).flatMap(task => {
        if (task.id !== failedTask.id) return [task];
        if (change === 'remove') return [];
        return [{ ...task, ...(change === 'revise' ? { revision: task.revision + 1 } : { status: 'paused' as const }) }];
      });
      if (change === 'remove') {
        tasks.push({ ...failedTask, id: 'replacement', revision: failedTask.revision + 1 });
      }
      fs.appendFileSync(path.join(directory, 'edits.jsonl'), JSON.stringify({
        id: 'during-close', baseVersion: state.cooperation!.planVersion, tasks,
      }) + '\n');
      await cooperative!.pulse();
      expect(state.cooperation!.edits?.find(edit => edit.id === 'during-close')?.status).toBe('applied');
      if (kind === 'review' && change !== 'pause') {
        cooperative!.rejected(assigned, 'Late failure from the superseded review.');
        expect(state.cooperation!.review).toBeUndefined();
      }
    });
    const modules: SolverModules = { ...directSolverModules,
      M1: { ...directSolverModules.M1, open: async options => ({
        threadId: 'fixture-failed-thread', lastError: 'fetch failed', close,
        interrupt: vi.fn(async () => {}), run: async message => {
          const action = JSON.parse(message) as CooperativeAction;
          if (action.kind !== kind) throw new Error('fixture_unexpected_model_assignment');
          assigned = action;
          if (!isStatementAction(action)) {
            const file = path.join(options.workspace, problem.projectRelative,
              action.kind === 'task' ? action.task.proofPath! : target.proofPath!);
            fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('n + 0 = n', 'n + 0 = 0'));
          }
          return 'failed';
        },
      }) },
      M2: { ...directSolverModules.M2,
        check: async () => { throw new Error('fixture_unexpected_proof_check'); },
        checkTask: async () => { throw new Error('fixture_unexpected_task_check'); } },
      M3: { ...directSolverModules.M3, retry, select: (_state, _options, _budget, assignment) =>
        kind === 'lead' && assignment?.kind === 'task' ? { operation: 'stop', reason: 'fixture_only_lead_runs' }
          : { operation: 'direct', reason: 'fixture_failure' } },
      M4: { ...directSolverModules.M4, build: (_problem, _state, access) => ({
        instructions: 'Local fixture.', message: JSON.stringify(access.assignment),
        scope: 'original-problem-and-allowed-library', sources: { problemReceiptDigest: problem.receiptDigest },
      }), statement: (_review, action, problemReceiptDigest) => ({
        instructions: 'Fixed local statement fixture.', message: JSON.stringify(action),
        scope: 'fixed-statement', sources: { problemReceiptDigest },
      }) },
    };

    const result = runResearchWorkers({ state, workers, modules,
      access: workerAccess(workers, directory), root: directory, buildFile: path.join(directory, 'build.json'), taskText: 'Prove the original targets.',
      executable: 'fixture-no-model', profile: 'fixture', signal: new AbortController().signal,
      deadline: Infinity, maxTurns: 1, maxTurnMs: Infinity, maxTotalTokens: 0,
      save: () => {}, emit: (event, details) => events.push({ event, details }),
    });
    const currentReviewFailure = kind === 'review' && change === 'pause';
    if (currentReviewFailure) await expect(result).rejects.toThrow('math_original_declaration_changed');
    else await expect(result).resolves.toBeUndefined();

    expect(edited).toBe(true);
    expect(state.cooperation!.tasks.every(node => node.status === 'pending' && !node.feedback)).toBe(true);
    const failures = state.cooperation!.deliveries?.filter(delivery => delivery.kind === 'failure') ?? [];
    if (currentReviewFailure) {
      expect(failures).toHaveLength(1);
      expect(state.cooperation!.review).toMatchObject({ status: 'changes_requested',
        summary: expect.stringContaining('math_original_declaration_changed') });
    } else expect(failures).toEqual([]);
    expect(events.some(event => event.event === 'assignment_superseded')).toBe(!currentReviewFailure);
    if (kind === 'review' && !currentReviewFailure) expect(state.cooperation!.deliveries).toContainEqual(
      expect.objectContaining({ kind: 'review', status: 'superseded', commit: problem.baseCommit }));
    expect(retry).not.toHaveBeenCalled();
    expect(close).toHaveBeenCalledOnce();
  });

  it.each(['replacement', 'accepted'])('preserves a %s review and its records after late callbacks from the old action', async version => {
    const controller = create();
    try {
      await cooperative!.restore();
      const check: ProofCheck = { commit: problem.baseCommit, sourceDigest: baseDigest(), passed: true,
        verification: { schema: 'deepscientist.mathematics.verification-batch/v1', status: 'kernel_verified',
          targetCommit: problem.baseCommit, sessionId: 'review-fixture', events: [], results: [],
          startedAt: 1, checkedAt: 2, durationMs: 1 } };
      cooperative!.requireReview(check);
      const action = await cooperative!.next(workers[1], budget);
      if (action?.kind !== 'review') throw new Error('fixture_missing_review_assignment');
      expect(cooperative!.started(workers[1], action)).toBe(true);
      if (version === 'accepted') {
        fs.writeFileSync(path.join(workers[1].worktree, 'RESEARCH.md'), '```math-review\n' + JSON.stringify({
          commit: action.seedCommit, verdict: 'accepted', summary: 'Fixed candidate reviewed.',
        }) + '\n```');
        await cooperative!.deliver(workers[1], action, commitSolverSources(problem, workers[1].worktree));
      } else {
        fs.writeFileSync(path.join(workers[0].worktree, 'RESEARCH.md'), 'A replacement immutable candidate.\n');
        cooperative!.requireReview({ ...check, commit: commitSolverSources(problem, workers[0].worktree) });
      }
      const current = { ...state.cooperation!.review };
      expect(cooperative!.current(action)).toBe(false);

      cooperative!.rejected(action, 'Late failure from the old review action.');
      cooperative!.interrupted(workers[1], action);
      cooperative!.release(workers[1], action);
      await cooperative!.deliver(workers[1], action, action.seedCommit);

      expect(state.cooperation!.review).toEqual(current);
      expect(state.cooperation!.review?.status).toBe(version === 'accepted' ? 'accepted' : 'pending');
      expect(state.cooperation!.deliveries?.filter(delivery => delivery.kind === 'review').map(delivery => delivery.status))
        .toEqual(version === 'accepted' ? ['accepted', 'superseded'] : ['superseded']);
      expect(state.cooperation!.deliveries?.some(delivery => delivery.kind === 'failure')).not.toBe(true);
    } finally { controller.abort(); await cooperative!.stop(); }
  });

  it.each(['accepted', 'changes_requested'] as const)('does not reopen a legacy %s review after late cancellation or release', async status => {
    const controller = await restore();
    try {
      state.cooperation!.review = { commit: problem.baseCommit, sourceDigest: baseDigest(), status, workerId: workers[1].id };
      const action: CooperativeAction = { kind: 'review', seedCommit: problem.baseCommit,
        sourceDigest: state.cooperation!.review.sourceDigest };
      const before = { ...state.cooperation!.review };
      cooperative!.interrupted(workers[1], action);
      cooperative!.release(workers[1], action);
      expect(state.cooperation!.review).toEqual(before);
    } finally { controller.abort(); await cooperative!.stop(); }
  });

  it('isolates repeated final reviews of the same commit and worker from every old callback', async () => {
    const controller = await restore();
    try {
      state.cooperation!.review = { commit: problem.baseCommit, sourceDigest: baseDigest(), status: 'pending' };
      const first = await cooperative!.next(workers[1], budget);
      if (first?.kind !== 'review') throw new Error('fixture_missing_review_assignment');
      expect(cooperative!.started(workers[1], first)).toBe(true);
      cooperative!.interrupted(workers[1], first);
      const second = await cooperative!.next(workers[1], budget);
      if (second?.kind !== 'review') throw new Error('fixture_missing_review_assignment');
      expect(first.assignmentId).toEqual(expect.any(String));
      expect(second.assignmentId).toEqual(expect.any(String));
      expect(second.assignmentId).not.toBe(first.assignmentId);
      const before = { ...state.cooperation!.review };
      const turns = state.cooperation!.groups![0].turns;

      expect(cooperative!.current(first)).toBe(false);
      expect(cooperative!.started(workers[1], first)).toBe(false);
      expect(() => cooperative!.started(workers[0], second)).toThrow('math_review_assignment_invalid');
      cooperative!.rejected(first, 'Failure from the previous dispatch.');
      cooperative!.interrupted(workers[1], first);
      cooperative!.release(workers[1], first);
      fs.writeFileSync(path.join(workers[1].worktree, 'RESEARCH.md'), '```math-review\n' + JSON.stringify({
        commit: first.seedCommit, verdict: 'accepted', summary: 'Old dispatch result.',
      }) + '\n```');
      await cooperative!.deliver(workers[1], first, first.seedCommit);
      await cooperative!.deliver(workers[1], first, first.seedCommit, true);

      expect(state.cooperation!.review).toEqual(before);
      expect(state.cooperation!.groups![0].turns).toBe(turns);
      expect(state.cooperation!.deliveries?.filter(record => record.kind === 'review').map(record => record.status))
        .toEqual(['superseded', 'superseded']);
      expect(state.cooperation!.deliveries?.some(record => record.kind === 'failure')).not.toBe(true);
      expect(cooperative!.started(workers[1], second)).toBe(true);
      cooperative!.rejected(second, 'Current reviewer diagnostic.');
      expect(state.cooperation!.review).toMatchObject({ status: 'changes_requested', workerId: undefined });
      expect(state.cooperation!.deliveries?.at(-1)).toMatchObject({ producer: workers[1].id, kind: 'failure' });
    } finally { controller.abort(); await cooperative!.stop(); }
  });

  it('accepts a legacy running review only until its first new dispatch', async () => {
    const controller = await restore();
    try {
      state.cooperation!.review = { commit: problem.baseCommit, sourceDigest: baseDigest(), status: 'running', workerId: workers[1].id };
      const legacy: CooperativeAction = { kind: 'review', seedCommit: problem.baseCommit,
        sourceDigest: state.cooperation!.review.sourceDigest };
      expect(cooperative!.current(legacy)).toBe(true);
      cooperative!.interrupted(workers[1], legacy);
      const next = await cooperative!.next(workers[1], budget);
      if (next?.kind !== 'review') throw new Error('fixture_missing_review_assignment');
      expect(next.assignmentId).toEqual(expect.any(String));
      expect(cooperative!.current(legacy)).toBe(false);
      const wrongSource = { ...next, sourceDigest: 'wrong-fixed-source' };
      const before = { ...state.cooperation!.review };
      cooperative!.interrupted(workers[1], wrongSource);
      await cooperative!.deliver(workers[1], wrongSource, next.seedCommit);
      expect(state.cooperation!.review).toEqual(before);
    } finally { controller.abort(); await cooperative!.stop(); }
  });

  it.each(['backtranslate', 'statement-review'] as const)('isolates repeated %s dispatches in the same workspace', async kind => {
    const controller = await restore();
    try {
      const review = addStatementReview(kind);
      const first = await cooperative!.next(workers[1], budget);
      if (!first || first.kind !== kind) throw new Error('fixture_missing_statement_assignment');
      expect(cooperative!.started(workers[1], first)).toBe(true);
      cooperative!.interrupted(workers[1], first);
      const second = await cooperative!.next(workers[1], budget);
      if (!second || second.kind !== kind) throw new Error('fixture_missing_statement_assignment');
      expect(second.assignmentId).toEqual(expect.any(String));
      expect(second.assignmentId).not.toBe(first.assignmentId);
      expect(second.workspace).toBe(first.workspace);
      const before = { ...review };
      const turns = state.cooperation!.groups![0].turns;

      expect(cooperative!.current(first)).toBe(false);
      expect(cooperative!.started(workers[1], first)).toBe(false);
      expect(() => cooperative!.started(workers[0], second)).toThrow('math_statement_review_assignment_invalid');
      cooperative!.rejected(first, 'Failure from the previous statement dispatch.');
      cooperative!.interrupted(workers[1], first);
      cooperative!.release(workers[1], first);
      fs.writeFileSync(path.join(review.workspace, 'RESEARCH.md'), '```' +
        (kind === 'backtranslate' ? 'math-backtranslation' : 'math-statement-review') + '\n' + JSON.stringify({
          reviewId: review.id, snapshotDigest: review.snapshotDigest, mathematics: 'The original arithmetic target holds.',
          verdict: 'accepted', summary: 'The fixed intended statement agrees.',
        }) + '\n```');
      await cooperative!.deliverStatement(workers[1], first);
      expect(review).toEqual(before);
      expect(state.cooperation!.groups![0].turns).toBe(turns);
      expect(state.cooperation!.deliveries?.at(-1)).toMatchObject({ status: 'superseded' });
      expect(cooperative!.started(workers[1], second)).toBe(true);
      await cooperative!.deliverStatement(workers[1], second);
      expect(review.status).toBe(kind === 'backtranslate' ? 'translated' : 'accepted');
      expect(review.workerId).toBeUndefined();
      const completed = { ...review };
      cooperative!.rejected(second, 'Late terminal failure.');
      cooperative!.interrupted(workers[1], second);
      cooperative!.release(workers[1], second);
      expect(cooperative!.started(workers[1], second)).toBe(false);
      expect(review).toEqual(completed);
    } finally { controller.abort(); await cooperative!.stop(); }
  });

  it.each(['backtranslate', 'statement-review'] as const)('migrates a legacy running %s without accepting its later callbacks', async kind => {
    const controller = await restore();
    try {
      const review = addStatementReview(kind);
      review.status = kind === 'backtranslate' ? 'translating' : 'reviewing'; review.workerId = workers[1].id;
      const legacy: StatementAction = { kind, reviewId: review.id, taskId: review.taskId, taskDigest: review.taskDigest,
        snapshotDigest: review.snapshotDigest, seedCommit: review.commit, workspace: review.workspace };
      expect(cooperative!.current(legacy)).toBe(true);
      cooperative!.interrupted(workers[1], legacy);
      const next = await cooperative!.next(workers[1], budget);
      if (!next || next.kind !== kind) throw new Error('fixture_missing_statement_assignment');
      expect(next.assignmentId).toEqual(expect.any(String));
      expect(cooperative!.current(legacy)).toBe(false);
      const before = { ...review }, turns = state.cooperation!.groups![0].turns;
      expect(cooperative!.started(workers[1], legacy)).toBe(false);
      cooperative!.rejected(legacy, 'Late legacy diagnostic.');
      cooperative!.interrupted(workers[1], legacy);
      cooperative!.release(workers[1], legacy);
      await cooperative!.deliverStatement(workers[1], legacy);
      expect(review).toEqual(before);
      expect(state.cooperation!.groups![0].turns).toBe(turns);
      expect(state.cooperation!.deliveries?.at(-1)).toMatchObject({ status: 'superseded' });
    } finally { controller.abort(); await cooperative!.stop(); }
  });
});
