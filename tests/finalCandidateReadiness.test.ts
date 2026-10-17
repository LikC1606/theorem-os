import { describe, expect, it } from 'vitest';
import { criticalPathResearchTasks, finalCandidateReviewReady, goalsFirstResearchTasks,
  readyResearchTasks, taskCanStart } from '../src/solver/modules/search';
import { isFinalCandidateReview, markTaskAcceptance, parseCooperationPlan, taskVersion,
  type CooperativeTask, type TaskRecord } from '../src/solver/tasks';
import type { SolverProblem } from '../src/solver/problem';

const node = (id: string, kind: CooperativeTask['kind']): TaskRecord => ({
  task: { id, kind, objective: id, revision: 0, dependsOn: [],
    ...(kind === 'goal' ? { proofPath: 'Submission.lean', theoremName: `Submission.${id}` } : {}) },
  status: 'pending', attempts: 0,
});
function accepted(record: TaskRecord, fresh = true) {
  record.status = 'integrated';
  record.integratedCheck = { passed: true, taskDigest: taskVersion(record.task), conditions: [],
    commit: 'source', sourceDigest: 'digest', seedCommit: 'seed', changes: [],
    verification: { schema: 'deepscientist.mathematics.verification-batch/v1', status: 'kernel_verified',
      targetCommit: 'projection', sessionId: 'fixture', startedAt: 1, checkedAt: 2, durationMs: 1,
      events: [], results: [] } };
  if (fresh) markTaskAcceptance(record.integratedCheck);
  return record;
}

describe('final candidate research dispatch gate', () => {
  it.each(['research', 'sketch'] as const)('requires every fresh original goal before a %s candidate review', kind => {
    const first = accepted(node('first', 'goal')), second = node('second', 'goal'), review = node('review', kind);
    review.task = { ...review.task, reviewScope: 'final-candidate' };
    const tasks = [review, first, second];
    expect(taskCanStart(review.task, tasks)).toBe(false);
    for (const select of [readyResearchTasks, criticalPathResearchTasks, goalsFirstResearchTasks])
      expect(select(tasks)).not.toContain(review);
    accepted(second, false);
    expect(finalCandidateReviewReady(tasks)).toBe(false);
    markTaskAcceptance(second.integratedCheck!);
    expect(finalCandidateReviewReady(tasks)).toBe(true);
    expect(taskCanStart(review.task, tasks)).toBe(true);
    expect(readyResearchTasks(tasks)).toContain(review);
  });

  it('blocks legacy final review even when its ordinary research dependencies are empty or relabeled', () => {
    const review = node('independent_candidate_review', 'research');
    review.task = { ...review.task, reviewScope: 'feasibility' };
    expect(isFinalCandidateReview(review.task)).toBe(true);
    expect(taskCanStart(review.task, [review])).toBe(false);
    expect(taskCanStart(review.task, [review, node('goal', 'goal')])).toBe(false);
  });

  it.each(['conditional', 'revision', 'archived', 'source-mutated'] as const)('does not unlock on %s acceptance', flaw => {
    const goal = accepted(node('goal', 'goal')), review = node('review', 'research');
    review.task = { ...review.task, reviewScope: 'final-candidate' };
    if (flaw === 'conditional') goal.integratedCheck = { ...goal.integratedCheck!, conditions: [{ taskId: 'missing', taskDigest: 'old' }] };
    if (flaw === 'revision') goal.task = { ...goal.task, revision: 1 };
    if (flaw === 'archived') goal.integratedCheck = JSON.parse(JSON.stringify(goal.integratedCheck));
    if (flaw === 'source-mutated') (goal.integratedCheck as any).sourceDigest = 'changed-after-acceptance';
    expect(taskCanStart(review.task, [goal, review])).toBe(false);
  });

  it('keeps mathematical feasibility research available before its proof dependencies', () => {
    const goal = node('goal', 'goal'), research = node('route_audit', 'research');
    research.task = { ...research.task, reviewScope: 'feasibility', dependsOn: ['goal'] };
    expect(taskCanStart(research.task, [goal, research])).toBe(true);
    expect(isFinalCandidateReview(research.task)).toBe(false);
  });

  it('preserves and validates explicit review scope without relaxing original goal coverage', () => {
    const goal = node('goal', 'goal'), review = node('route_audit', 'research');
    const problem = { ownedFiles: ['Submission.lean'], targets: [{ proofPath: 'Submission.lean', theoremName: 'Submission.goal' }],
      declarations: { 'Submission.lean': [] } } as unknown as SolverProblem;
    const plan = { tasks: [goal.task, { ...review.task, reviewScope: 'feasibility' }] };
    expect(parseCooperationPlan(problem, plan).tasks[1].reviewScope).toBe('feasibility');
    expect(() => parseCooperationPlan(problem, { tasks: [{ ...goal.task, reviewScope: 'final-candidate' }, review.task] }))
      .toThrow('math_plan_invalid_task');
    expect(() => parseCooperationPlan(problem, { tasks: [goal.task, { ...review.task, reviewScope: 'unknown' }] }))
      .toThrow('math_plan_invalid_task');
  });
});
