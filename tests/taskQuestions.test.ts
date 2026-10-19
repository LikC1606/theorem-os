import { expect, it } from 'vitest';
import { configuredSolverModules } from '../src/solver/modules';
import { hasRunningDuplicateQuestion, parallelQuestions } from '../src/solver/taskQuestions';
import type { TaskRecord } from '../src/solver/tasks';

const question = (id: string, groupId = 'main'): TaskRecord => ({ task: { id, groupId, sharing: 'problem',
  kind: 'research', objective: 'Find an application of the injectivity hypothesis', dependsOn: [], revision: 0 },
  status: 'pending', attempts: 0 });

it('prevents every scheduler from concurrently assigning an identical public question', () => {
  const first = question('first', 'left'), second = question('second', 'right'), different = question('different', 'right');
  different.task = { ...different.task, objective: 'Test a counterexample to the surjectivity claim' };
  first.status = 'running';
  const tasks = [first, second, different];
  const worker = { id: 'researcher', role: 'researcher' as const, worktree: '/proof', ownedFiles: [] };
  for (const scheduler of ['plan', 'continuation', 'primary-led', 'goals-first', 'critical-path'])
    expect(configuredSolverModules('direct', scheduler).M5.assign([second, different], worker, [worker], undefined, tasks)).toBe(different);
  first.status = 'completed';
  expect(hasRunningDuplicateQuestion(second, tasks)).toBe(false);
});

it('keeps independent reviews, different inputs and private groups separate', () => {
  const first = question('first', 'left'), second = question('second', 'right');
  first.status = 'running';
  first.task = { ...first.task, sharing: 'group' };
  expect(hasRunningDuplicateQuestion(second, [first, second])).toBe(false);
  second.task = { ...second.task, groupId: 'left', reviewScope: 'feasibility' };
  expect(hasRunningDuplicateQuestion(second, [first, second])).toBe(false);
  second.task = { ...second.task, reviewScope: undefined, dependsOn: ['new_input'] };
  expect(hasRunningDuplicateQuestion(second, [first, second])).toBe(false);
});

it('projects public in-flight metadata without private task content or proof state', () => {
  const current = question('current'), shared = question('shared', 'other'), secret = question('secret', 'other');
  shared.status = secret.status = 'running';
  shared.finding = 'NOT_PART_OF_QUESTION_METADATA';
  secret.task = { ...secret.task, sharing: 'group', objective: 'PRIVATE_QUESTION' };
  const rows = parallelQuestions([current, shared, secret], current.task);
  expect(rows.map(row => row.taskId)).toEqual(['shared']);
  expect(JSON.stringify(rows)).not.toContain('PRIVATE_QUESTION');
  expect(JSON.stringify(rows)).not.toContain('NOT_PART_OF_QUESTION_METADATA');
});
