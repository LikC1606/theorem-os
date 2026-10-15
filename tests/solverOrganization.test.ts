import { it, expect } from 'vitest';
import { assignResearchTask, type ResearchWorker } from '../src/solver/modules/organization';
import type { TaskRecord } from '../src/solver/tasks';

it('lets an idle engineer advance independent research while respecting priority and ownership', () => {
  const engineer: ResearchWorker = { id: 'engineer', role: 'engineer', worktree: '/engineer', ownedFiles: [] };
  const researcher: ResearchWorker = { ...engineer, id: 'researcher', role: 'researcher' };
  const research: TaskRecord = { task: { id: 'definition-consistency', kind: 'research', objective: 'Check definitions', dependsOn: [], revision: 0 }, status: 'pending', attempts: 0 };
  const goal: TaskRecord = { ...research, task: { ...research.task, id: 'goal', kind: 'goal' } };
  const live = [engineer, researcher];
  expect(assignResearchTask([research], engineer, live)).toBe(research);
  expect(assignResearchTask([research, goal], engineer, live)).toBe(goal);
  expect(assignResearchTask([research, goal], engineer, [engineer])).toBe(research);
  expect(assignResearchTask([{ ...research, task: { ...research.task, ownerId: researcher.id } }], engineer, live)).toBeUndefined();
  expect(assignResearchTask([goal], researcher, live, [{ group: { id: 'main', objective: 'Proof', status: 'active', revision: 0, engineerId: engineer.id }, turns: 0 }])).toBeUndefined();
});
