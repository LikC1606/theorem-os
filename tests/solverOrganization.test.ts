import { it, expect } from 'vitest';
import { assignResearchTask, type ResearchWorker } from '../src/solver/modules/organization';
import type { TaskRecord } from '../src/solver/tasks';
import { configuredSolverModules } from '../src/solver/modules';

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

it('keeps M3 priority for both proof roles under every configured scheduler', () => {
  const researcher: ResearchWorker = { id: 'researcher', role: 'researcher', worktree: '/researcher', ownedFiles: [] };
  const engineer: ResearchWorker = { ...researcher, id: 'engineer', role: 'engineer' };
  const goal: TaskRecord = { task: { id: 'original', kind: 'goal', objective: 'Original', dependsOn: [], revision: 0 }, status: 'pending', attempts: 0 };
  const research: TaskRecord = { ...goal, task: { ...goal.task, id: 'explore', kind: 'research' } };
  for (const method of ['direct', 'lemma']) for (const scheduler of ['plan', 'goals-first', 'critical-path', 'continuation', 'primary-led']) {
    const { M5 } = configuredSolverModules(method, scheduler);
    for (const worker of [researcher, engineer]) {
      expect(M5.assign([goal, research], worker, [researcher, engineer])).toBe(goal);
      expect(M5.assign([research, goal], worker, [researcher, engineer])).toBe(research);
      const pinned = { ...goal, task: { ...goal.task, ownerId: 'other' } };
      expect(M5.assign([pinned, research], worker, [researcher, engineer])).toBe(research);
      expect(M5.assign([{ ...goal, assignment: { taskId: 'original', taskDigest: 'version', workerId: 'other', seedCommit: 'seed' } }],
        worker, [researcher, engineer])).toBeUndefined();
    }
    const groups = [{ group: { id: 'main', objective: 'Proof', status: 'active' as const, revision: 0, engineerId: engineer.id }, turns: 0 }];
    expect(M5.assign([goal, research], researcher, [researcher, engineer], groups)).toBe(research);
    expect(M5.assign([goal, research], engineer, [researcher, engineer], groups)).toBe(goal);
    expect(M5.assign([goal], { ...researcher, role: 'lead' }, [researcher, engineer])).toBeUndefined();
  }
});
