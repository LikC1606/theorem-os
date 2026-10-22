import { describe, expect, it } from 'vitest';
import { configuredSolverModules } from '../src/solver/modules';
import { buildResearchContext } from '../src/solver/modules/context';
import { assignResearchReviewer, defaultResearchRouteConcurrency, researchRouteGroups, researchWorkers,
  type ResearchWorker } from '../src/solver/modules/organization';
import type { SolverProblem } from '../src/solver/problem';
import type { SolverRunState } from '../src/solver/archive';
import { taskVersion, type CooperativeAction, type CooperativeTask, type TaskRecord } from '../src/solver/tasks';

const node = (id: string, kind: CooperativeTask['kind'] = 'lemma'): TaskRecord => ({
  task: { id, kind, objective: `Resolve the ${id} inference`, dependsOn: [], revision: 0,
    ...(['lemma', 'goal'].includes(kind) ? { proofPath: 'Submission.lean', theoremName: id,
      type: '∀ (n : Nat), n = n', conditional: false } : {}) },
  status: 'pending', attempts: 0,
});
const occupy = (record: TaskRecord, worker: ResearchWorker) => {
  record.status = 'running';
  record.assignment = { taskId: record.task.id, taskDigest: taskVersion(record.task), workerId: worker.id, seedCommit: 'seed' };
};

describe('proof-writing responsibilities', () => {
  it.each([1, 2, 3, 4])('keeps the legacy %i-worker roster', count => {
    const workers = researchWorkers('/proof', ['Submission.lean'], count);
    expect(workers.map(worker => worker.id)).toEqual(count === 1 ? ['solver'] :
      ['solver', ...Array.from({ length: count - 2 }, (_, index) => `researcher-${index + 1}`), 'engineer']);
    expect(workers.some(worker => worker.role === 'prover')).toBe(false);
  });

  it.each([5, 6, 7, 8])('adds %i-worker proof capacity with unique worktrees', count => {
    const workers = researchWorkers('/proof', ['Submission.lean'], count);
    expect(workers.filter(worker => worker.role === 'researcher')).toHaveLength(2);
    expect(workers.filter(worker => worker.role === 'prover')).toHaveLength(count - 4);
    expect(workers.at(-1)?.role).toBe('engineer');
    expect(new Set(workers.map(worker => worker.id)).size).toBe(count);
    expect(new Set(workers.map(worker => worker.worktree)).size).toBe(count);
  });

  it.each(['plan', 'critical-path', 'continuation'])('%s dispatches seven distinct useful tasks across the expanded roster', scheduler => {
    const workers = researchWorkers('/proof', ['Submission.lean'], 8), peers = workers.slice(1);
    const tasks = [node('goal', 'goal'), ...Array.from({ length: 4 }, (_, i) => node(`helper_${i}`)),
      node('route_analysis', 'research'), node('library_interface', 'research')];
    const groups = researchRouteGroups([{ id: 'main', objective: 'Proof route', status: 'active', revision: 0 }], workers)
      .map(group => ({ group, turns: 0 }));
    const modules = configuredSolverModules('direct', scheduler);
    const assignments = peers.map(worker => {
      const selected = modules.M5.assign(modules.M3.ready(tasks, groups), worker, peers, groups, tasks);
      expect(selected, worker.id).toBeDefined();
      occupy(selected!, worker);
      return { role: worker.role, kind: selected!.task.kind };
    });
    expect(assignments).toEqual([
      { role: 'researcher', kind: 'research' }, { role: 'researcher', kind: 'research' },
      ...Array.from({ length: 4 }, () => ({ role: 'prover', kind: 'lemma' })),
      { role: 'engineer', kind: 'goal' },
    ]);
    expect(tasks.filter(task => task.status === 'running')).toHaveLength(7);
  });

  it('keeps Provers on typed lemmas and respects ownership and dependency readiness', () => {
    const workers = researchWorkers('/proof', [], 8), prover = workers.find(worker => worker.role === 'prover')!;
    const modules = configuredSolverModules('direct', 'plan'), lemma = node('helper');
    const untyped = { ...lemma, task: { ...lemma.task, id: 'untyped', type: undefined } };
    expect(modules.M5.assign([node('notes', 'research'), node('sketch', 'sketch'), node('goal', 'goal'), untyped], prover, workers))
      .toBeUndefined();
    const owned = { ...lemma, task: { ...lemma.task, ownerId: 'prover-2' } };
    expect(modules.M5.assign([owned], prover, workers)).toBeUndefined();
    lemma.task = { ...lemma.task, dependsOn: ['input'] };
    const tasks = [node('input'), lemma];
    expect(modules.M3.ready(tasks)).not.toContain(lemma);
    lemma.task = { ...lemma.task, dependsOn: [] };
    expect(modules.M5.assign(modules.M3.ready(tasks), prover, workers)).toBe(tasks[0]);
  });

  it('leaves a Prover waiting when only advisory work is ready and permits independent review', () => {
    const workers = researchWorkers('/proof', [], 8), prover = workers.find(worker => worker.role === 'prover')!;
    const modules = configuredSolverModules('direct', 'plan');
    expect(modules.M5.assign([node('research', 'research')], prover, workers)).toBeUndefined();
    expect(assignResearchReviewer(workers, prover.id)).toMatchObject({ role: 'researcher' });
    expect(assignResearchReviewer([workers[0], prover], prover.id)).toBeUndefined();
  });

  it('lets generalists prove spare lemmas when their preferred work is unavailable', () => {
    const workers = researchWorkers('/proof', [], 8), lemma = node('helper');
    const modules = configuredSolverModules('direct', 'plan');
    for (const worker of workers.filter(worker => ['researcher', 'engineer'].includes(worker.role)))
      expect(modules.M5.assign([lemma], worker, workers)).toBe(lemma);
  });

  it('expands unspecified route capacity and preserves explicit limits and legacy defaults', () => {
    const workers = researchWorkers('/proof', [], 8);
    const groups = [{ id: 'main', objective: 'Proof', status: 'active' as const, revision: 0 },
      { id: 'limited', objective: 'Limited route', status: 'active' as const, revision: 0, maxConcurrent: 2 }];
    expect(defaultResearchRouteConcurrency(workers)).toBe(7);
    expect(researchRouteGroups(groups, workers).map(group => group.maxConcurrent)).toEqual([7, 2]);
    expect(researchRouteGroups(groups, researchWorkers('/proof', [], 4))).toEqual(groups);
    expect(groups[0]).not.toHaveProperty('maxConcurrent');
    const routes = [{ group: { ...groups[0], maxConcurrent: 2 }, turns: 0 }], tasks = [node('a'), node('b'), node('c')];
    occupy(tasks[0], workers[3]); occupy(tasks[1], workers[4]);
    expect(configuredSolverModules('direct', 'plan').M3.ready(tasks, routes)).toEqual([]);
  });
});

describe('proof-writing context', () => {
  const helper = node('helper');
  const problem = { projectRelative: '.', ownedFiles: ['Submission.lean'], declarations: {}, targets: [], receiptDigest: 'problem',
    baseCommit: 'seed', contract: { formalStatement: 'theorem target : True := by sorry', assumptions: [] } } as unknown as SolverProblem;
  const build = (action: CooperativeAction) => buildResearchContext(problem, {
    workers: researchWorkers('/proof', ['Submission.lean'], 8), cooperation: { tasks: [helper] },
  } as unknown as SolverRunState, { root: '/runtime', worktree: '/proof', environment: {}, taskText: 'Prove the target',
    retrievalRoot: '/library', frozenContexts: { 'Submission.lean': 'theorem target : True := /- body omitted -/' }, assignment: action });

  it('tells a typed helper writer to save a proof and keeps its exact interface mandatory', () => {
    const action: CooperativeAction = { kind: 'task', task: helper.task,
      assignment: { taskId: helper.task.id, taskDigest: taskVersion(helper.task), workerId: 'prover-1', seedCommit: 'seed' } };
    const context = build(action);
    expect(context.instructions).toContain('You are a Lean Prover.');
    expect(context.instructions).toContain('return for host checking and integration');
    expect(context.instructions).not.toContain('You are a Mathematical Researcher.');
    expect(context.message).toContain('Your role: prover');
    expect(context.message).toContain(JSON.stringify(helper.task.type));
  });

  it('gives Lead the actual proof roster and the expanded route capacity', () => {
    const context = build({ kind: 'lead', seedCommit: 'seed' });
    expect(context.instructions).toContain('"id":"prover-4","role":"prover"');
    expect(context.instructions).toContain('Provers claim only typed lemma tasks');
    expect(context.instructions).toContain('unspecified route maxConcurrent uses 7 task slots');
    expect(context.instructions).toContain('let Provers wait');
  });
});
