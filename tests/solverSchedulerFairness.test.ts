import { describe, expect, it } from 'vitest';
import { configuredSolverModules } from '../src/solver/modules';
import { researchWorkers } from '../src/solver/modules/organization';
import { taskVersion, type TaskRecord } from '../src/solver/tasks';

const node = (id: string, kind: 'goal' | 'lemma' = 'lemma', dependsOn: string[] = []): TaskRecord => ({
  task: { id, kind, objective: id, dependsOn, revision: 0, conditional: false,
    type: 'True', theoremName: id, proofPath: 'Submission.lean' },
  status: 'pending', attempts: 0,
});

describe.each(['plan', 'critical-path', 'continuation'])('%s original-goal coverage', scheduler => {
  it.each([false, true])('starts an uncovered goal prerequisite in the last proof slot (shared input: %s)', shared => {
    const workers = researchWorkers('/fixture', [], 4), proofWorkers = workers.slice(1);
    const running = [node('working_a'), node('working_b')];
    running.forEach((record, index) => {
      record.status = 'running';
      record.assignment = { taskId: record.task.id, taskDigest: taskVersion(record.task),
        workerId: proofWorkers[index]!.id, seedCommit: 'fixture' };
    });
    const core = node('core'), initial = node('initial_factor'), factor = node('factor_gt_one');
    const tasks = [...running, core, initial, factor,
      node('invariance', 'goal', ['working_a', 'working_b', 'core']),
      ...(shared ? [node('terminal_value', 'goal', ['working_a', 'core'])] : []),
      node('mval_gt_one', 'goal', ['initial_factor', 'factor_gt_one'])];
    const modules = configuredSolverModules('direct', scheduler), before = structuredClone(tasks);
    const ready = modules.M3.ready(tasks);
    expect(ready[0]).toBe(core);
    expect(modules.M5.assign(ready, proofWorkers[2]!, workers, undefined, tasks)).toBe(initial);
    expect(tasks).toEqual(before);

    // Once the first independent input has finished, the next input stays
    // eligible for the same coverage reservation instead of waiting for core.
    initial.status = 'completed';
    expect(modules.M5.assign(modules.M3.ready(tasks), proofWorkers[2]!, workers, undefined, tasks)).toBe(factor);
  });

  it('keeps M3 ordering when every original goal already has a running proof task', () => {
    const workers = researchWorkers('/fixture', [], 4), proofWorkers = workers.slice(1);
    const running = [node('working_a'), node('working_b')];
    running.forEach((record, index) => {
      record.status = 'running';
      record.assignment = { taskId: record.task.id, taskDigest: taskVersion(record.task),
        workerId: proofWorkers[index]!.id, seedCommit: 'fixture' };
    });
    const core = node('core'), factor = node('factor_gt_one');
    const tasks = [...running, core, factor, node('invariance', 'goal', ['working_a', 'core']),
      node('mval_gt_one', 'goal', ['working_b', 'factor_gt_one'])];
    const modules = configuredSolverModules('direct', scheduler);
    expect(modules.M5.assign(modules.M3.ready(tasks), proofWorkers[2]!, workers, undefined, tasks)).toBe(core);
  });
});
