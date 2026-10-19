import { describe, expect, it } from 'vitest';
import { readyResearchTasks, researchCanAdvance, taskCanStart, taskDependenciesReady } from '../src/solver/modules/search';
import { invalidatedTaskIds, markTaskReferences, taskProofContractVersion, taskVersion, type TaskRecord } from '../src/solver/tasks';

const node = (id: string, dependsOn: string[] = []): TaskRecord => ({ task: { id, kind: 'lemma', objective: id,
  theoremName: id, type: 'True', proofPath: 'Submission.lean', dependsOn, revision: 0 }, status: 'integrated', attempts: 0 });

describe('dependency readiness', () => {
  it('distinguishes descriptive proof revisions from changed mathematical contracts', () => {
    const original = node('a').task;
    const revised = { ...original, objective: 'A clearer description of the same theorem', revision: 1 };
    expect(taskVersion(revised)).not.toBe(taskVersion(original));
    expect(taskProofContractVersion(revised)).toBe(taskProofContractVersion(original));
    for (const change of [{ type: 'False' }, { premises: ['An additional assumption'] }, { dependsOn: ['new_input'] }])
      expect(taskProofContractVersion({ ...revised, ...change })).not.toBe(taskProofContractVersion(original));
    const research = { ...original, kind: 'research' as const };
    expect(taskProofContractVersion({ ...research, objective: 'A different question' })).not.toBe(taskProofContractVersion(research));
  });
  it('keeps checked proofs and consumers valid across review configuration changes', () => {
    const previous = [node('a'), node('b', ['a']), node('c', ['b'])];
    previous[0].task = { ...previous[0].task, statementReview: true, informalStatement: 'The proposition holds.' };
    const tasks = previous.map(record => ({ ...record.task }));
    tasks[0] = { ...tasks[0], statementReview: false, informalStatement: undefined };
    expect(taskVersion(tasks[0])).toBe(taskVersion(previous[0].task));
    expect([...invalidatedTaskIds(previous, tasks, new Set(), new Map())]).toEqual([]);
    tasks[0] = { ...tasks[0], statementReview: true, informalStatement: 'A revised interpretation.' };
    expect([...invalidatedTaskIds(previous, tasks, new Set(), new Map())]).toEqual([]);
    tasks[0] = { ...tasks[0], type: 'False' };
    expect([...invalidatedTaskIds(previous, tasks, new Set(), new Map())]).toEqual(['a', 'b', 'c']);
    expect(taskVersion({ ...previous[0].task, premises: ['A new assumption'] })).not.toBe(taskVersion(previous[0].task));
  });

  it('propagates revisions through effective references while preserving unrelated tasks', () => {
    const previous = [node('a'), node('b', ['a']), node('c', ['b']), node('unused', ['a']), node('unrelated')];
    const tasks = previous.map(record => record.task.id === 'a' ? { ...record.task, revision: 1 } : record.task);
    expect([...invalidatedTaskIds(previous, tasks, new Set(), new Map([['unused', []]]))]).toEqual(['a', 'b', 'c']);
  });
  it('visits shared DAG dependencies once per selection', () => {
    const tasks = [node('base')];
    let previous = ['base'], reads = 0;
    for (let i = 0; i < 20; i++) {
      const next = [`a${i}`, `b${i}`];
      for (const id of next) {
        const task = node(id, previous), dependencies = task.task.dependsOn;
        Object.defineProperty(task.task, 'dependsOn', { get: () => { reads++; return dependencies; } });
        tasks.push(task);
      }
      previous = next;
    }
    const target = node('target', previous); target.status = 'pending'; tasks.push(target);
    expect(readyResearchTasks(tasks)).toEqual([target]);
    expect(reads).toBeLessThanOrEqual(40);
  });

  it('rejects cycles and reflects mutations without stale cached readiness', () => {
    const tasks = [node('a', ['b']), node('b', ['a'])];
    expect(taskDependenciesReady(tasks[0].task, tasks)).toBe(false);
    tasks[1].task = { ...tasks[1].task, dependsOn: [] };
    expect(taskDependenciesReady(tasks[0].task, tasks)).toBe(true);
    tasks[1].status = 'pending';
    expect(taskDependenciesReady(tasks[0].task, tasks)).toBe(false);
    tasks[0].task = { ...tasks[0].task, conditional: true };
    expect(taskCanStart(tasks[0].task, tasks)).toBe(true);
  });

  it('checks future progress once per shared dependency and reflects cycles and stopped owners', () => {
    const tasks = [node('base')];
    let previous = ['base'], reads = 0;
    for (let index = 0; index < 20; index++) {
      const next = [`a${index}`, `b${index}`];
      for (const id of next) {
        const record = node(id, previous), dependencies = record.task.dependsOn;
        record.status = 'pending';
        Object.defineProperty(record.task, 'dependsOn', { get: () => { reads++; return dependencies; } });
        tasks.push(record);
      }
      previous = next;
    }
    const target = node('target', previous); target.status = 'pending';
    tasks.unshift(target);
    expect(researchCanAdvance(tasks, undefined, new Set())).toBe(true);
    expect(reads).toBeLessThanOrEqual(40);
    const owned = node('owned'); owned.status = 'pending'; owned.task.ownerId = 'peer';
    expect(researchCanAdvance([owned], undefined, new Set())).toBe(false);
    expect(researchCanAdvance([owned], undefined, new Set(['peer']))).toBe(true);
    owned.task.dependsOn = ['owned'];
    expect(researchCanAdvance([owned], undefined, new Set(['peer']))).toBe(false);
    owned.task.dependsOn = ['missing'];
    expect(researchCanAdvance([owned], undefined, new Set(['peer']))).toBe(false);
  });

  it('requires dependency receipts to match the current task version', () => {
    const dependency = node('a'), target = node('target', ['a']);
    target.integratedCheck = { commit: 'checked', sourceDigest: 'source', passed: true, taskDigest: taskVersion(target.task), seedCommit: 'seed', changes: [],
      verification: { schema: 'deepscientist.mathematics.verification-batch/v1', status: 'kernel_verified', targetCommit: 'checked',
        sessionId: 'test', events: [], startedAt: 1, checkedAt: 2, durationMs: 1, results: [] },
      references: { tasks: [{ taskId: 'a', taskDigest: taskVersion(dependency.task) }], inputs: [], contextDigest: 'context',
        sourceCommit: 'checked', environmentDigest: 'env', root: { name: 'target', file: 'Submission.lean' }, statement: [], proof: [] } };
    markTaskReferences(target.integratedCheck);
    expect(taskDependenciesReady(target.task, [dependency, target])).toBe(true);
    dependency.task = { ...dependency.task, revision: dependency.task.revision + 1 };
    expect(taskDependenciesReady(target.task, [dependency, target])).toBe(false);
  });
});
