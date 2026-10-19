import { describe, expect, it } from 'vitest';
import type { TaskProof } from '../src/solver/cooperativeProof';
import { taskDependenciesReady } from '../src/solver/modules/search';
import type { ProofReferences } from '../src/solver/proofReferences';
import { attributeTaskReferences } from '../src/solver/taskReferenceAttribution';
import { markTaskReferences, taskReferenceDependencies, taskVersion, type TaskRecord } from '../src/solver/tasks';

const helper = 'Submission/Helpers.lean';
const node = (id: string, name = id, dependsOn: string[] = []): TaskRecord => ({
  task: { id, kind: 'lemma', objective: id, theoremName: `Submission.Helpers.${name}`,
    type: 'True', proofPath: helper, dependsOn, revision: 0 }, status: 'integrated', attempts: 1,
});
const references = (record: TaskRecord, uses: Partial<Pick<ProofReferences, 'statement' | 'proof'>> = {}): ProofReferences => ({
  root: { name: record.task.theoremName!, file: record.task.proofPath! }, statement: [], proof: [], ...uses,
  sourceCommit: 'checked', environmentDigest: 'env', contextDigest: 'context',
  inputs: [{ file: record.task.proofPath!, name: record.task.theoremName!.split('.').at(-1)!, digest: 'root' },
    ...[...uses.statement ?? [], ...uses.proof ?? []].map(reference => ({
      file: reference.file, name: reference.name.split('.').at(-1)!, digest: 'dependency',
    }))],
});
const proof = (record: TaskRecord, actualReferences: ProofReferences, changes: TaskProof['changes'] = []): TaskProof => ({
  commit: 'checked', sourceDigest: 'source', passed: true, taskDigest: taskVersion(record.task), seedCommit: 'seed', changes,
  references: actualReferences,
  verification: { schema: 'deepscientist.mathematics.verification-batch/v1', status: 'kernel_verified', targetCommit: 'checked',
    sessionId: 'test', events: [], startedAt: 1, checkedAt: 2, durationMs: 1, results: [] },
});
function attach(record: TaskRecord, tasks: TaskRecord[], actualReferences: ProofReferences) {
  actualReferences.tasks = attributeTaskReferences(actualReferences, tasks);
  record.integratedCheck = proof(record, actualReferences);
  markTaskReferences(record.integratedCheck);
}

describe('proof reference task ownership', () => {
  it('keeps a root fingerprint copied in another delivery from creating a false dependency cycle', () => {
    const roots = node('recover', 'roots_between_alternating_eval');
    const rounded = node('rounded', 'rounded_certificate', ['recover']);
    rounded.proof = proof(rounded, references(rounded), [
      { file: helper, name: 'roots_between_alternating_eval', after: 'lemma roots_between_alternating_eval : True := by trivial' },
      { file: helper, name: 'rounded_certificate', after: 'lemma rounded_certificate : True := by trivial' },
    ]);
    const tasks = [roots, rounded], rootReferences = references(roots);
    const fingerprints = structuredClone(rootReferences.inputs);
    attach(roots, tasks, rootReferences);
    expect(rootReferences.tasks).toEqual([]);
    expect(taskDependenciesReady(roots.task, tasks)).toBe(true);
    expect(rootReferences.inputs).toEqual(fingerprints);

    attach(rounded, tasks, references(rounded, { proof: [{ file: helper, name: roots.task.theoremName! }] }));
    expect(rounded.integratedCheck!.references!.tasks).toEqual([{ taskId: 'recover', taskDigest: taskVersion(roots.task) }]);
    expect(tasks.every(record => taskDependenciesReady(record.task, tasks))).toBe(true);
  });

  it('does not infer task ownership from a fingerprint without a kernel-reported use', () => {
    const producer = node('producer'), consumer = node('consumer');
    producer.proof = proof(producer, references(producer), [{ file: helper, name: 'support', after: 'lemma support : True := by trivial' }]);
    const actualReferences = references(consumer);
    actualReferences.inputs.push({ file: helper, name: 'support', digest: 'fingerprint-only' });
    expect(attributeTaskReferences(actualReferences, [producer, consumer])).toEqual([]);
  });

  it('does not attribute an actual self reference to another task that copied the root', () => {
    const consumer = node('consumer'), copier = node('copier');
    copier.proof = proof(copier, references(copier), [{ file: helper, name: 'consumer', after: 'def consumer := consumer' }]);
    expect(attributeTaskReferences(references(consumer, { proof: [{ file: helper, name: consumer.task.theoremName! }] }),
      [consumer, copier])).toEqual([]);
  });

  it.each(['statement', 'proof'] as const)('retains real %s dependencies and rejects a changed dependency version', scope => {
    const producer = node('producer'), consumer = node('consumer');
    const actualReferences = references(consumer, { [scope]: [{ file: helper, name: producer.task.theoremName! }] });
    attach(consumer, [producer, consumer], actualReferences);
    expect(actualReferences.tasks).toEqual([{ taskId: 'producer', taskDigest: taskVersion(producer.task) }]);
    expect(taskDependenciesReady(consumer.task, [producer, consumer])).toBe(true);
    producer.task = { ...producer.task, revision: producer.task.revision + 1 };
    expect(taskDependenciesReady(consumer.task, [producer, consumer])).toBe(false);
  });

  it('preserves supporting helper source inputs without attributing ownership to an unrelated task root', () => {
    const producer = node('producer'), consumer = node('consumer');
    producer.task = { ...producer.task, proofPath: 'Submission.lean', theoremName: 'Submission.producer' };
    producer.proof = proof(producer, references(producer), [{ file: helper, name: 'support', after: 'lemma support : True := by trivial' }]);
    const actualReferences = references(consumer, { proof: [{ file: helper, name: 'Submission.Helpers.support' }] });
    const fingerprints = structuredClone(actualReferences.inputs);
    attach(consumer, [producer, consumer], actualReferences);
    expect(actualReferences.tasks).toEqual([]);
    expect(actualReferences.inputs).toEqual(fingerprints);
    expect(actualReferences.inputs).toContainEqual({ file: helper, name: 'support', digest: 'dependency' });
  });

  it('continues to reject cycles formed by actual references', () => {
    const first = node('first'), second = node('second'), tasks = [first, second];
    attach(first, tasks, references(first, { proof: [{ file: helper, name: second.task.theoremName! }] }));
    attach(second, tasks, references(second, { statement: [{ file: helper, name: first.task.theoremName! }] }));
    expect(tasks.every(record => !taskDependenciesReady(record.task, tasks))).toBe(true);
  });

  it('preserves the declared dependency fallback for whole-module fingerprints', () => {
    const producer = node('producer'), consumer = node('consumer', 'consumer', ['producer']);
    producer.status = 'blocked';
    const actualReferences = references(consumer, { proof: [{ file: helper, name: 'Submission.Helpers.generated._proof_1' }] });
    actualReferences.inputs.push({ file: helper, digest: 'whole-module' });
    attach(consumer, [producer, consumer], actualReferences);
    expect(taskReferenceDependencies(consumer)).toBeUndefined();
    expect(taskDependenciesReady(consumer.task, [producer, consumer])).toBe(false);
  });

  it('does not let restored reference metadata bypass an unchecked declared dependency', () => {
    const producer = node('producer'), consumer = node('consumer', 'consumer', ['producer']);
    producer.status = 'blocked';
    const actualReferences = { ...references(consumer), tasks: [] };
    consumer.integratedCheck = proof(consumer, actualReferences);
    expect(taskReferenceDependencies(consumer)).toBeUndefined();
    expect(taskDependenciesReady(consumer.task, [producer, consumer])).toBe(false);
  });
});
