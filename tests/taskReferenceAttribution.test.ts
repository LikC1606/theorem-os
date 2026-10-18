import { describe, expect, it } from 'vitest';
import type { ProofReferences } from '../src/solver/proofReferences';
import { attributeTaskReferences } from '../src/solver/taskReferenceAttribution';
import { taskVersion, type TaskRecord } from '../src/solver/tasks';

const file = 'Submission/Helpers.lean';
const declaration = (name: string, proofPath = file) => ({ name, file: proofPath });
const references = (overrides: Partial<ProofReferences> = {}): ProofReferences => ({
  sourceCommit: 'source', environmentDigest: 'environment', contextDigest: 'context',
  root: declaration('Submission.Helpers.consumer'), statement: [], proof: [], inputs: [], ...overrides,
});
const record = (id: string, name = `Submission.Helpers.${id}`, options: {
  file?: string; status?: TaskRecord['status']; changes?: string[];
} = {}): TaskRecord => {
  const task = { id, kind: 'lemma' as const, objective: `Prove ${id}`, dependsOn: [], revision: 0,
    proofPath: options.file ?? file, theoremName: name, type: 'True' };
  return { task, status: options.status ?? 'integrated', attempts: 1,
    ...(options.changes ? { proof: {
      commit: 'source', seedCommit: 'seed', sourceDigest: 'source-digest', taskDigest: taskVersion(task), passed: false,
      changes: options.changes.map(name => ({ file: options.file ?? file, name, after: `lemma ${name} : True := by trivial` })),
      verification: { schema: 'deepscientist.mathematics.verification-batch/v1' as const,
        sessionId: 'session', status: 'failed' as const, targetCommit: 'source', results: [], events: [],
        startedAt: 1, checkedAt: 1, durationMs: 0 },
    } } : {}),
  };
};
const edge = (node: TaskRecord) => ({ taskId: node.task.id, taskDigest: taskVersion(node.task) });
const freeze = <T>(value: T): T => {
  if (value && typeof value === 'object') {
    for (const item of Object.values(value)) freeze(item);
    Object.freeze(value);
  }
  return value;
};

describe('formal task reference attribution', () => {
  it('does not create a task cycle from support declarations shared by two deliveries', () => {
    const shared = 'Submission.Helpers.curve_space_smoothness';
    const curve = record('curve_smoothness', undefined, { changes: [shared, 'curve_smoothness'] });
    const integral = record('derivative_integral', undefined, { changes: [shared, 'derivative_integral'] });
    const tasks = [curve, integral];
    const curveRefs = references({ root: declaration(curve.task.theoremName!), proof: [declaration(shared)],
      inputs: [{ ...declaration('curve_space_smoothness'), digest: 'support-digest' }] });
    const integralRefs = references({ root: declaration(integral.task.theoremName!),
      proof: [declaration(shared), declaration(curve.task.theoremName!)] });

    expect(attributeTaskReferences(curveRefs, tasks)).toEqual([]);
    expect(attributeTaskReferences(integralRefs, tasks)).toEqual([edge(curve)]);
    expect(curveRefs.inputs).toEqual([{ ...declaration('curve_space_smoothness'), digest: 'support-digest' }]);
  });

  it('does not attribute an already available support theorem to an unfinished replay that repaired it', () => {
    const replay = record('square_approximation_replay', undefined,
      { status: 'pending', changes: ['Submission.Helpers.finite_hybrid_mean_square_explicit'] });
    const refs = references({ proof: [declaration('Submission.Helpers.finite_hybrid_mean_square_explicit')],
      inputs: [{ ...declaration('finite_hybrid_mean_square_explicit'), digest: 'checked-support' }] });

    expect(attributeTaskReferences(refs, [replay])).toEqual([]);
  });

  it.each(['statement', 'proof'] as const)('records a genuine formal root use in the %s', scope => {
    const producer = record('producer');
    expect(attributeTaskReferences(references({ [scope]: [declaration(producer.task.theoremName!)] }), [producer]))
      .toEqual([edge(producer)]);
  });

  it('keeps a real root dependency even when the producer has not passed acceptance', () => {
    const pending = record('pending', undefined, { status: 'pending', changes: ['support'] });
    expect(attributeTaskReferences(references({ proof: [declaration(pending.task.theoremName!)] }), [pending]))
      .toEqual([edge(pending)]);
  });

  it.each([
    ['Submission.Helpers.producer', 'producer'],
    ['producer', 'Submission.Helpers.producer'],
    ['producer', 'producer'],
  ])('matches a source-level unqualified name (%s, %s)', (taskName, referenceName) => {
    const producer = record('producer', taskName);
    expect(attributeTaskReferences(references({ proof: [declaration(referenceName)] }), [producer])).toEqual([edge(producer)]);
  });

  it('does not conflate two distinct qualified names that share a short name', () => {
    const producer = record('producer', 'Submission.Helpers.producer');
    expect(attributeTaskReferences(references({ proof: [declaration('Other.producer')] }), [producer])).toEqual([]);
  });

  it('excludes the reference root and its unqualified self-reference', () => {
    const consumer = record('consumer');
    const refs = references({ root: declaration(consumer.task.theoremName!),
      statement: [declaration(consumer.task.theoremName!)], proof: [declaration('consumer')] });
    expect(attributeTaskReferences(refs, [consumer])).toEqual([]);
  });

  it('requires matching files and can reference the same short name in another file', () => {
    const own = record('consumer');
    const other = record('other', 'Submission.Helpers.consumer', { file: 'Submission/Other.lean' });
    const refs = references({ proof: [declaration('consumer', 'Submission/Other.lean')] });
    expect(attributeTaskReferences(refs, [own, other])).toEqual([edge(other)]);
    expect(attributeTaskReferences(references({ proof: [declaration('producer', 'Submission/Other.lean')] }), [record('producer')]))
      .toEqual([]);
  });

  it('does not infer edges from fingerprint inputs or an archived task edge', () => {
    const producer = record('producer');
    const refs = references({ inputs: [{ ...declaration('producer'), digest: 'fingerprint' }], tasks: [edge(producer)] });
    expect(attributeTaskReferences(refs, [producer])).toEqual([]);
  });

  it('deduplicates repeated uses and excludes advisory records', () => {
    const producer = record('producer'), advisory = record('advisory');
    advisory.task = { ...advisory.task, kind: 'research' };
    const refs = references({ statement: [declaration('producer')], proof: [declaration('producer'), declaration('advisory')] });
    expect(attributeTaskReferences(refs, [producer, advisory])).toEqual([edge(producer)]);
  });

  it('returns current task versions without mutating any declaration evidence or task record', () => {
    const producer = record('producer', undefined, { changes: ['shared_support'] });
    producer.task = { ...producer.task, revision: 3 };
    const refs = references({ proof: [declaration('producer'), declaration('shared_support')],
      inputs: [{ ...declaration('shared_support'), digest: 'support-fingerprint' }],
      tasks: [{ taskId: 'old', taskDigest: 'old-version' }] });
    const before = structuredClone({ refs, tasks: [producer] });
    freeze(refs); freeze(producer);

    expect(attributeTaskReferences(refs, [producer])).toEqual([edge(producer)]);
    expect({ refs, tasks: [producer] }).toEqual(before);
  });
});
