import { expect, it } from 'vitest';
import { inspectKnowledgeUses } from '../src/solver/knowledgeUsage';
import type { KnowledgeContextSnapshot } from '../src/solver/knowledgeContext';
import type { TaskProof } from '../src/solver/cooperativeProof';
import type { CooperativeTask } from '../src/solver/tasks';

const task: CooperativeTask = { id: 'consumer', kind: 'lemma', revision: 0, dependsOn: [], objective: 'Use the saved bridge.',
  theoremName: 'Current.consumer', proofPath: 'Submission.lean', type: 'True' };
const knowledge = { digest: 'pinned-catalog', base: { entries: [{ id: 'saved-theorem' }] } } as KnowledgeContextSnapshot;
const claim = { id: 'saved-theorem', catalogDigest: knowledge.digest, declaration: { name: 'Current.bridge', file: 'Submission.lean' } };
const proof = { passed: true, commit: 'fixed-commit', sourceDigest: 'fixed-source', verification: { results: [] },
  references: { proof: [claim.declaration] } } as unknown as TaskProof;

it('separates a reported origin from a Lean-confirmed reference to its adapted declaration', () => {
  expect(inspectKnowledgeUses([claim], knowledge, task).uses[0]).toMatchObject({ status: 'reported-attempt', attribution: 'model-reported-origin' });
  expect(inspectKnowledgeUses([claim], knowledge, task, proof).uses[0]).toMatchObject({ status: 'checked-reference',
    attribution: 'model-reported-origin', checkedCommit: 'fixed-commit', checkedSourceDigest: 'fixed-source' });
});

it('does not upgrade unused, statement-only, wrong-file or failed declarations', () => {
  for (const changed of [
    { ...proof, passed: false },
    { ...proof, references: { ...proof.references!, proof: [], statement: [claim.declaration] } },
    { ...proof, references: { ...proof.references!, proof: [{ ...claim.declaration, file: 'Other.lean' }] } },
  ]) expect(inspectKnowledgeUses([claim], knowledge, task, changed).uses[0].status).toBe('reported-attempt');
});

it('checks original-target references only against that exact file and theorem', () => {
  const whole = { ...proof, references: undefined, verification: { ...proof.verification, results: [
    { theoremName: 'Different.consumer', proofPath: task.proofPath, declarationReferences: { proof: [claim.declaration] } },
  ] } } as unknown as TaskProof;
  expect(inspectKnowledgeUses([claim], knowledge, task, whole).uses[0].status).toBe('reported-attempt');
  whole.verification.results[0]!.theoremName = task.theoremName!;
  expect(inspectKnowledgeUses([claim], knowledge, task, whole).uses[0].status).toBe('checked-reference');
});

it('records malformed, disabled or forged usage as rejected telemetry without rejecting a proof', () => {
  expect(inspectKnowledgeUses([claim], undefined, task, proof)).toEqual({ uses: [], rejected: 1 });
  for (const invalid of [{ ...claim, id: 'forged' }, { ...claim, catalogDigest: 'changed' }, null, { ...claim, declaration: false }])
    expect(inspectKnowledgeUses([invalid], knowledge, task, proof)).toEqual({ uses: [], rejected: 1 });
  expect(inspectKnowledgeUses({}, knowledge, task)).toEqual({ uses: [], rejected: 1 });
});

it('bounds optional claims and removes duplicate records', () => {
  expect(inspectKnowledgeUses(Array.from({ length: 20 }, () => claim), knowledge, task, proof)).toMatchObject({ rejected: 4, uses: [
    expect.objectContaining({ status: 'checked-reference' }),
  ] });
});
