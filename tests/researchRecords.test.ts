import { describe, expect, it } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { captureResearchBasis, researchBasisSchema, researchRecordSchema, researchSourceDigest, restoreResearch,
  settleResearch, type ResearchView } from '../src/solver/researchRecords';
import { taskVersion, type CooperativeTask, type TaskAssignment } from '../src/solver/tasks';
import type { DeliveryRecord } from '../src/solver/deliveries';

const research: CooperativeTask = { id: 'route', kind: 'research', objective: 'Find a sufficient route',
  dependsOn: ['library'], revision: 0 };
const library: CooperativeTask = { id: 'library', kind: 'research', objective: 'Inspect the pinned library',
  dependsOn: ['bound'], revision: 0 };
const bound: CooperativeTask = { id: 'bound', kind: 'lemma', objective: 'Prove the bound', dependsOn: [], revision: 0,
  type: 'True', proofPath: 'Helpers.lean', theoremName: 'Helpers.bound' };
const finding = 'The requested rank-only estimate has a diagonal counterexample.';
const sources = { 'Helpers.lean': 'lemma bound : True := by trivial\n', 'Submission.lean': 'theorem goal : True := by sorry\n' };

function fixture(): ResearchView {
  return { problemReceiptDigest: 'fixture-problem', environmentDigest: 'fixture-environment',
    retrievalDigest: 'fixture-corpus', knowledgeDigest: 'fixture-knowledge', sourceDigest: researchSourceDigest(sources),
    tasks: [{ task: research, status: 'running' }, { task: library, status: 'completed', finding: 'No uniform estimate found.' },
      { task: bound, status: 'integrated', integratedCheck: { taskDigest: taskVersion(bound), passed: true, conditions: [] } }],
    deliveries: [] };
}
const assignment = (task: CooperativeTask, id = 'first-assignment'): TaskAssignment => ({ taskId: task.id,
  taskDigest: taskVersion(task), workerId: 'researcher', seedCommit: 'fixture-seed', assignmentId: id });
const publish = (view: ResearchView, task = research, id = 'publication-a', complete = true) => settleResearch({
  id, assignment: assignment(task, id), basis: captureResearchBasis(task, view), commit: 'fixture-publication', finding, complete })!;
const delivery = (task = library): DeliveryRecord => ({ id: 'library-publication', producer: 'researcher', taskId: task.id,
  taskDigest: taskVersion(task), kind: 'research', status: 'advisory', statement: task.objective, premises: [],
  dependencies: [], remainingObligations: ['Prove the discriminating bound'], summary: 'An exact library result was found.',
  evidenceRefs: ['Mathlib/Exact/Path.lean'], finding: 'A weaker bound is available under an extra hypothesis.', createdAt: 1 });

describe('immutable research completion records', () => {
  it('keeps the actual older input when the source changes before the first continuation', () => {
    const original = fixture(), record = publish(original);
    const newer = { ...original, sourceDigest: researchSourceDigest({ ...sources, 'Helpers.lean': sources['Helpers.lean'] +
      'lemma useful_bridge : True := by trivial\n' }) };
    expect(restoreResearch(record, research, original, finding)).toEqual({ status: 'completed', reason: 'restored' });
    expect(restoreResearch(record, research, newer, finding)).toEqual({ status: 'pending', reason: 'inputs-changed' });
    expect(record.basis.sourceDigest).toBe(original.sourceDigest);
  });

  it('invalidates a completed investigation when a dependency publishes a new finding under the same task contract', () => {
    const original = fixture(), record = publish(original);
    const newer = { ...original, tasks: original.tasks.map(node => node.task.id === library.id
      ? { ...node, finding: 'A uniform estimate is impossible; here is the explicit counterexample.' } : node) };
    expect(taskVersion(newer.tasks[1]!.task)).toBe(taskVersion(library));
    expect(restoreResearch(record, research, newer, finding)).toEqual({ status: 'pending', reason: 'inputs-changed' });
  });

  it('includes semantic deliveries from transitive dependencies and ignores their publication metadata', () => {
    const original = fixture(), input = delivery(bound);
    const first = { ...original, deliveries: [input] }, record = publish(first);
    const metadataOnly = { ...first, deliveries: [{ ...input, id: 'republished', producer: 'engineer', createdAt: 99,
      commit: 'fresh-commit', assignmentKey: 'fresh-assignment', submissionId: 'new-submission' }] };
    expect(restoreResearch(record, research, metadataOnly, finding).status).toBe('completed');
    const changed = { ...first, deliveries: [{ ...input, finding: 'The bound requires an additional inequality.' }] };
    expect(restoreResearch(record, research, changed, finding).status).toBe('pending');
    const changedObligation = { ...first, deliveries: [{ ...input, remainingObligations: ['Resolve a different exact gap'] }] };
    expect(restoreResearch(record, research, changedObligation, finding).status).toBe('pending');
  });

  it('ignores an unrelated inbox and newly issued proof receipts', () => {
    const original = fixture(), record = publish(original);
    const actualProof = { taskDigest: taskVersion(bound), passed: true, conditions: [], commit: 'new-check-commit',
      sourceDigest: 'renewed-source-wrapper', seedCommit: 'new-seed', changes: [],
      verification: { receiptId: 'fresh-receipt', status: 'kernel_verified' } };
    const otherTask = { ...library, id: 'unrelated' };
    const newer: ResearchView = { ...original, deliveries: [delivery(otherTask)], tasks: original.tasks.map(node =>
      node.task.id === bound.id ? { ...node, integratedCheck: actualProof } : node) };
    expect(restoreResearch(record, research, newer, finding)).toEqual({ status: 'completed', reason: 'restored' });
  });

  it('treats a fresh completion with the same text as a new publication on its own current basis', () => {
    const firstView = fixture(), first = publish(firstView);
    const nextView = { ...firstView, sourceDigest: researchSourceDigest({ ...sources, 'Bridge.lean': 'lemma bridge : True := by trivial\n' }) };
    const next = publish(nextView, research, 'publication-b');
    expect(first.findingDigest).toBe(next.findingDigest);
    expect(first.id).not.toBe(next.id);
    expect(first.assignmentKey).not.toBe(next.assignmentKey);
    expect(next.basis.sourceDigest).toBe(nextView.sourceDigest);
    expect(restoreResearch(next, research, nextView, finding)).toEqual({ status: 'completed', reason: 'restored' });
    expect(restoreResearch(first, research, nextView, finding).status).toBe('pending');
  });

  it('requires a complete record and its full bound finding', () => {
    const view = fixture(), record = publish(view);
    expect(restoreResearch(undefined, research, view, finding).reason).toBe('missing-record');
    expect(restoreResearch(publish(view, research, 'checkpoint', false), research, view, finding).reason).toBe('incomplete');
    expect(restoreResearch(record, research, view).reason).toBe('finding-changed');
    expect(restoreResearch(record, research, view, finding + ' Changed assumptions.').reason).toBe('finding-changed');
    expect(settleResearch({ id: 'legacy-publication', assignment: assignment(research), commit: 'legacy-commit',
      finding, complete: true })).toBeUndefined();
  });

  it('restores ordinary sketches, while reviews and proof tasks never become completed from a research record', () => {
    const view = fixture(), sketch = { ...research, kind: 'sketch' as const }, record = publish(view, sketch);
    expect(restoreResearch(record, sketch, view, finding).status).toBe('completed');
    for (const task of [{ ...research, reviewScope: 'feasibility' as const },
      { ...research, reviewScope: 'final-candidate' as const }, { ...research, id: 'independent_candidate_review' }, bound]) {
      expect(restoreResearch(record, task, view, finding)).toEqual({ status: 'pending', reason: 'not-ordinary-research' });
    }
  });

  it('compares proof conditions and current semantic proof availability', () => {
    const original = fixture(), record = publish(original), reference = { taskId: library.id, taskDigest: taskVersion(library) };
    const changed = { ...original, tasks: original.tasks.map(node => node.task.id === bound.id
      ? { ...node, status: 'conditional' as const, integratedCheck: { passed: true, taskDigest: taskVersion(bound), conditions: [reference] } } : node) };
    expect(restoreResearch(record, research, changed, finding).status).toBe('pending');
    const unproved = { ...original, tasks: original.tasks.map(node => node.task.id === bound.id
      ? { task: node.task, status: 'pending' as const } : node) };
    expect(restoreResearch(record, research, unproved, finding).status).toBe('pending');
    const noReceipt = publish(unproved), running = { ...unproved, tasks: unproved.tasks.map(node => node.task.id === bound.id
      ? { ...node, status: 'running' as const } : node) };
    expect(restoreResearch(noReceipt, research, running, finding).status).toBe('completed');
  });

  it('requires the same problem, environment, retrieval and knowledge inputs and mathematical task version', () => {
    const view = fixture(), record = publish(view);
    for (const key of ['problemReceiptDigest', 'environmentDigest', 'retrievalDigest', 'knowledgeDigest'] as const) {
      expect(restoreResearch(record, research, { ...view, [key]: 'different-identity' }, finding).status).toBe('pending');
    }
    expect(restoreResearch(record, { ...research, revision: 1 }, view, finding).reason).toBe('task-changed');
    expect(restoreResearch(record, { ...research, ownerId: 'engineer', status: 'paused' }, view, finding).status).toBe('completed');
  });

  it('rejects another assignment task and freezes independently of mutable caller data', () => {
    const view = fixture(), basis = structuredClone(captureResearchBasis(research, view)), record = settleResearch({
      id: 'publication', assignment: assignment(research), basis, commit: 'fixture-commit', finding, complete: true })!;
    expect(() => settleResearch({ id: 'wrong-task', assignment: assignment(library), basis,
      commit: 'fixture-commit', finding, complete: true })).toThrow('math_research_basis_assignment_changed');
    Object.assign(basis, { sourceDigest: 'caller-changed-after-publication' });
    expect(record.basis.sourceDigest).toBe(view.sourceDigest);
    expect(Object.isFrozen(record)).toBe(true);
    expect(Object.isFrozen(record.basis.dependencies)).toBe(true);
    expect(Object.isFrozen(record.basis.dependencies[0])).toBe(true);
    expect(record).not.toHaveProperty('finding');
  });

  it('uses stable computed digests while schemas allow existing nonempty fixture identities', () => {
    expect(researchSourceDigest(sources)).toBe(researchSourceDigest(Object.fromEntries(Object.entries(sources).reverse())));
    const basis = captureResearchBasis(research, fixture()), record = publish(fixture());
    expect(basis.sourceDigest).toMatch(/^[a-f0-9]{64}$/u);
    expect(record.findingDigest).toBe(mathDigest(finding));
    expect(researchBasisSchema.parse(basis)).toEqual(basis);
    expect(researchRecordSchema.parse(record)).toEqual(record);
    expect(researchRecordSchema.safeParse({ ...record, findingDigest: 'not-a-computed-digest' }).success).toBe(false);
    expect(researchRecordSchema.safeParse({ ...record, taskId: 'mismatched' }).success).toBe(false);
    expect(researchRecordSchema.safeParse({ ...record, id: '' }).success).toBe(false);
  });

  it('does not use stale or superseded dependency deliveries or its own output as new inputs', () => {
    const original = fixture(), record = publish(original);
    const newer = { ...original, deliveries: [{ ...delivery(), taskDigest: 'obsolete-version' },
      { ...delivery(), status: 'superseded' as const }, delivery(research)] };
    expect(restoreResearch(record, research, newer, finding).status).toBe('completed');
  });

  it('records a missing transitive task so its later appearance changes the basis', () => {
    const original = fixture(), missing = { ...original, tasks: original.tasks.filter(node => node.task.id !== bound.id) };
    const record = publish(missing);
    expect(record.basis.dependencies.find(input => input.taskId === bound.id)?.taskDigest).toBeNull();
    expect(restoreResearch(record, research, original, finding).status).toBe('pending');
  });
});
