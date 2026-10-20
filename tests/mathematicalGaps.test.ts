import { expect, it } from 'vitest';
import { deliveryDetails, type DeliveryRecord } from '../src/solver/deliveries';
import { bindMathematicalGap, mathematicalGapContext, mathematicalGaps, mathematicalGapVisible,
  MATHEMATICAL_GAP_CONTEXT_MAX_BYTES, MATHEMATICAL_GAP_ENTRY_MAX_BYTES, type MathematicalGap } from '../src/solver/mathematicalGaps';
import { markTaskReferences, taskVersion, type CooperativeTask, type TaskRecord } from '../src/solver/tasks';

const source: CooperativeTask = { id: 'core', kind: 'research', objective: 'Uniform nondegenerate counting',
  groupId: 'route', sharing: 'group', dependsOn: ['input'], revision: 0 };
const consumer: CooperativeTask = { id: 'original', kind: 'goal', objective: 'Prove original',
  theoremName: 'Original', proofPath: 'Submission.lean', dependsOn: ['core'], revision: 0, groupId: 'route' };
const input: CooperativeTask = { ...source, id: 'input', objective: 'Exact removal input', dependsOn: [], kind: 'lemma', type: 'True' };
const identity = { problemReceiptDigest: 'receipt', environmentDigest: 'env' };
const gap: MathematicalGap = { consumer: { taskId: consumer.id, taskDigest: taskVersion(consumer) },
  previousGap: 'Need c(k,ε) q^k configurations', reduced: 'Checked a count with S₀=0',
  remaining: 'c>0 independent of q, arbitrary k and nondegenerate configurations',
  evidenceScope: 'Only degenerate configurations established', reconsiderWhen: ['Prove uniform removal/counting with exact parameters'] };
const node = (task: CooperativeTask): TaskRecord => ({ task, status: 'pending', attempts: 0 });
function fixture() {
  const tasks = [source, consumer, input].map(node);
  const delivery: DeliveryRecord = { id: 'finding', producer: 'worker', taskId: source.id, taskDigest: taskVersion(source),
    kind: 'research', status: 'advisory', summary: 'Exact gap', statement: source.objective, premises: [],
    dependencies: [], remainingObligations: [consumer.id], evidenceRefs: [], createdAt: 1, mathematicalGap: gap,
    mathematicalGapScope: bindMathematicalGap(gap, source, { tasks }, identity) };
  return { tasks, deliveries: [delivery] };
}
it('retains quantified gaps across serialization, compaction and revisions without asserting equivalence', () => {
  const state = JSON.parse(JSON.stringify(fixture()));
  expect(mathematicalGaps(state, identity)[0].scopeStatus).toBe('current-contracts');
  state.tasks[0].task = { ...source, objective: 'Tensor reformulation', revision: 1 };
  state.deliveries[0].status = 'superseded';
  const history = mathematicalGaps(state, identity);
  expect(history[0].scopeStatus).toBe('historical-scope');
  expect(mathematicalGapContext(history).entries[0]).toMatchObject({ remaining: gap.remaining,
    read: { file: 'COOPERATION.json', collection: 'mathematicalGaps', deliveryId: 'finding' } });
  const updated = { ...gap, previousDeliveryId: 'finding', reduced: 'New exact bound' };
  expect(bindMathematicalGap(updated, state.tasks[0].task, state, identity).source.revision).toBe(1);
});
it('invalidates current scope when inputs or environment change and keeps retry evidence', () => {
  const state = fixture();
  state.tasks[2].task = { ...input, type: 'False', revision: 1 };
  expect(mathematicalGaps(state, identity)[0].scopeStatus).toBe('historical-scope');
  expect(mathematicalGaps(fixture(), { ...identity, environmentDigest: 'new' })[0].scopeStatus).toBe('historical-scope');
  expect(mathematicalGaps(fixture(), { ...identity, problemReceiptDigest: 'other' })).toEqual([]);
});

it('retains the exact transitive input contracts and marks deep changes as historical', () => {
  const state = fixture(), deep = { ...input, id: 'deep', objective: 'Deep uniformity input' };
  state.tasks[2].task = { ...input, dependsOn: [deep.id] };
  state.tasks.push(node(deep));
  state.deliveries[0].mathematicalGapScope = bindMathematicalGap(gap, source, state, identity);
  expect(state.deliveries[0].mathematicalGapScope.dependencies).toEqual([
    { taskId: input.id, taskDigest: taskVersion(state.tasks[2].task) },
    { taskId: deep.id, taskDigest: taskVersion(deep) },
  ]);
  expect(mathematicalGaps(state, identity)[0].scopeStatus).toBe('current-contracts');
  state.tasks[3].task = { ...deep, type: 'False', revision: 1 };
  const restored = JSON.parse(JSON.stringify(state));
  expect(mathematicalGaps(restored, identity)).toHaveLength(1);
  expect(mathematicalGaps(restored, identity)[0]).toMatchObject({ remaining: gap.remaining, scopeStatus: 'historical-scope' });
  expect(restored.deliveries[0].mathematicalGapScope.dependencies[1].taskDigest).toBe(taskVersion(deep));
});

it('visits repeated, self and cyclic dependencies once without including the source twice', () => {
  const state = fixture(), deep = { ...input, id: 'deep', dependsOn: [input.id, 'deep'] };
  const cyclicSource = { ...source, dependsOn: [input.id, input.id, deep.id, source.id] };
  state.tasks[0].task = cyclicSource;
  state.tasks[2].task = { ...input, dependsOn: [deep.id, deep.id, source.id] };
  state.tasks.push(node(deep));
  const scope = bindMathematicalGap(gap, cyclicSource, state, identity);
  expect(scope.dependencies).toEqual([
    { taskId: input.id, taskDigest: taskVersion(state.tasks[2].task) },
    { taskId: deep.id, taskDigest: taskVersion(deep) },
  ]);
});

it('captures the selected route inputs without adding the unselected alternative', () => {
  const state = fixture(), selected = node({ ...input, id: 'selected' }), unused = node({ ...input, id: 'unused' });
  state.tasks.push(selected, unused);
  state.tasks[2].status = 'running';
  state.tasks[2].assignment = { taskId: input.id, taskDigest: taskVersion(input), workerId: 'worker', seedCommit: 'seed', routeId: 'selected-route' };
  state.tasks[2].alternativeRoutes = [
    { id: 'unused-route', targetTaskId: input.id, prerequisiteTaskIds: [], closingTaskId: unused.task.id },
    { id: 'selected-route', targetTaskId: input.id, prerequisiteTaskIds: [], closingTaskId: selected.task.id },
  ];
  const scope = bindMathematicalGap(gap, source, state, identity);
  expect(scope.dependencies.map(dependency => dependency.taskId)).toEqual([input.id, selected.task.id]);
});

it('uses freshly checked task references when they narrow an intermediate input contract', () => {
  const state = fixture(), deep = node({ ...input, id: 'deep' }), unused = node({ ...input, id: 'unused' });
  state.tasks.push(deep, unused);
  const helper = state.tasks[2];
  helper.task = { ...helper.task, dependsOn: [unused.task.id] }; helper.status = 'integrated';
  helper.integratedCheck = { commit: 'checked', seedCommit: 'seed', sourceDigest: 'source', changes: [], passed: true,
    taskDigest: taskVersion(helper.task), verification: { schema: 'deepscientist.mathematics.verification-batch/v1',
      status: 'kernel_verified', targetCommit: 'checked', sessionId: 'test', events: [], startedAt: 1, checkedAt: 2, durationMs: 1, results: [] },
    references: { tasks: [{ taskId: deep.task.id, taskDigest: taskVersion(deep.task) }], inputs: [],
      contextDigest: 'context', sourceCommit: 'checked', environmentDigest: 'env',
      root: { name: 'Input', file: 'Submission.lean' }, statement: [], proof: [] } };
  markTaskReferences(helper.integratedCheck);
  expect(bindMathematicalGap(gap, source, state, identity).dependencies.map(dependency => dependency.taskId)).toEqual([input.id, deep.task.id]);
});

it('rejects a missing deep input rather than recording an incomplete current scope', () => {
  const state = fixture();
  state.tasks[2].task = { ...input, dependsOn: ['missing'] };
  expect(() => bindMathematicalGap(gap, source, state, identity)).toThrow('gap_dependency');
});

it('keeps private route history scoped and rejects private or stale consumer selectors', () => {
  const state = fixture(), other = { ...source, id: 'other', groupId: 'other' };
  expect(mathematicalGaps(state, identity, other)).toEqual([]);
  expect(() => bindMathematicalGap({ ...gap, consumer: { ...gap.consumer, taskDigest: 'f'.repeat(64) } }, source, state, identity))
    .toThrow('gap_consumer');
  expect(() => bindMathematicalGap({ ...gap, previousDeliveryId: 'missing' }, source, state, identity)).toThrow('gap_previous');
  state.tasks[1].task = { ...consumer, sharing: 'group', groupId: 'other' };
  expect(() => bindMathematicalGap({ ...gap, consumer: { taskId: consumer.id, taskDigest: taskVersion(state.tasks[1].task) } },
    source, state, identity)).toThrow('gap_consumer');
});
it('validates optional gap reports without changing legacy deliveries', () => {
  expect(deliveryDetails({ summary: 'ordinary' })).toEqual({ summary: 'ordinary', evidenceRefs: [] });
  expect(deliveryDetails({ mathematicalGap: gap }).mathematicalGap).toEqual(gap);
  expect(() => deliveryDetails({ mathematicalGap: { ...gap, remaining: '' } })).toThrow('math_delivery_invalid');
});

it('keeps a private consumer private even when its source is public or its current sharing changed', () => {
  const state = fixture(), delivery = state.deliveries[0], other = { ...source, id: 'other', groupId: 'other' };
  state.tasks[0].task = { ...source, sharing: 'problem' };
  state.tasks[1].task = { ...consumer, sharing: 'group' };
  delivery.mathematicalGap = { ...gap, consumer: { taskId: consumer.id, taskDigest: taskVersion(state.tasks[1].task) } };
  delivery.taskDigest = taskVersion(state.tasks[0].task);
  delivery.mathematicalGapScope = bindMathematicalGap(delivery.mathematicalGap, state.tasks[0].task, state, identity);
  expect(mathematicalGapVisible(delivery, state, other)).toBe(false);
  state.tasks[1].task = { ...consumer, sharing: 'problem' };
  expect(mathematicalGapVisible(delivery, state, other)).toBe(false);
  delivery.mathematicalGapScope = { ...delivery.mathematicalGapScope, consumer: state.tasks[1].task };
  expect(mathematicalGapVisible(delivery, state, other)).toBe(true);
  state.tasks[1].task = { ...consumer, sharing: 'group' };
  expect(mathematicalGapVisible(delivery, state, other)).toBe(false);
  delivery.mathematicalGapScope = { ...delivery.mathematicalGapScope, consumer: state.tasks[1].task };
  state.tasks[1].task = { ...consumer, sharing: 'problem' };
  expect(() => bindMathematicalGap({ ...gap, consumer: { taskId: consumer.id, taskDigest: taskVersion(state.tasks[1].task) },
    previousDeliveryId: delivery.id }, other, state, identity)).toThrow('gap_previous');
});

it('bounds escaped and Unicode text, evidence and dependency lists by encoded JSON bytes', () => {
  const records = Array.from({ length: 12 }, (_, index) => {
    const state = fixture(), delivery = state.deliveries[0];
    delivery.id = `finding-${index}`;
    delivery.createdAt = index;
    const route = { ...source, groupId: `route-${index}`, sharing: 'problem' as const };
    state.tasks[0].task = route;
    delivery.taskDigest = taskVersion(route);
    delivery.mathematicalGap = { ...gap, previousGap: '\u0000'.repeat(12000), reduced: '量😀'.repeat(3000),
      remaining: '\\"'.repeat(6000), evidenceScope: 'x'.repeat(12000), reconsiderWhen: Array(32).fill('量'.repeat(4000)) };
    delivery.evidenceRefs = Array(256).fill('x'.repeat(2000));
    delivery.mathematicalGapScope = { ...bindMathematicalGap(delivery.mathematicalGap, route, state, identity),
      dependencies: Array.from({ length: 100 }, (_, i) => ({ taskId: `dependency-${i}`, taskDigest: 'f'.repeat(64) })) };
    return mathematicalGaps(state, identity)[0];
  });
  const packet = mathematicalGapContext(records);
  expect(Buffer.byteLength(JSON.stringify(packet))).toBeLessThanOrEqual(MATHEMATICAL_GAP_CONTEXT_MAX_BYTES);
  expect(packet.complete).toBe(false);
  expect(packet.shown).toBeGreaterThan(0); expect(packet.omittedRoutes).toBe(12 - packet.shown);
  expect(packet.omittedForBudget).toBeGreaterThan(0);
  for (const entry of packet.entries) {
    expect(Buffer.byteLength(JSON.stringify(entry))).toBeLessThanOrEqual(MATHEMATICAL_GAP_ENTRY_MAX_BYTES);
    expect(entry).toMatchObject({ complete: false, omittedRetryConditions: 28, omittedEvidenceRefs: 252, omittedDependencies: 96,
      evidenceRefsDigest: expect.stringMatching(/^[a-f0-9]{64}$/u),
      read: { file: 'COOPERATION.json', collection: 'mathematicalGaps', deliveryId: entry.deliveryId } });
    expect(entry.remaining).toMatchObject({ complete: false, sha256: expect.stringMatching(/^[a-f0-9]{64}$/u) });
  }
});
