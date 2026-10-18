import { expect, it } from 'vitest';
import { pendingResearchHandoffs, researchHandoffs, resolveResearchHandoffs, selectResearchHandoffBatch } from '../src/solver/researchHandoffs';
import type { DeliveryRecord } from '../src/solver/deliveries';
import { taskVersion, type CooperativeTask, type TaskRecord } from '../src/solver/tasks';

const research: CooperativeTask = { id: 'investigate', kind: 'research', objective: 'Find the missing bridge', dependsOn: [], revision: 0 };
const proposal: CooperativeTask = { id: 'bridge', kind: 'lemma', objective: 'Prove the bridge', theoremName: 'Original.bridge',
  proofPath: 'Submission.lean', type: '∀ n : Nat, n = n', dependsOn: [], revision: 0 };
const node = (task: CooperativeTask): TaskRecord => ({ task, status: 'pending', attempts: 0 });
const delivery: DeliveryRecord = { id: 'delivery', producer: 'researcher', taskId: research.id, taskDigest: taskVersion(research),
  kind: 'research', status: 'advisory', summary: 'A bridge is worth proving.', statement: '', premises: [],
  dependencies: [], remainingObligations: [], evidenceRefs: [], createdAt: 1, commit: 'a'.repeat(40), lemmaRequests: [proposal] };
const fixture = () => ({ tasks: [{ ...node(research), status: 'completed' as const }], deliveries: [structuredClone(delivery)] });

it('reconstructs an unresolved exact proposal from its immutable delivery across restarts', () => {
  const state = fixture(), before = structuredClone(state);
  const handoff = pendingResearchHandoffs(state)[0];
  expect(handoff).toMatchObject({ proposal, status: 'pending', source: { commit: delivery.commit, notesPath: 'RESEARCH.md' } });
  expect(pendingResearchHandoffs(JSON.parse(JSON.stringify(state)))).toEqual([handoff]);
  expect(state).toEqual(before);
});

it('requires a decision only for proposals shown at dispatch, preserving later arrivals', () => {
  const state = fixture(), first = pendingResearchHandoffs(state)[0];
  state.deliveries.push({ ...delivery, id: 'arrived-later', lemmaRequests: [{ ...proposal, id: 'later', theoremName: 'Original.later' }] });
  expect(() => resolveResearchHandoffs(state, [first.id], [], undefined)).toThrow('math_handoff_unresolved:' + first.id);
  const decisions = resolveResearchHandoffs(state, [first.id], [], [{ id: first.id, status: 'deferred', reason: 'Need a finite-field estimate.' }]);
  expect(pendingResearchHandoffs({ ...state, researchDecisions: decisions })).toHaveLength(1);
  expect(pendingResearchHandoffs({ ...state, researchDecisions: decisions })[0].proposal.id).toBe('later');
});

it('records adoption as a pending typed task and reopens the handoff if that contract disappears', () => {
  const state = fixture(), id = pendingResearchHandoffs(state)[0].id;
  const adopted = { ...proposal, id: 'scheduled_bridge', objective: 'Exact bridge for the current goal' };
  const decisions = resolveResearchHandoffs(state, [id], [research, adopted], undefined);
  const planned = { ...state, tasks: [...state.tasks, node(adopted)], researchDecisions: decisions };
  expect(researchHandoffs(planned)[0]).toMatchObject({ status: 'adopted', decision: { taskId: adopted.id, taskDigest: taskVersion(adopted) } });
  expect(planned.tasks[1].status).toBe('pending');
  expect(pendingResearchHandoffs({ ...planned, tasks: state.tasks })).toHaveLength(1);
  expect(pendingResearchHandoffs({ ...planned, tasks: [...state.tasks, node({ ...adopted, type: 'False' })] })).toHaveLength(1);
});

it.each([
  { type: 'True' }, { theoremName: 'Original.unrelated' }, { proofPath: 'Other.lean' },
  { conditional: true }, { premises: ['extra assumption'] }, { groupId: 'other-route' },
])('does not confuse a changed proof target with adoption: %j', change => {
  const state = fixture(), id = pendingResearchHandoffs(state)[0].id;
  expect(() => resolveResearchHandoffs(state, [id], [{ ...proposal, ...change }], undefined)).toThrow('math_handoff_unresolved:');
});

it('retains the proposal prerequisite contract when recognizing adoption', () => {
  const state = fixture(); state.deliveries[0].lemmaRequests = [{ ...proposal, dependsOn: ['needed'] }];
  const id = pendingResearchHandoffs(state)[0].id;
  expect(() => resolveResearchHandoffs(state, [id], [proposal], undefined)).toThrow('math_handoff_unresolved:');
  expect(resolveResearchHandoffs(state, [id], [{ ...proposal, dependsOn: ['needed', 'extra'] }], undefined)[0].status).toBe('adopted');
});

it('preserves a proposed task id while an undispatched proposal in the same delivery still depends on it', () => {
  const state = fixture();
  state.deliveries[0].lemmaRequests = [proposal, { ...proposal, id: 'consumer', theoremName: 'Original.consumer', dependsOn: [proposal.id] }];
  const [base] = selectResearchHandoffBatch(state, { maxItems: 1 });
  const renamed = { ...proposal, id: 'renamed_bridge' };
  expect(() => resolveResearchHandoffs(state, [base.id], [renamed], undefined))
    .toThrow('math_handoff_dependency_id_required:' + proposal.id);
  expect(resolveResearchHandoffs(state, [base.id], [renamed, proposal], undefined)[0])
    .toMatchObject({ status: 'adopted', taskId: proposal.id });
});

it('allows renaming after the proposals depending on the original id have durable decisions', () => {
  const state = fixture();
  state.deliveries[0].lemmaRequests = [proposal, { ...proposal, id: 'consumer', theoremName: 'Original.consumer', dependsOn: [proposal.id] }];
  const [base, consumer] = pendingResearchHandoffs(state);
  const decisions = resolveResearchHandoffs(state, [consumer.id], [], [{
    id: consumer.id, status: 'rejected', reason: 'The consumer does not resolve an original obligation.',
  }]);
  expect(resolveResearchHandoffs({ ...state, researchDecisions: decisions }, [base.id], [{ ...proposal, id: 'renamed_bridge' }], undefined)[0])
    .toMatchObject({ status: 'adopted', taskId: 'renamed_bridge' });
});

it.each(['rejected', 'deferred'] as const)('persists a reasoned %s decision without declaring mathematical progress', status => {
  const state = fixture(), id = pendingResearchHandoffs(state)[0].id;
  const decisions = resolveResearchHandoffs(state, [id], [], [{ id, status, reason: 'The analytic premise is still unavailable.' }]);
  const restored = JSON.parse(JSON.stringify({ ...state, researchDecisions: decisions }));
  expect(pendingResearchHandoffs(restored)).toEqual([]);
  expect(researchHandoffs(restored)[0].decision?.reason).toContain('analytic premise');
  expect(restored.tasks).toEqual(state.tasks);
});

it.each([
  null, {}, [{ id: 'unknown', status: 'rejected', reason: 'Unknown proposal.' }],
  [{ status: 'rejected', reason: 'Missing id.' }],
])('rejects invalid decision data: %j', value => {
  const state = fixture(), id = pendingResearchHandoffs(state)[0].id;
  expect(() => resolveResearchHandoffs(state, [id], [], value)).toThrow('math_handoff_decision_invalid');
});

it('rejects empty reasons, duplicate decisions, and contradictory adoption', () => {
  const state = fixture(), id = pendingResearchHandoffs(state)[0].id;
  const decision = { id, status: 'rejected', reason: 'The type does not help the original bound.' };
  expect(() => resolveResearchHandoffs(state, [id], [], [{ ...decision, reason: ' ' }])).toThrow('math_handoff_decision_invalid');
  expect(() => resolveResearchHandoffs(state, [id], [], [decision, decision])).toThrow('math_handoff_decision_invalid');
  expect(() => resolveResearchHandoffs(state, [id], [proposal], [decision])).toThrow('math_handoff_decision_conflict:');
});

it('accepts acknowledged decisions idempotently while rejecting changed decisions', () => {
  const state = fixture(), id = pendingResearchHandoffs(state)[0].id;
  const response = { id, status: 'deferred', reason: 'Need a uniform cancellation estimate.' };
  const decisions = resolveResearchHandoffs(state, [id], [], [response]);
  const restored = { ...state, researchDecisions: decisions };
  expect(resolveResearchHandoffs(restored, [id], [], [response])).toEqual([]);
  expect(resolveResearchHandoffs(restored, [], [], [response])).toEqual([]);
  expect(() => resolveResearchHandoffs(restored, [id], [], [{ ...response, status: 'rejected' }])).toThrow('math_handoff_decision_invalid');
  expect(() => resolveResearchHandoffs(restored, [id], [], [{ ...response, reason: 'A changed decision.' }])).toThrow('math_handoff_decision_invalid');
});

it('excludes superseded, changed and missing-source proposals instead of reviving historical work', () => {
  const state = fixture();
  expect(pendingResearchHandoffs({ ...state, deliveries: [{ ...delivery, status: 'superseded' }] })).toEqual([]);
  expect(pendingResearchHandoffs({ ...state, deliveries: [{ ...delivery, taskDigest: 'old-version' }] })).toEqual([]);
  expect(pendingResearchHandoffs({ ...state, tasks: [] })).toEqual([]);
  expect(pendingResearchHandoffs({ ...state, deliveries: [{ ...delivery, dependencies: [{ taskId: 'gone', taskDigest: 'unknown' }] }] })).toEqual([]);
});

const proposals = (count: number): CooperativeTask[] => Array.from({ length: count }, (_, index) =>
  ({ ...proposal, id: `bridge_${index}`, theoremName: `Original.bridge_${index}` }));

it('bounds a thousand pending proposals while retaining undispatched work for subsequent batches', () => {
  const state = fixture(); state.deliveries[0].lemmaRequests = proposals(1000);
  const before = structuredClone(state), batch = selectResearchHandoffBatch(state);
  expect(batch).toHaveLength(8);
  expect(Buffer.byteLength(JSON.stringify(batch))).toBeLessThanOrEqual(32 * 1024);
  expect(batch.map(item => item.proposal.id)).toEqual(proposals(8).map(task => task.id));
  expect(state).toEqual(before);
  const decisions = resolveResearchHandoffs(state, batch.map(item => item.id), [],
    batch.map(item => ({ id: item.id, status: 'deferred', reason: 'Await a sharper estimate.' })));
  const remaining = { ...state, researchDecisions: decisions };
  expect(pendingResearchHandoffs(remaining)).toHaveLength(992);
  expect(selectResearchHandoffBatch(remaining).map(item => item.proposal.id))
    .toEqual(proposals(16).slice(8).map(task => task.id));
  expect(selectResearchHandoffBatch(JSON.parse(JSON.stringify(remaining)))).toEqual(selectResearchHandoffBatch(remaining));
});

it('places pending prerequisites first without binding a long dependency chain into one batch', () => {
  const state = fixture(), chain = proposals(1000).map((task, index) =>
    ({ ...task, dependsOn: index ? [`bridge_${index - 1}`] : [] }));
  state.deliveries[0].lemmaRequests = [...chain].reverse();
  expect(selectResearchHandoffBatch(state).map(item => item.proposal.id)).toEqual(chain.slice(0, 8).map(task => task.id));
  expect(pendingResearchHandoffs(state)).toHaveLength(1000);
});

it('keeps deliveries FIFO while moving a later prerequisite before its earlier consumer', () => {
  const state = fixture(), [base, consumer, later] = proposals(3);
  state.deliveries[0].lemmaRequests = [{ ...consumer, dependsOn: [base.id] }, base];
  state.deliveries.push({ ...delivery, id: 'later-delivery', createdAt: 2, lemmaRequests: [later] });
  const batch = selectResearchHandoffBatch(state, { maxItems: 2 });
  expect(batch.map(item => item.proposal.id)).toEqual([base.id, consumer.id]);
  expect(selectResearchHandoffBatch(state, { maxItems: 1 })[0].proposal.id).toBe(base.id);
  const decisions = resolveResearchHandoffs(state, batch.map(item => item.id), [],
    batch.map(item => ({ id: item.id, status: 'rejected', reason: 'The bridge has the wrong hypotheses.' })));
  expect(selectResearchHandoffBatch({ ...state, researchDecisions: decisions }).map(item => item.proposal.id)).toEqual([later.id]);
});

it('does not add a late delivery to an already selected batch', () => {
  const state = fixture(), batch = selectResearchHandoffBatch(state);
  const later = { ...proposal, id: 'later', theoremName: 'Original.later' };
  state.deliveries.push({ ...delivery, id: 'later-delivery', createdAt: 2, lemmaRequests: [later] });
  const decisions = resolveResearchHandoffs(state, batch.map(item => item.id), [],
    batch.map(item => ({ id: item.id, status: 'deferred', reason: 'Await a uniform bound.' })));
  expect(batch).toHaveLength(1);
  expect(batch[0].proposal.id).toBe(proposal.id);
  expect(selectResearchHandoffBatch({ ...state, researchDecisions: decisions }).map(item => item.proposal.id)).toEqual(['later']);
});

it('measures the complete JSON array in UTF-8 bytes, including commas and brackets', () => {
  const state = fixture();
  state.deliveries[0].lemmaRequests = proposals(3).map(task => ({ ...task, objective: '研究一致估计'.repeat(20) }));
  const pending = pendingResearchHandoffs(state), two = JSON.stringify(pending.slice(0, 2));
  const bytes = Buffer.byteLength(two);
  expect(bytes).toBeGreaterThan(two.length);
  expect(selectResearchHandoffBatch(state, { maxBytes: bytes })).toEqual(pending.slice(0, 2));
  expect(selectResearchHandoffBatch(state, { maxBytes: bytes - 1 })).toEqual(pending.slice(0, 1));
  expect(selectResearchHandoffBatch(state, { maxItems: 1, maxBytes: bytes * 10 })).toEqual(pending.slice(0, 1));
});

it('dispatches an oversized first proposal intact instead of skipping it or truncating its exact type', () => {
  const state = fixture(), [first, second] = proposals(2);
  const type = '(' + 'True ∧ '.repeat(10_000) + 'True)';
  state.deliveries[0].lemmaRequests = [{ ...first, type }, second];
  const pending = pendingResearchHandoffs(state), selected = selectResearchHandoffBatch(state);
  expect(Buffer.byteLength(JSON.stringify(selected))).toBeGreaterThan(32 * 1024);
  expect(selected).toEqual([pending[0]]);
  expect(selected[0].proposal.type).toBe(type);
  expect(selectResearchHandoffBatch(JSON.parse(JSON.stringify(state)))).toEqual(selected);
});

it.each([{ maxItems: 0 }, { maxItems: 1.5 }, { maxBytes: -1 }, { maxBytes: Infinity }])
  ('rejects invalid batch limits: %j', options => {
    expect(() => selectResearchHandoffBatch(fixture(), options)).toThrow('math_handoff_invalid_batch_limit:');
  });
