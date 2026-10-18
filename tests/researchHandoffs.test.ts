import { expect, it } from 'vitest';
import { pendingResearchHandoffs, researchHandoffs, resolveResearchHandoffs } from '../src/solver/researchHandoffs';
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
