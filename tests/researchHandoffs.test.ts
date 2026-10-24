import { expect, it } from 'vitest';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';
import { pendingResearchHandoffs, retainedResearchHandoffs, researchHandoffs, researchHandoffContext,
  normalizedResearchHandoffDecisions, resolveResearchHandoffs, scopeResearchHandoffDecisions, selectResearchHandoffBatch,
  type ResearchHandoffDecision } from '../src/solver/researchHandoffs';
import type { TaskProof } from '../src/solver/cooperativeProof';
import type { DeliveryRecord } from '../src/solver/deliveries';
import { markTaskAcceptance, taskVersion, type CooperativeTask, type TaskRecord } from '../src/solver/tasks';

const research: CooperativeTask = { id: 'investigate', kind: 'research', objective: 'Find the missing bridge', dependsOn: [], revision: 0 };
const proposal: CooperativeTask = { id: 'bridge', kind: 'lemma', objective: 'Prove the bridge', theoremName: 'Original.bridge',
  proofPath: 'Submission.lean', type: '∀ n : Nat, n = n', dependsOn: [], revision: 0 };
const node = (task: CooperativeTask): TaskRecord => ({ task, status: 'pending', attempts: 0 });
const delivery: DeliveryRecord = { id: 'delivery', producer: 'researcher', taskId: research.id, taskDigest: taskVersion(research),
  kind: 'research', status: 'advisory', summary: 'A bridge is worth proving.', statement: '', premises: [],
  dependencies: [], remainingObligations: [], evidenceRefs: [], createdAt: 1, commit: 'a'.repeat(40), lemmaRequests: [proposal] };
type TestState = { tasks: TaskRecord[]; deliveries: DeliveryRecord[]; researchDecisions?: ResearchHandoffDecision[];
  history?: { task: CooperativeTask }[] };
const fixture = (): TestState => ({ tasks: [{ ...node(research), status: 'completed' }], deliveries: [structuredClone(delivery)] });

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

it('accepts explicit full-plan adoption only through the same exact typed task as inferred adoption', () => {
  const state = fixture(), handoff = pendingResearchHandoffs(state)[0], before = structuredClone(state);
  const adopted = { ...proposal, revision: 1, ownerId: 'prover', sharing: 'problem' as const };
  const tasks = [research, adopted], response = [{ id: handoff.id, status: 'adopted' }];
  const decisions = resolveResearchHandoffs(state, [handoff.id], tasks, response,
    { [handoff.id]: handoff.activationDigest });

  expect(decisions).toEqual(resolveResearchHandoffs(state, [handoff.id], tasks, undefined));
  expect(decisions).toMatchObject([{ status: 'adopted', taskId: adopted.id, taskDigest: taskVersion(adopted) }]);
  const restored = JSON.parse(JSON.stringify({ ...state, tasks: [...state.tasks, node(adopted)], researchDecisions: decisions }));
  expect(resolveResearchHandoffs(restored, [], tasks, response)).toEqual([]);
  expect(state).toEqual(before);
});

it.each([undefined, { type: 'False' }, { theoremName: 'Original.other' }, { groupId: 'other-route' },
  { proofPath: 'Other.lean' }, { conditional: true }, { premises: ['new premise'] }])
('does not let an explicit adopted declaration replace its missing or changed typed target: %j', change => {
  const state = fixture(), handoff = pendingResearchHandoffs(state)[0];
  const tasks = change ? [research, { ...proposal, ...change }] : [research];
  expect(() => resolveResearchHandoffs(state, [handoff.id], tasks, [{ id: handoff.id, status: 'adopted' }]))
    .toThrow('math_handoff_unresolved:' + handoff.id);
  expect(state.researchDecisions).toBeUndefined();
});

it('keeps dispatch and source activation checks for explicit full-plan adoption', () => {
  const state = fixture(), handoff = pendingResearchHandoffs(state)[0], tasks = [research, proposal];
  const response = [{ id: handoff.id, status: 'adopted' }];
  expect(() => resolveResearchHandoffs(state, [], tasks, response)).toThrow('math_handoff_decision_invalid');
  expect(() => resolveResearchHandoffs(state, [handoff.id], tasks, response, { [handoff.id]: 'old-activation' }))
    .toThrow('math_handoff_dispatch_superseded:' + handoff.id);
  expect(() => resolveResearchHandoffs({ ...state, deliveries: [{ ...delivery, status: 'superseded' }] },
    [handoff.id], tasks, response)).toThrow('math_handoff_decision_invalid');
});

it.each([{ ownerId: 'different-writer' }, { type: 'False' }, { waitsOn: ['invented'] }])
('rejects task or waiting fields supplied inside a full-plan adoption declaration: %j', extra => {
  const state = fixture(), handoff = pendingResearchHandoffs(state)[0];
  expect(() => resolveResearchHandoffs(state, [handoff.id], [research, proposal],
    [{ id: handoff.id, status: 'adopted', ...extra }])).toThrow('math_handoff_decision_invalid');
});

it.each([false, true])('rejects conflicting adoption and rejection across delivery aliases (adoption first: %s)', first => {
  const state = fixture(); state.deliveries.push({ ...structuredClone(delivery), id: 'duplicate' });
  const handoff = pendingResearchHandoffs(state)[0];
  const responses = [{ id: handoff.sources[0].handoffId, status: 'adopted' },
    { id: handoff.sources[1].handoffId, status: 'rejected', reason: 'This proposal cannot close the goal.' }];
  if (!first) responses.reverse();
  expect(() => resolveResearchHandoffs(state, [handoff.id], [research, proposal], responses))
    .toThrow('math_handoff_decision_conflict:' + handoff.id);
});

it('keeps adoption durable when only scheduling metadata changes', () => {
  const state = fixture();
  state.deliveries.push({ ...structuredClone(delivery), id: 'repeated', createdAt: 2 });
  const id = pendingResearchHandoffs(state)[0].id;
  const oldVersion = { ...proposal, id: 'scheduled_bridge' };
  const adopted = { ...oldVersion, sharing: 'group' as const };
  const decisions = resolveResearchHandoffs(state, [id], [research, adopted], undefined);
  state.researchDecisions = decisions.map((decision, index) => index === 0 ?
    { ...decision, taskDigest: taskVersion(oldVersion) } : decision);
  const current = { ...adopted, sharing: 'problem' as const };
  state.tasks.push(node(current));

  expect(taskVersion(current)).not.toBe(taskVersion(adopted));
  expect(taskVersion(current)).not.toBe(taskVersion(oldVersion));
  expect(researchHandoffs(state)).toMatchObject([{ status: 'adopted', decision: {
    taskId: current.id, taskDigest: taskVersion(current),
  } }]);
  expect(pendingResearchHandoffs(state)).toEqual([]);
});

it.each([undefined, 'group'] as const)('keeps adoption after unpinned prerequisites change sharing from %s across a restart', sharing => {
  const state = fixture(), inputs = ['left', 'right'].map(id => ({ ...proposal, id,
    theoremName: `Original.${id}`, ...(sharing ? { sharing } : {}) }));
  const requested = { ...proposal, dependsOn: inputs.map(task => task.id) };
  state.tasks.push(...inputs.map(node)); state.deliveries[0].lemmaRequests = [requested];
  const handoff = pendingResearchHandoffs(state)[0];
  state.researchDecisions = resolveResearchHandoffs(state, [handoff.id], [research, ...inputs, requested], undefined);
  state.tasks.push(node(requested));
  for (const input of state.tasks.filter(item => inputs.some(task => task.id === item.task.id)))
    input.task = { ...input.task, sharing: 'problem' };

  expect(researchHandoffs(JSON.parse(JSON.stringify(state)))).toMatchObject([{ status: 'adopted',
    decision: { taskId: requested.id } }]);
  expect(pendingResearchHandoffs(state)).toEqual([]);
});

it('migrates legacy adoption bindings through recorded prerequisite sharing edits without mutating the archive', () => {
  const state = fixture(), inputs = ['left', 'right'].map(id => ({ ...proposal, id,
    theoremName: `Original.${id}`, sharing: 'group' as const }));
  const requested = { ...proposal, dependsOn: inputs.map(task => task.id) };
  state.tasks.push(...inputs.map(node)); state.deliveries[0].lemmaRequests = [requested];
  const handoff = pendingResearchHandoffs(state)[0];
  state.researchDecisions = resolveResearchHandoffs(state, [handoff.id], [research, ...inputs, requested], undefined)
    .map(decision => ({ ...decision, contextDigest: handoff.contextDigest }));
  state.tasks.push(node(requested));
  expect(researchHandoffs(state)[0].status).toBe('adopted');
  state.history = inputs.map(task => ({ task }));
  for (const input of state.tasks.filter(item => inputs.some(task => task.id === item.task.id)))
    input.task = { ...input.task, sharing: 'problem' };
  const before = structuredClone(state);

  expect(researchHandoffs(state)[0].status).toBe('adopted');
  const decisions = normalizedResearchHandoffDecisions(state);
  expect(decisions[0].contextDigest).not.toBe(handoff.contextDigest);
  const restored = JSON.parse(JSON.stringify({ ...state, researchDecisions: decisions, history: [] }));
  expect(researchHandoffs(restored)[0].status).toBe('adopted');
  const scope = { tasks: state.tasks, deliveries: state.deliveries };
  expect(researchHandoffs({ ...scope, researchDecisions: scopeResearchHandoffDecisions(state, scope) })[0].status).toBe('adopted');
  expect(state).toEqual(before);
  expect(researchHandoffs({ ...state, history: [] })[0].status).toBe('pending');
});

it.each([{ type: 'False' }, { theoremName: 'Original.changed' }, { conditional: true }, { premises: ['new assumption'] }])
('does not migrate legacy adoption across a changed prerequisite contract: %j', change => {
  const state = fixture(), input = { ...proposal, id: 'input', theoremName: 'Original.input', sharing: 'group' as const };
  const requested = { ...proposal, dependsOn: [input.id] };
  state.tasks.push(node(input)); state.deliveries[0].lemmaRequests = [requested];
  const handoff = pendingResearchHandoffs(state)[0];
  state.researchDecisions = resolveResearchHandoffs(state, [handoff.id], [research, input, requested], undefined)
    .map(decision => ({ ...decision, contextDigest: handoff.contextDigest }));
  state.tasks.push(node(requested)); state.history = [{ task: input }];
  state.tasks[1].task = { ...input, sharing: 'problem', ...change };

  expect(researchHandoffs(state)[0].status).toBe('pending');
  expect(normalizedResearchHandoffDecisions(state)).toEqual(state.researchDecisions);
});

it.each(['rejected', 'deferred'] as const)('reopens a %s decision when a versioned prerequisite changes sharing', status => {
  const state = fixture(), input = { ...proposal, id: 'input', theoremName: 'Original.input', sharing: 'group' as const };
  const requested = { ...proposal, dependsOn: [input.id] };
  state.tasks.push(node(input)); state.deliveries[0].lemmaRequests = [requested];
  const handoff = pendingResearchHandoffs(state)[0];
  state.researchDecisions = resolveResearchHandoffs(state, [handoff.id], [research, input], [{ id: handoff.id, status,
    reason: 'Decided for the current prerequisite version.', ...(status === 'deferred' ? { waitsOn: [input.id] } : {}) }]);
  state.history = [{ task: input }]; state.tasks[1].task = { ...input, sharing: 'problem' };

  expect(researchHandoffs(state)[0].status).toBe('pending');
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

it('coalesces exact repeated proposals without changing the original id or activation and retains immutable sources', () => {
  const state = fixture(), first = pendingResearchHandoffs(state)[0];
  state.deliveries.push({ ...structuredClone(delivery), id: 'repeated', producer: 'other-researcher', commit: 'b'.repeat(40), createdAt: 2 });
  const before = structuredClone(state), handoffs = pendingResearchHandoffs(state);
  expect(handoffs).toHaveLength(1);
  expect(handoffs[0]).toMatchObject({ id: first.id, activationDigest: first.activationDigest, proposal,
    sources: [{ handoffId: first.id, deliveryId: delivery.id, producer: delivery.producer, source: first.source },
      { deliveryId: 'repeated', producer: 'other-researcher', source: { commit: 'b'.repeat(40), notesPath: 'RESEARCH.md' } }] });
  expect(first.id).toBe(mathDigest(canonicalMathJson({ deliveryId: delivery.id, proposalDigest: taskVersion(proposal) })));
  expect(pendingResearchHandoffs(JSON.parse(JSON.stringify(state)))).toEqual(handoffs);
  expect(state).toEqual(before);
});

it('decides a late duplicate once and keeps every old delivery key durable if the first delivery is superseded', () => {
  const state = fixture(), dispatched = pendingResearchHandoffs(state)[0];
  state.deliveries.push({ ...structuredClone(delivery), id: 'repeated', createdAt: 2 });
  const responses = [{ id: dispatched.id, status: 'rejected', reason: 'This exact interface misses the required bound.' }];
  const decisions = resolveResearchHandoffs(state, [dispatched.id], [research], responses,
    { [dispatched.id]: dispatched.activationDigest });
  expect(decisions).toHaveLength(2);
  expect(decisions.map(item => item.deliveryId)).toEqual([delivery.id, 'repeated']);
  expect(new Set(decisions.map(item => item.contextDigest)).size).toBe(1);
  state.researchDecisions = decisions;
  expect(pendingResearchHandoffs(state)).toEqual([]);
  const sources = researchHandoffs(state)[0].sources;
  expect(resolveResearchHandoffs(state, [], [research], [{ ...responses[0], id: sources[1].handoffId }])).toEqual([]);
  state.deliveries[0].status = 'superseded';
  expect(researchHandoffs(state)).toMatchObject([{ deliveryId: 'repeated', status: 'rejected' }]);
  expect(pendingResearchHandoffs(JSON.parse(JSON.stringify(state)))).toEqual([]);
});

it.each(['adopted', 'rejected', 'deferred'] as const)('reads a legacy %s decision recorded under a non-primary delivery id', status => {
  const state = fixture(), repeated = { ...structuredClone(delivery), id: 'repeated', createdAt: 2 };
  const alias = pendingResearchHandoffs({ ...state, deliveries: [repeated] })[0].id;
  state.deliveries.push(repeated);
  if (status === 'adopted') state.tasks.push(node(proposal));
  state.researchDecisions = [{ id: alias, deliveryId: repeated.id, status,
    ...(status === 'adopted' ? { taskId: proposal.id, taskDigest: taskVersion(proposal) } : { reason: 'The current bound is unavailable.' }) }];
  const handoffs = researchHandoffs(state);
  expect(handoffs).toHaveLength(1);
  expect(handoffs[0]).toMatchObject({ deliveryId: delivery.id, status, decision: { id: handoffs[0].id, status } });
  expect(pendingResearchHandoffs(JSON.parse(JSON.stringify(state)))).toEqual([]);
});

it('resolves an in-flight legacy alias after another duplicate becomes its primary source', () => {
  const state = fixture(), original = pendingResearchHandoffs(state)[0];
  state.deliveries.unshift({ ...structuredClone(delivery), id: 'earlier', createdAt: 0 });
  const current = pendingResearchHandoffs(state)[0];
  expect(current.id).not.toBe(original.id);
  expect(current.activationDigest).toBe(original.activationDigest);
  const decisions = resolveResearchHandoffs(state, [original.id], [research], [
    { id: original.id, status: 'deferred', reason: 'Need a separate estimate.' },
  ], { [original.id]: original.activationDigest });
  expect(decisions.map(item => item.deliveryId)).toEqual(['earlier', delivery.id]);
  expect(pendingResearchHandoffs({ ...state, researchDecisions: decisions })).toEqual([]);
});

it('accepts consistent decisions for old duplicate ids and rejects conflicting duplicate decisions atomically', () => {
  const state = fixture(); state.deliveries.push({ ...structuredClone(delivery), id: 'repeated', createdAt: 2 });
  const sources = pendingResearchHandoffs(state)[0].sources, ids = sources.map(source => source.handoffId);
  const responses = ids.map(id => ({ id, status: 'rejected', reason: 'The typed target has insufficient hypotheses.' }));
  expect(resolveResearchHandoffs(state, ids, [research], responses)).toHaveLength(2);
  const before = structuredClone(state);
  expect(() => resolveResearchHandoffs(state, ids, [research], [responses[0], { ...responses[1], status: 'deferred' }]))
    .toThrow('math_handoff_decision_conflict:');
  expect(state).toEqual(before);
});

it('reopens conflicting historical dispositions rather than silently choosing one duplicate decision', () => {
  const state = fixture(); state.deliveries.push({ ...structuredClone(delivery), id: 'repeated', createdAt: 2 });
  const handoff = pendingResearchHandoffs(state)[0];
  state.researchDecisions = handoff.sources.map((source, index) => ({ id: source.handoffId, deliveryId: source.deliveryId,
    status: index ? 'deferred' : 'rejected', reason: 'Different historical dispositions.' }));
  expect(pendingResearchHandoffs(state)).toHaveLength(1);
  const current = pendingResearchHandoffs(state)[0];
  const decisions = resolveResearchHandoffs(state, [current.id], [research], [
    { id: current.id, status: 'rejected', reason: 'Reconciled against the exact current target.' },
  ], { [current.id]: current.activationDigest });
  expect(pendingResearchHandoffs({ ...state, researchDecisions: decisions })).toEqual([]);
});

it('keeps globally conflicting dispositions pending when a peer can see only one decided duplicate', () => {
  const state = fixture(), repeated = { ...structuredClone(delivery), id: 'public-duplicate' };
  state.deliveries.push(repeated);
  const handoff = researchHandoffs(state)[0];
  state.researchDecisions = handoff.sources.map((source, index) => ({ id: source.handoffId, deliveryId: source.deliveryId,
    status: index ? 'deferred' : 'rejected', reason: 'Historical dispositions conflict.', contextDigest: handoff.contextDigest }));
  const scope = { tasks: state.tasks, deliveries: [repeated] };
  expect(researchHandoffs({ ...scope, researchDecisions: [state.researchDecisions[1]] })[0].status).toBe('deferred');
  const decisions = scopeResearchHandoffDecisions(state, scope);
  expect(decisions).toEqual([]);
  expect(researchHandoffs({ ...scope, researchDecisions: decisions })[0].status).toBe('pending');
});

it('projects a complete visible waiting contract and never wakes a private contract from only its visible subset', () => {
  const { state, needed, other, defer } = waitingFixture();
  defer(['needed', 'other']);
  const repeated = { ...structuredClone(delivery), id: 'public-duplicate' };
  state.deliveries.push(repeated); accept(needed);
  const scope = { tasks: state.tasks.filter(item => item !== other), deliveries: [repeated] };
  const before = structuredClone(state), decisions = scopeResearchHandoffDecisions(state, scope);
  expect(decisions).toMatchObject([{ status: 'deferred', deliveryId: repeated.id }]);
  expect(decisions[0]).not.toHaveProperty('waitsOn');
  expect(decisions[0]).not.toHaveProperty('reason');
  expect(JSON.stringify(decisions)).not.toContain(other.task.id);
  expect(researchHandoffs({ ...scope, researchDecisions: decisions })[0].status).toBe('deferred');
  const visibleScope = { ...scope, tasks: state.tasks };
  expect(scopeResearchHandoffDecisions(state, visibleScope)[0].waitsOn).toEqual(state.researchDecisions![0].waitsOn);
  expect(state).toEqual(before);

  accept(other);
  expect(researchHandoffs(state)[0].status).toBe('pending');
  const reopened = scopeResearchHandoffDecisions(state, scope);
  expect(reopened).toEqual([]);
  expect(researchHandoffs({ ...scope, researchDecisions: reopened })[0].status).toBe('pending');
});

it('does not disclose an adopted task absent from the scoped graph', () => {
  const state = fixture(), handoff = researchHandoffs(state)[0];
  state.researchDecisions = resolveResearchHandoffs(state, [handoff.id], [research, proposal], undefined);
  state.tasks.push(node(proposal));
  const repeated = { ...structuredClone(delivery), id: 'public-duplicate' };
  state.deliveries.push(repeated);
  const scope = { tasks: state.tasks.filter(item => item.task.id !== proposal.id), deliveries: [repeated] };
  const decisions = scopeResearchHandoffDecisions(state, scope);
  expect(decisions).toEqual([]);
  expect(researchHandoffs({ ...scope, researchDecisions: decisions })[0].status).toBe('pending');
});

it('does not project adoption onto a sibling fallback with a different current input context', () => {
  const state = fixture(), input = node({ ...proposal, id: 'input', theoremName: 'Original.input' });
  const requested = { ...proposal, dependsOn: [input.task.id] };
  state.tasks.push(input); state.deliveries[0].lemmaRequests = [requested, input.task];
  const handoff = researchHandoffs(state).find(item => item.proposal.id === requested.id)!;
  state.researchDecisions = resolveResearchHandoffs(state, [handoff.id], [research, input.task, requested], undefined);
  state.tasks.push(node(requested)); input.task = { ...input.task, type: 'False' };
  const scope = { tasks: state.tasks.filter(item => item !== input), deliveries: state.deliveries };
  expect(researchHandoffs({ ...scope, researchDecisions: state.researchDecisions })[0].status).toBe('adopted');
  const decisions = scopeResearchHandoffDecisions(state, scope);
  expect(researchHandoffs({ ...scope, researchDecisions: decisions })[0].status).toBe('pending');
});

it.each([{ type: 'True' }, { theoremName: 'Original.other' }, { premises: ['an extra premise'] },
  { objective: 'A distinct exact request' }, { revision: 1 }, { dependsOn: ['different-input'] }])
('keeps distinct exact proposal contracts separate: %j', change => {
  const state = fixture();
  state.deliveries.push({ ...structuredClone(delivery), id: 'different', lemmaRequests: [{ ...proposal, ...change }] });
  expect(pendingResearchHandoffs(state)).toHaveLength(2);
});

it('keeps source tasks and versioned delivery inputs separate while normalizing input order and duplicates', () => {
  const state = fixture(), left = { ...proposal, id: 'left' }, right = { ...proposal, id: 'right' };
  state.tasks.push(node(left), node(right));
  const inputs = [left, right].map(task => ({ taskId: task.id, taskDigest: taskVersion(task) }));
  state.deliveries[0].dependencies = inputs;
  state.deliveries.push({ ...structuredClone(delivery), id: 'same-inputs', dependencies: [inputs[1], inputs[0], inputs[1]] });
  expect(pendingResearchHandoffs(state)).toHaveLength(1);
  state.deliveries.push({ ...structuredClone(delivery), id: 'other-inputs', dependencies: [inputs[0]] });
  expect(pendingResearchHandoffs(state)).toHaveLength(2);
  const otherSource = { ...research, id: 'other-source' };
  state.tasks.push(node(otherSource));
  state.deliveries.push({ ...structuredClone(delivery), id: 'other-source', taskId: otherSource.id,
    taskDigest: taskVersion(otherSource), dependencies: inputs });
  expect(pendingResearchHandoffs(state)).toHaveLength(3);
});

it('does not reuse a decision when a new delivery refers to a different source task version', () => {
  const state = fixture(), original = pendingResearchHandoffs(state)[0];
  state.researchDecisions = resolveResearchHandoffs(state, [original.id], [research], [
    { id: original.id, status: 'rejected', reason: 'The original research contract does not close the gap.' },
  ]);
  state.tasks[0].task = { ...research, revision: 1 };
  state.deliveries.push({ ...structuredClone(delivery), id: 'new-source-version', taskDigest: taskVersion(state.tasks[0].task) });
  expect(pendingResearchHandoffs(state)).toMatchObject([{ deliveryId: 'new-source-version', status: 'pending' }]);
  expect(pendingResearchHandoffs(state)[0].contextDigest).not.toBe(original.contextDigest);
});

it.each(['source', 'delivery-input'] as const)('does not replay a bound decision if restored %s contracts changed under an old delivery id', change => {
  const state = fixture(), input = node({ ...proposal, id: 'input', theoremName: 'Original.input' });
  state.tasks.push(input);
  state.deliveries[0].dependencies = [{ taskId: input.task.id, taskDigest: taskVersion(input.task) }];
  const original = pendingResearchHandoffs(state)[0];
  state.researchDecisions = resolveResearchHandoffs(state, [original.id], state.tasks.map(node => node.task), [
    { id: original.id, status: 'rejected', reason: 'Only valid for the pinned input contracts.' },
  ]);
  expect(state.researchDecisions[0].contextDigest).toBe(original.contextDigest);
  if (change === 'source') {
    state.tasks[0].task = { ...research, revision: 1 };
    state.deliveries[0].taskDigest = taskVersion(state.tasks[0].task);
  } else {
    input.task = { ...input.task, type: 'True', revision: 1 };
    state.deliveries[0].dependencies = [{ taskId: input.task.id, taskDigest: taskVersion(input.task) }];
  }
  expect(pendingResearchHandoffs(state)).toHaveLength(1);
  expect(pendingResearchHandoffs(state)[0].contextDigest).not.toBe(original.contextDigest);
});

it.each(['adopted', 'rejected', 'deferred'] as const)('does not carry a %s decision to a new version of an unpinned proposal input', status => {
  const state = fixture(), input = node({ ...proposal, id: 'input', theoremName: 'Original.input' });
  state.tasks.push(input);
  const requested = { ...proposal, dependsOn: [input.task.id] };
  state.deliveries[0].lemmaRequests = [requested];
  const original = pendingResearchHandoffs(state)[0], planned = state.tasks.map(node => node.task);
  if (status === 'adopted') planned.push(requested);
  state.researchDecisions = resolveResearchHandoffs(state, [original.id], planned, status === 'adopted' ? undefined : [
    { id: original.id, status, reason: 'Decided for the exact current premise.' },
  ]);
  if (status === 'adopted') state.tasks.push(node(requested));
  expect(pendingResearchHandoffs(state)).toEqual([]);
  input.task = { ...input.task, type: 'False', revision: 1 };
  const reopened = pendingResearchHandoffs(state)[0];
  expect(reopened.id).toBe(original.id);
  expect(reopened.contextDigest).not.toBe(original.contextDigest);
  expect(reopened.activationDigest).not.toBe(original.activationDigest);
  expect(() => resolveResearchHandoffs(state, [original.id], state.tasks.map(node => node.task), [],
    { [original.id]: original.activationDigest })).toThrow('math_handoff_dispatch_superseded:');
});

it('does not merge a consumer whose sibling input has a different exact contract', () => {
  const state = fixture(), input = { ...proposal, id: 'input', theoremName: 'Original.input' };
  const consumer = { ...proposal, dependsOn: [input.id] };
  state.deliveries[0].lemmaRequests = [consumer, input];
  state.deliveries.push({ ...structuredClone(delivery), id: 'changed-sibling', lemmaRequests: [consumer, { ...input, type: 'True' }] });
  expect(pendingResearchHandoffs(state).filter(item => item.proposal.id === consumer.id)).toHaveLength(2);
});

it('binds adopted decisions to the resulting plan when it edits a proposed prerequisite in the same response', () => {
  const state = fixture(), input = { ...proposal, id: 'input', theoremName: 'Original.input' };
  const consumer = { ...proposal, dependsOn: [input.id] };
  state.deliveries[0].lemmaRequests = [consumer, input];
  const batch = selectResearchHandoffBatch(state), planned = [research, { ...input, objective: 'The chosen premise', revision: 1 }, consumer];
  state.researchDecisions = resolveResearchHandoffs(state, batch.map(item => item.id), planned, undefined);
  state.tasks = planned.map(node);
  expect(researchHandoffs(state).map(item => item.status)).toEqual(['adopted', 'adopted']);
  expect(pendingResearchHandoffs(state)).toEqual([]);
});

it('keeps merged prerequisite order and its original task id while a consumer in any source delivery remains undecided', () => {
  const state = fixture(), consumer = { ...proposal, id: 'consumer', theoremName: 'Original.consumer', dependsOn: [proposal.id] };
  state.deliveries.push({ ...structuredClone(delivery), id: 'consumer-delivery', lemmaRequests: [consumer, proposal] });
  const batch = selectResearchHandoffBatch(state);
  expect(batch.map(item => item.proposal.id)).toEqual([proposal.id, consumer.id]);
  expect(batch[0].sources).toHaveLength(2);
  expect(() => resolveResearchHandoffs(state, [batch[0].id], [{ ...proposal, id: 'renamed' }], undefined))
    .toThrow('math_handoff_dependency_id_required:' + proposal.id);
});

it('keeps a thousand duplicate provenance records out of the prompt and batch allowance without truncating the typed proposal', () => {
  const state = fixture(), later = { ...proposal, id: 'later', theoremName: 'Original.later' };
  state.deliveries[0].lemmaRequests = [proposal, later];
  const single = researchHandoffContext(pendingResearchHandoffs(state)[0]);
  state.deliveries.push(...Array.from({ length: 999 }, (_, index) => ({ ...structuredClone(delivery), id: `repeat-${index}`, createdAt: index + 2 })));
  const before = structuredClone(state), pending = pendingResearchHandoffs(state), projected = researchHandoffContext(pending[0]);
  expect(pending).toHaveLength(2);
  expect(pending[0].sources).toHaveLength(1000);
  expect(projected).not.toHaveProperty('sources');
  expect(projected.proposal).toEqual(proposal);
  expect(projected.source).toEqual(single.source);
  expect(projected.sourceSet).toEqual({ count: 1000, digest: mathDigest(canonicalMathJson(pending[0].sources)),
    reference: { path: 'COOPERATION.json', handoffId: pending[0].id, contextDigest: pending[0].contextDigest } });
  expect(Buffer.byteLength(JSON.stringify(projected))).toBeLessThan(Buffer.byteLength(JSON.stringify(single)) + 16);
  const selected = selectResearchHandoffBatch(state, { maxBytes: 4096 });
  expect(selected.map(item => item.proposal.id)).toEqual([proposal.id, later.id]);
  expect(Buffer.byteLength(JSON.stringify(selected))).toBeGreaterThan(32 * 1024);
  expect(Buffer.byteLength(JSON.stringify(selected.map(researchHandoffContext)))).toBeLessThanOrEqual(4096);
  expect(state).toEqual(before);
});

const proposals = (count: number): CooperativeTask[] => Array.from({ length: count }, (_, index) =>
  ({ ...proposal, id: `bridge_${index}`, theoremName: `Original.bridge_${index}` }));

it('bounds a thousand pending proposals while retaining undispatched work for subsequent batches', () => {
  const state = fixture(); state.deliveries[0].lemmaRequests = proposals(1000);
  const before = structuredClone(state), batch = selectResearchHandoffBatch(state);
  expect(batch).toHaveLength(8);
  expect(Buffer.byteLength(JSON.stringify(batch.map(researchHandoffContext)))).toBeLessThanOrEqual(32 * 1024);
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
  const pending = pendingResearchHandoffs(state), two = JSON.stringify(pending.slice(0, 2).map(researchHandoffContext));
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

function waitingFixture() {
  const needed = node({ ...proposal, id: 'needed', theoremName: 'Original.needed' });
  const other = node({ ...proposal, id: 'other', theoremName: 'Original.other' });
  const state: { tasks: TaskRecord[]; deliveries: DeliveryRecord[]; researchDecisions?: ResearchHandoffDecision[] } = fixture();
  state.tasks.push(needed, other);
  const handoff = pendingResearchHandoffs(state)[0];
  const defer = (waitsOn = ['needed']) => {
    state.researchDecisions = resolveResearchHandoffs(state, [handoff.id], state.tasks.map(node => node.task),
      [{ id: handoff.id, status: 'deferred', reason: 'Need independently checked inputs.', waitsOn }]);
  };
  return { state, needed, other, handoff, defer };
}
function accept(node: TaskRecord, conditions: TaskProof['conditions'] = []) {
  const commit = 'b'.repeat(40);
  node.status = 'integrated';
  node.integratedCheck = { commit, sourceDigest: 'source', seedCommit: 'a'.repeat(40), passed: true,
    taskDigest: taskVersion(node.task), conditions, changes: [], verification: { status: 'kernel_verified', targetCommit: commit,
      results: [{ receiptId: 'checked-' + node.task.id, status: 'kernel_verified', targetCommit: commit }] } as TaskProof['verification'] };
  markTaskAcceptance(node.integratedCheck);
}

it('pins normalized wait contracts and reopens only when every exact input receives fresh unconditional acceptance', () => {
  const { state, needed, other, handoff, defer } = waitingFixture();
  defer(['other', 'needed']);
  expect(state.researchDecisions![0].waitsOn).toEqual([needed, other].map(node => ({ taskId: node.task.id, taskDigest: taskVersion(node.task) })));
  expect(pendingResearchHandoffs(state)).toEqual([]);
  expect(retainedResearchHandoffs(state)).toHaveLength(1);
  accept(needed);
  expect(pendingResearchHandoffs(state)).toEqual([]);
  accept(other, [{ taskId: 'unproved', taskDigest: 'unknown' }]);
  expect(pendingResearchHandoffs(state)).toEqual([]);
  accept(other);
  const reopened = pendingResearchHandoffs(state)[0];
  expect(reopened).toMatchObject({ id: handoff.id, status: 'pending', reopened: 'checked-prerequisites', decision: { status: 'deferred' } });
  expect(reopened.activationDigest).not.toBe(handoff.activationDigest);
  expect(selectResearchHandoffBatch(state)).toEqual([reopened]);
  expect(state.tasks.some(node => node.task.id === proposal.id)).toBe(false);
});

it('preserves a legacy deferred decision only while its explicit wait versions also bind the proposal inputs', () => {
  const { state, needed } = waitingFixture();
  state.deliveries[0].lemmaRequests = [{ ...proposal, dependsOn: [needed.task.id] }];
  const original = pendingResearchHandoffs(state)[0];
  state.researchDecisions = [{ id: original.id, deliveryId: original.deliveryId, status: 'deferred', reason: 'Await the pinned premise.',
    waitsOn: [{ taskId: needed.task.id, taskDigest: taskVersion(needed.task) }] }];
  expect(researchHandoffs(state)[0].status).toBe('deferred');
  const previousTask = needed.task;
  needed.task = { ...needed.task, type: 'True', revision: 1 };
  expect(pendingResearchHandoffs(state)).toHaveLength(1);
  needed.task = previousTask; accept(needed);
  expect(pendingResearchHandoffs(state)[0].reopened).toBe('checked-prerequisites');
});

it('requires revalidation of legacy decisions over proposal inputs whose historical versions were never pinned', () => {
  const { state, needed } = waitingFixture();
  state.deliveries[0].lemmaRequests = [{ ...proposal, dependsOn: [needed.task.id] }];
  const original = pendingResearchHandoffs(state)[0];
  state.researchDecisions = [{ id: original.id, deliveryId: original.deliveryId, status: 'rejected', reason: 'An old unbound decision.' }];
  expect(pendingResearchHandoffs(state)).toHaveLength(1);
  const decisions = resolveResearchHandoffs(state, [original.id], state.tasks.map(node => node.task), [
    { id: original.id, status: 'rejected', reason: 'Rechecked for the current exact input.' },
  ]);
  expect(decisions[0].contextDigest).toBe(original.contextDigest);
  expect(pendingResearchHandoffs({ ...state, researchDecisions: decisions })).toEqual([]);
});

it('ignores unrelated checked lemmas and stale wait contracts or modified receipts', () => {
  const { state, needed, other, defer } = waitingFixture(); defer();
  accept(other);
  expect(pendingResearchHandoffs(state)).toEqual([]);
  const originalTask = needed.task;
  needed.task = { ...needed.task, type: 'True' };
  accept(needed);
  expect(pendingResearchHandoffs(state)).toEqual([]);
  needed.task = originalTask; accept(needed);
  needed.integratedCheck!.commit = 'c'.repeat(40);
  expect(pendingResearchHandoffs(state)).toEqual([]);
});

it('does not use JSON receipts to reactivate waiting research before host rechecking', () => {
  const { state, needed, defer } = waitingFixture(); defer(); accept(needed);
  const restored = JSON.parse(JSON.stringify(state)) as typeof state;
  expect(pendingResearchHandoffs(restored)).toEqual([]);
  accept(restored.tasks.find(node => node.task.id === needed.task.id)!);
  expect(pendingResearchHandoffs(restored)[0].reopened).toBe('checked-prerequisites');
  expect(pendingResearchHandoffs(restored)).toEqual(pendingResearchHandoffs(state));
});

it('binds a reopened proposal to its current activation and prevents deferring again on already checked inputs', () => {
  const { state, needed, handoff, defer } = waitingFixture(); defer(); accept(needed);
  const current = pendingResearchHandoffs(state)[0];
  const response = [{ id: handoff.id, status: 'deferred', reason: 'Need independently checked inputs.', waitsOn: ['needed'] }];
  expect(() => resolveResearchHandoffs(state, [handoff.id], [...state.tasks.map(node => node.task), proposal], undefined))
    .toThrow('math_handoff_dispatch_superseded:');
  expect(() => resolveResearchHandoffs(state, [handoff.id], [...state.tasks.map(node => node.task), proposal], undefined,
    { [handoff.id]: handoff.activationDigest })).toThrow('math_handoff_dispatch_superseded:');
  expect(() => resolveResearchHandoffs(state, [handoff.id], state.tasks.map(node => node.task), response,
    { [handoff.id]: current.activationDigest })).toThrow('math_handoff_waits_on_satisfied:');
  expect(resolveResearchHandoffs(state, [handoff.id], [...state.tasks.map(node => node.task), proposal], undefined,
    { [handoff.id]: current.activationDigest })[0]).toMatchObject({ status: 'adopted', taskId: proposal.id });
});

it('allows an explicit waiting-condition update or cancellation without redispatching unchanged proposals', () => {
  const { state, handoff, other, defer } = waitingFixture(); defer();
  const tasks = state.tasks.map(node => node.task);
  const repeated = [{ id: handoff.id, status: 'deferred', reason: 'Need independently checked inputs.', waitsOn: ['needed'] }];
  expect(resolveResearchHandoffs(state, [], tasks, repeated)).toEqual([]);
  const updated = resolveResearchHandoffs(state, [], tasks,
    [{ id: handoff.id, status: 'deferred', reason: 'Use a different proved estimate.', waitsOn: ['other'] }]);
  expect(updated[0].waitsOn).toEqual([{ taskId: other.task.id, taskDigest: taskVersion(other.task) }]);
  state.researchDecisions = updated;
  state.researchDecisions = resolveResearchHandoffs(state, [], tasks,
    [{ id: handoff.id, status: 'rejected', reason: 'This route is no longer useful.' }]);
  accept(other);
  expect(pendingResearchHandoffs(state)).toEqual([]);
  expect(retainedResearchHandoffs(state)).toEqual([]);
});

it.each([[], ['missing'], ['investigate'], ['needed', 'needed'], [1], null])
  ('rejects invalid wait inputs before changing state: %j', waitsOn => {
    const { state, handoff } = waitingFixture(), before = structuredClone(state);
    expect(() => resolveResearchHandoffs(state, [handoff.id], state.tasks.map(node => node.task),
      [{ id: handoff.id, status: 'deferred', reason: 'Need a checked premise.', waitsOn }])).toThrow('math_handoff_waits_on_invalid');
    expect(state).toEqual(before);
  });

it('does not revive a waiting proposal whose source or delivery has been superseded', () => {
  const { state, needed, defer } = waitingFixture(); defer(); accept(needed);
  expect(pendingResearchHandoffs({ ...state, deliveries: [{ ...state.deliveries[0], status: 'superseded' }] })).toEqual([]);
  state.tasks[0].task = { ...state.tasks[0].task, revision: 1 };
  expect(pendingResearchHandoffs(state)).toEqual([]);
});
