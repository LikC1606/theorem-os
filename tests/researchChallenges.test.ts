import { expect, it } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { pendingResearchChallenges, preserveResearchChallengeBacklog, researchChallenges, resolveResearchChallenges,
  retainedResearchChallenges, researchChallengeContext, selectResearchChallengeBatch } from '../src/solver/researchChallenges';
import { markTaskAcceptance, taskVersion, type CooperativeTask, type TaskRecord } from '../src/solver/tasks';
import type { DeliveryRecord } from '../src/solver/deliveries';
import type { TaskProof } from '../src/solver/cooperativeProof';

function fixture() {
  const core: CooperativeTask = { id: 'core', kind: 'lemma', objective: 'The challenged inference', revision: 0,
    type: '∀ n : Nat, n = n', theoremName: 'core', proofPath: 'Submission.lean', dependsOn: [] };
  const goal: CooperativeTask = { id: 'goal', kind: 'goal', objective: 'Original', revision: 0, dependsOn: ['core'] };
  const review: CooperativeTask = { id: 'feasibility', kind: 'research', objective: 'Challenge the inference',
    revision: 0, dependsOn: ['goal', 'core'], reviewScope: 'feasibility' };
  const finding = JSON.stringify({ taskId: review.id, conclusion: 'refuted', needsDecision: true,
    summary: 'COUNTEREXAMPLE_SENTINEL', evidenceRefs: ['FIXED_COUNTEREXAMPLE_REF'] });
  const tasks: TaskRecord[] = [core, goal, review].map(task => ({ task, attempts: 0,
    status: task === review ? 'completed' : 'pending', ...(task === review ? { finding } : {}) }));
  const delivery: DeliveryRecord = { id: 'research', kind: 'research', status: 'advisory', producer: 'independent',
    taskId: review.id, taskDigest: taskVersion(review), findingDigest: mathDigest(finding),
    summary: 'COUNTEREXAMPLE_SENTINEL', evidenceRefs: ['FIXED_COUNTEREXAMPLE_REF'], statement: '', premises: [],
    dependencies: [goal, core].map(task => ({ taskId: task.id, taskDigest: taskVersion(task) })), remainingObligations: [],
    commit: 'a'.repeat(40), createdAt: 1 };
  return { tasks, deliveries: [delivery], proofRoutes: [{ id: 'route', targetTaskId: goal.id,
    closingTaskId: core.id, prerequisiteTaskIds: [] }] };
}

it('derives an advisory challenge with exact sources from a refuted reverse feasibility dependency', () => {
  const state = fixture(), [challenge] = pendingResearchChallenges(state);
  expect(challenge).toMatchObject({ sourceTaskId: 'feasibility', conclusion: 'refuted', summary: 'COUNTEREXAMPLE_SENTINEL',
    evidenceRefs: ['FIXED_COUNTEREXAMPLE_REF'], source: { commit: 'a'.repeat(40) } });
  expect(() => resolveResearchChallenges(state, [challenge.id], { [challenge.id]: challenge.activationDigest },
    state.tasks.map(node => node.task), undefined)).toThrow('math_challenge_unresolved');
});

it('keeps oversized complete findings retrievable without overflowing mandatory decision context', () => {
  const state = fixture();
  const finding = JSON.stringify({ conclusion: 'refuted', summary: 'A large complete argument', argument: 'precise '.repeat(100000) });
  state.tasks[2].finding = finding;
  Object.assign(state.deliveries[0], { finding, findingDigest: mathDigest(finding) });
  const [challenge] = pendingResearchChallenges(state), context = researchChallengeContext(challenge);
  expect(challenge.finding).toBe(finding);
  expect(context).not.toHaveProperty('finding');
  expect(context).toMatchObject({ findingBytes: Buffer.byteLength(finding),
    findingSource: { id: challenge.id, findingDigest: mathDigest(finding) } });
  expect(Buffer.byteLength(JSON.stringify(context))).toBeLessThan(4096);
});

it('bounds a coordination batch without truncating its first finding or consuming later challenges', () => {
  const state = fixture();
  state.deliveries = Array.from({ length: 5 }, (_, index) => ({ ...state.deliveries[0]!, id: 'finding-' + index }));
  const pending = pendingResearchChallenges(state);
  expect(selectResearchChallengeBatch(state, { maxItems: 2, maxBytes: 12 * 1024 })).toEqual(pending.slice(0, 2));
  expect(selectResearchChallengeBatch(state, { maxItems: 2, maxBytes: 1 })).toEqual([pending[0]]);
  expect(selectResearchChallengeBatch(state)).toEqual(pending);
  expect(pendingResearchChallenges(state)).toEqual(pending);
});

it('persists a specific response through serialization without granting proof acceptance', () => {
  const state = fixture(), [challenge] = pendingResearchChallenges(state);
  const challengeDecisions = resolveResearchChallenges(state, [challenge.id], { [challenge.id]: challenge.activationDigest },
    state.tasks.map(node => node.task), [{ id: challenge.id, status: 'disputed', reason: 'The example violates the premise.',
      evidenceRefs: ['fixed-commit:RESEARCH.md'] }]);
  const restored = JSON.parse(JSON.stringify({ ...state, challengeDecisions }));
  expect(pendingResearchChallenges(restored)).toEqual([]);
  expect(researchChallenges(restored)[0]).toMatchObject({ status: 'disputed', decision: { reason: 'The example violates the premise.' } });
  expect(restored.tasks.map((node: TaskRecord) => node.status)).toEqual(['pending', 'pending', 'completed']);
});

it('invalidates a decision on same-ID OR topology changes and rejects a stale dispatched activation', () => {
  const state = fixture(), [original] = pendingResearchChallenges(state);
  const response = [{ id: original.id, status: 'deferred', reason: 'Need a new bound.', reopenOn: 'A valid uniform bound is available.' }];
  const challengeDecisions = resolveResearchChallenges(state, [original.id], { [original.id]: original.activationDigest },
    state.tasks.map(node => node.task), response);
  const changed = { ...state, challengeDecisions, proofRoutes: [{ ...state.proofRoutes[0], prerequisiteTaskIds: ['core'] }] };
  expect(pendingResearchChallenges(changed)).toHaveLength(1);
  expect(() => resolveResearchChallenges(changed, [original.id], { [original.id]: original.activationDigest },
    state.tasks.map(node => node.task), response)).toThrow('math_challenge_dispatch_superseded');
});

it('binds route topology for fixed delivery inputs outside the current source dependency list', () => {
  const state = fixture();
  state.tasks[2]!.task = { ...state.tasks[2]!.task, dependsOn: [] };
  state.deliveries[0]!.taskDigest = taskVersion(state.tasks[2]!.task);
  const [challenge] = pendingResearchChallenges(state);
  const response = [{ id: challenge.id, status: 'disputed', reason: 'The boundary witness misses a premise.', evidenceRefs: ['fixed-argument'] }];
  const challengeDecisions = resolveResearchChallenges(state, [challenge.id], { [challenge.id]: challenge.activationDigest },
    state.tasks.map(node => node.task), response);
  const changed = { ...state, challengeDecisions, proofRoutes: [{ ...state.proofRoutes[0], prerequisiteTaskIds: ['core'] }] };
  expect(pendingResearchChallenges(changed)).toHaveLength(1);
  expect(() => resolveResearchChallenges(changed, [challenge.id], { [challenge.id]: challenge.activationDigest },
    state.tasks.map(node => node.task), response)).toThrow('math_challenge_dispatch_superseded');
});

it.each(['null', '[]', '42'])('ignores malformed restored finding %s without crashing planning', finding => {
  const state = fixture();
  state.tasks[2]!.finding = finding;
  state.deliveries[0]!.findingDigest = mathDigest(finding);
  expect(researchChallenges(state)).toEqual([]);
});

it('does not require late arrivals and does not expose a challenge when its scoped source is absent', () => {
  const state = fixture();
  expect(resolveResearchChallenges(state, [], {}, state.tasks.map(node => node.task), undefined)).toEqual([]);
  expect(researchChallenges({ ...state, tasks: state.tasks.slice(0, 2) })).toEqual([]);
  expect(() => preserveResearchChallengeBacklog(state, state.tasks.slice(0, 2).map(node => node.task), state.proofRoutes, []))
    .toThrow('math_challenge_backlog_source_required');
});

it.each([
  { status: 'disputed', reason: 'Disagree.' },
  { status: 'deferred', reason: 'Later.' },
  { status: 'deferred', reason: 'Wait.', waitsOn: ['feasibility'] },
  { status: 'revised', reason: '' },
])('rejects an ungrounded response %j', response => {
  const state = fixture(), [challenge] = pendingResearchChallenges(state);
  expect(() => resolveResearchChallenges(state, [challenge.id], { [challenge.id]: challenge.activationDigest },
    state.tasks.map(node => node.task), [{ id: challenge.id, ...response }])).toThrow('math_challenge_');
});

it('ignores superseded source contracts and tampered finding bindings', () => {
  const state = fixture();
  expect(researchChallenges({ ...state, deliveries: [{ ...state.deliveries[0], findingDigest: 'wrong' }] })).toEqual([]);
  state.tasks[0]!.task = { ...state.tasks[0]!.task, revision: 1 };
  expect(researchChallenges(state)).toEqual([]);
});

it('never attaches current findings to older research deliveries without an exact digest binding', () => {
  const state = fixture(), original = state.deliveries[0]!;
  const deliveries = [{ ...original, id: 'old-supporting', findingDigest: undefined,
    summary: 'An old supporting argument.', evidenceRefs: ['old-supporting-source'], commit: 'b'.repeat(40) }, original];
  const challenges = researchChallenges({ ...state, deliveries });
  expect(challenges).toHaveLength(1);
  expect(challenges[0]).toMatchObject({ deliveryId: original.id, summary: 'COUNTEREXAMPLE_SENTINEL',
    source: { commit: 'a'.repeat(40) } });
  expect(researchChallenges({ ...state, deliveries: [deliveries[0]!] })).toEqual([]);
});

function deferredFixture() {
  const state = fixture();
  const waiting: CooperativeTask = { id: 'waiting', kind: 'lemma', objective: 'Supply a new bound', revision: 0,
    proofPath: 'Submission.lean', theoremName: 'waiting', type: 'True', dependsOn: [] };
  state.tasks.push({ task: waiting, status: 'pending', attempts: 0 });
  const [challenge] = pendingResearchChallenges(state);
  const challengeDecisions = resolveResearchChallenges(state, [challenge.id], { [challenge.id]: challenge.activationDigest },
    state.tasks.map(node => node.task), [{ id: challenge.id, status: 'deferred', reason: 'Need a checked new bound.', waitsOn: [waiting.id] }]);
  return { ...state, challengeDecisions };
}

it.each(['feasibility', 'core', 'goal', 'waiting'])('retains deferred research inputs when the next plan omits %s', removed => {
  const state = deferredFixture();
  expect(pendingResearchChallenges(state)).toEqual([]);
  expect(retainedResearchChallenges(state)).toHaveLength(1);
  expect(() => preserveResearchChallengeBacklog(state, state.tasks.filter(node => node.task.id !== removed).map(node => node.task),
    state.proofRoutes, [])).toThrow('math_challenge_backlog_source_required');
  expect(researchChallenges(state)[0]!.status).toBe('deferred');
});

it('keeps deferred decisions through restoration and reopens after fresh checked waiting evidence', () => {
  const state = deferredFixture(), node = state.tasks.find(node => node.task.id === 'waiting')!;
  const proof = { passed: true, commit: 'source-commit', sourceDigest: 'source', taskDigest: taskVersion(node.task),
    verification: { status: 'kernel_verified', targetCommit: 'checked-commit', results: [
      { receiptId: 'fresh-receipt', targetCommit: 'checked-commit', status: 'kernel_verified' },
    ] } } as TaskProof;
  node.status = 'integrated'; node.integratedCheck = proof;
  expect(pendingResearchChallenges(state)).toEqual([]);
  markTaskAcceptance(proof);
  expect(pendingResearchChallenges(state)).toHaveLength(1);
  expect(researchChallenges(state)[0]!.decision?.waitsOn).toEqual([{ taskId: 'waiting', taskDigest: taskVersion(node.task) }]);
  const restored = JSON.parse(JSON.stringify(state));
  expect(pendingResearchChallenges(restored)).toEqual([]);
  expect(retainedResearchChallenges(restored)).toHaveLength(1);
  markTaskAcceptance(restored.tasks.find((node: TaskRecord) => node.task.id === 'waiting').integratedCheck);
  expect(pendingResearchChallenges(restored)).toHaveLength(1);
});

it('reopens a deferred challenge after a same-ID waiting contract changes without losing its source', () => {
  const state = deferredFixture();
  const tasks = state.tasks.map(node => node.task.id === 'waiting' ? { ...node.task, type: 'True ∧ True' } : node.task);
  expect(() => preserveResearchChallengeBacklog(state, tasks, state.proofRoutes, [])).not.toThrow();
  const changed = { ...state, tasks: state.tasks.map((node, index) => ({ ...node, task: tasks[index]! })) };
  expect(pendingResearchChallenges(changed)).toHaveLength(1);
  expect(researchChallenges(changed)[0]!.decision).toBeUndefined();
});

it.each(['feasibility', 'core'])('allows an explicitly revised %s input to supersede evidence bound to the old contract', changedId => {
  const state = deferredFixture();
  const tasks = state.tasks.map(node => node.task.id === changedId ? { ...node.task, objective: 'A revised mathematical input',
    ...(node.task.kind === 'lemma' ? { type: 'True ∧ True' } : {}) } : node.task);
  expect(() => preserveResearchChallengeBacklog(state, tasks, state.proofRoutes, [])).not.toThrow();
  const changed = { ...state, tasks: state.tasks.map((node, index) => ({ ...node, task: tasks[index]! })) };
  expect(researchChallenges(changed)).toEqual([]);
  expect(changed.deliveries[0]!.findingDigest).toBe(state.deliveries[0]!.findingDigest);
});

it('permits an explicit grounded update to a deferred decision before discarding its retained tasks', () => {
  const state = deferredFixture(), challenge = researchChallenges(state)[0]!;
  const tasks = state.tasks.filter(node => !['feasibility', 'waiting'].includes(node.task.id)).map(node => node.task);
  const decisions = resolveResearchChallenges(state, [], {}, tasks, [{ id: challenge.id, status: 'disputed',
    reason: 'The witness fails the stated positivity assumption.', evidenceRefs: ['fixed-counterargument'] }]);
  expect(decisions).toHaveLength(1);
  expect(() => preserveResearchChallengeBacklog(state, tasks, state.proofRoutes, decisions)).not.toThrow();
  expect(state.tasks.map(node => node.status)).toEqual(['pending', 'pending', 'completed', 'pending']);
});
