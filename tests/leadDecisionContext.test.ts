import { expect, it } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import type { SolverRunState } from '../src/solver/archive';
import type { CooperationState } from '../src/solver/cooperation';
import type { DeliveryRecord } from '../src/solver/deliveries';
import { buildResearchContext } from '../src/solver/modules/context';
import type { SolverProblem } from '../src/solver/problem';
import { pendingResearchChallenges } from '../src/solver/researchChallenges';
import { pendingResearchHandoffs, selectResearchHandoffBatch } from '../src/solver/researchHandoffs';
import { taskVersion, type CooperativeAction, type CooperativeTask, type TaskRecord } from '../src/solver/tasks';

const formal = 'namespace Original\ntheorem target : True := by sorry\nend Original';
const problem = { projectRelative: '.', ownedFiles: ['Submission.lean'], declarations: {
  'Submission.lean': [{ name: 'target', header: 'target : True' }] },
  targets: [{ proofPath: 'Submission.lean', theoremName: 'Original.target' }], receiptDigest: 'problem',
  baseCommit: 'a'.repeat(40), contract: { formalStatement: formal, assumptions: [] } } as unknown as SolverProblem;
const task = (id: string, kind: CooperativeTask['kind'] = 'lemma', dependsOn: string[] = []): CooperativeTask => ({
  id, kind, dependsOn, objective: 'Prove ' + id, revision: 0,
  ...(['lemma', 'goal'].includes(kind) ? { type: '∀ n : Nat, n = n', proofPath: 'Submission.lean',
    theoremName: kind === 'goal' ? 'Original.target' : 'Original.' + id } : {}),
});
const node = (t: CooperativeTask): TaskRecord => ({ task: t, status: 'pending', attempts: 0 });
const base = (): CooperationState => ({ tasks: [node(task('goal', 'goal', ['core'])), node(task('core'))] });
const delivery = (source: CooperativeTask, id: string, proposals: CooperativeTask[] = []): DeliveryRecord => ({
  id, producer: 'researcher', taskId: source.id, taskDigest: taskVersion(source), kind: 'research', status: 'advisory',
  summary: 'Exact new inference', statement: '', premises: [], dependencies: [], remainingObligations: [],
  evidenceRefs: [], createdAt: 1, lemmaRequests: proposals,
});
const action = (cooperation: CooperationState): Extract<CooperativeAction, { kind: 'lead' | 'assemble' }> => {
  const handoffs = selectResearchHandoffBatch(cooperation, { maxItems: 2, maxBytes: 12 * 1024 });
  const challenges = pendingResearchChallenges(cooperation).slice(0, 2);
  return { kind: 'lead', coordination: true, seedCommit: problem.baseCommit, planVersion: 'plan', planNonce: 'nonce',
    handoffIds: handoffs.map(item => item.id), handoffActivations: Object.fromEntries(handoffs.map(item => [item.id, item.activationDigest])),
    challengeIds: challenges.map(item => item.id), challengeActivations: Object.fromEntries(challenges.map(item => [item.id, item.activationDigest])),
    capacityRefill: { requestId: 'capacity-request', inputDigest: 'capacity-input', requestedAt: 1, workerIds: ['researcher'] } };
};
const context = (cooperation: CooperationState, assignment = action(cooperation)) => buildResearchContext(problem,
  { problem, cooperation, environmentDigest: 'environment' } as SolverRunState, {
    root: '/runtime', worktree: '/proof', environment: {}, taskText: 'Prove the exact original proposition.',
    retrievalRoot: '/library', frozenContexts: { 'Submission.lean': formal }, assignment,
  });
const packet = (message: string) => JSON.parse(message.split('Current bounded Lead decision (advisory; no proof acceptance):\n')[1].split('\n\n')[0]);
const response = (instructions: string) => JSON.parse(instructions.split('replace statuses and placeholders with your supported decisions):\n')[1].split('\n\n')[0]);

it('keeps frozen problem identity and the active frontier while excluding unrelated long tasks from coordination', () => {
  const state = base();
  for (let i = 0; i < 80; i++) state.tasks.push(node({ ...task('unrelated_' + i), objective: 'Unrelated mathematical task '.repeat(200) }));
  const current = action(state);
  current.stagnationRecovery = { requestId: 'stagnation-request', inputDigest: 'stagnation-input', requestedAt: 1,
    reason: 'frontier-not-decomposed', taskIds: ['core'], workerIds: [] };
  const result = context(state, current);
  expect(result.manifest!.requiredTaskIds).toEqual(['goal', 'core']);
  expect(result.manifest!.included.map(item => item.id)).toEqual(expect.arrayContaining([
    'original-problem', 'original-assumptions', 'frozen-sources', 'original-targets', 'work-contract', 'coordination-decision',
  ]));
  expect(result.message).toContain(formal);
  expect(result.message).not.toContain('Unrelated mathematical task');
  expect(result.manifest!.omitted).toContainEqual({ id: 'interface:unrelated_0', kind: 'interfaces', reason: 'outside-task-scope' });
  expect(result.manifest!.mandatoryBytes).toBeLessThan(32 * 1024);
  expect(result.manifest!.optionalBytes).toBe(0);
  expect(result.continuationMessage).toContain('Current bounded Lead decision');
  expect(result.continuationMessage).toContain('capacity-request');
  expect(result.continuationMessage).not.toContain('Preserve the complete current math-plan');
});

it('presents a small version-bound inbox and leaves no-work assessments for a later dispatch', () => {
  const state = base(), source = task('investigate', 'research'); state.tasks.push(node(source));
  state.deliveries = Array.from({ length: 5 }, (_, i) => delivery(source, 'd' + i, [task('proposal_' + i)]));
  const result = context(state), decision = packet(result.message), template = response(result.instructions);
  expect(decision.pending).toEqual({ handoffs: 5, challenges: 0 });
  expect(decision.shown.handoffIds).toHaveLength(2);
  expect(decision.queuedForLater).toBe(3);
  expect(template).toMatchObject({ kind: 'handoff', baseVersion: 'plan', dispatchNonce: 'nonce' });
  expect(template.handoffDecisions).toHaveLength(2);
  expect(template).not.toHaveProperty('assessments');
  expect(result.instructions).toContain('Do not attach no-independent-work assessments');
  expect(result.instructions).toContain('preserving its mathematical contract, owner gates');
  expect(pendingResearchHandoffs(state)).toHaveLength(5);
});

it('includes only worker identities and current assignments from full persisted worker records', () => {
  const state = base(), current = action(state);
  const fullWorkers = Array.from({ length: 8 }, (_, index) => ({ id: 'worker_' + index,
    role: index ? 'researcher' : 'lead', threadId: 'PRIVATE_THREAD',
    lastContextManifest: { included: [{ text: 'PRIOR_CONTEXT_SENTINEL'.repeat(10000) }] },
    previousThreadIds: ['PRIVATE_HISTORY'], worktree: '/private/worktree' }));
  const result = buildResearchContext(problem,
    { problem, cooperation: state, workers: fullWorkers } as unknown as SolverRunState, {
      root: '/runtime', worktree: '/proof', environment: {}, taskText: 'Prove original', retrievalRoot: '/library',
      frozenContexts: { 'Submission.lean': formal }, assignment: current,
    });
  expect(packet(result.message).peers).toEqual(fullWorkers.map(worker => ({ id: worker.id, role: worker.role, assignments: [] })));
  expect(result.message).not.toContain('PRIOR_CONTEXT_SENTINEL');
  expect(result.message).not.toContain('PRIVATE_THREAD');
  expect(result.manifest!.mandatoryBytes).toBeLessThan(32 * 1024);
});

it('retains exact immutable delivery inputs even when the source is an original goal', () => {
  const state = base(), source = state.tasks[0].task;
  const dependency = { ...task('actual_input'), type: '∀ (P Q : Prop), P ∧ Q → Q ∧ P' };
  state.tasks.push(node(dependency));
  const finding = JSON.stringify({ needsDecision: true, conclusion: 'inconclusive', summary: 'The exact input is insufficient.' });
  state.deliveries = [{ ...delivery(source, 'goal-finding'), finding, findingDigest: mathDigest(finding),
    dependencies: [{ taskId: dependency.id, taskDigest: taskVersion(dependency) }] }];
  const result = context(state);
  expect(result.manifest!.requiredTaskIds).toContain(dependency.id);
  expect(result.message).toContain(JSON.stringify(dependency.type));
  expect(result.message).toContain(taskVersion(dependency));
  expect(result.instructions).toContain('A disputed decision requires nonempty evidenceRefs');
  expect(result.instructions).toContain('A deferred decision requires actual waitsOn inputs');
  expect(response(result.instructions).challengeDecisions[0]).toMatchObject({ status: 'deferred', reopenOn: 'SPECIFIC_NEW_INPUT' });
});

it('emits the exact explicit no-work envelope only after the inbox has been considered', () => {
  const state = base(), current = action(state), result = context(state, current);
  expect(response(result.instructions)).toEqual({ kind: 'assessment', baseVersion: 'plan', dispatchNonce: 'nonce',
    assessments: [{ kind: 'capacity', requestId: 'capacity-request', inputDigest: 'capacity-input',
      outcome: 'no-independent-work', reason: 'EXACT_MISSING_INPUT_AND_REOPEN_TRIGGER' }] });
  expect(result.workContract).toMatchObject({ stage: 'coordination-decision', sourcePolicy: 'read-only' });
  expect(result.instructions).toContain('New pending inbox input prevents its acceptance');
});

it('keeps an oversized exact proposal intact and lets the required-context budget reject it', () => {
  const state = base(), source = task('investigate', 'research'); state.tasks.push(node(source));
  const exactType = '∀ (P : Prop), ' + 'P → '.repeat(18000) + 'P';
  state.deliveries = [delivery(source, 'oversized', [{ ...task('large_proposal'), type: exactType }])];
  const current = action(state), result = context(state, current);
  expect(result.message).toContain(JSON.stringify(exactType));
  expect(() => buildResearchContext(problem, { problem, cooperation: state } as SolverRunState, {
    root: '/runtime', worktree: '/proof', environment: {}, taskText: 'Prove original', retrievalRoot: '/library',
    frozenContexts: { 'Submission.lean': formal }, assignment: current, maxContextBytes: 16 * 1024,
  })).toThrow('math_context_mandatory_overflow');
});
