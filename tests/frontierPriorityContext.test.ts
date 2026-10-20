import { afterEach, expect, it, vi } from 'vitest';
import * as contextCompiler from '../src/solver/contextCompiler';
import type { CooperationState } from '../src/solver/cooperation';
import type { SolverRunState } from '../src/solver/archive';
import type { SolverProblem } from '../src/solver/problem';
import { buildResearchContext } from '../src/solver/modules/context';
import { assignmentDeliveryFile, initialPlanDeliveryFile, taskVersion, type CooperativeAction, type TaskRecord } from '../src/solver/tasks';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';
import { researchHandoffs, resolveResearchHandoffs } from '../src/solver/researchHandoffs';

const seedCommit = 'a'.repeat(40);
const formal = 'namespace Original\ntheorem target : True := by sorry\nend Original';
const problem = {
  projectRelative: 'generated/p', ownedFiles: ['Submission.lean'],
  declarations: { 'Submission.lean': [{ name: 'target', header: 'target : True' }] },
  sourceImports: { 'Submission.lean': ['Mathlib.Data.Nat.Basic'] }, sourceStructure: { 'Submission.lean': 'context' },
  targets: [{ proofPath: 'Submission.lean', theoremName: 'Original.target', declarationHash: 'original-type' }],
  receiptDigest: 'problem-receipt', baseCommit: seedCommit,
  contract: { formalStatement: formal, informalStatement: 'Prove the original proposition.', assumptions: [],
    statementHash: 'statement', leanStatementHash: 'lean-statement' },
} as unknown as SolverProblem;
const node = (id: string, kind: TaskRecord['task']['kind'] = 'lemma', dependsOn: string[] = []): TaskRecord => ({
  task: { id, kind, objective: `Prove ${id}`, dependsOn, revision: 0,
    ...(['goal', 'lemma'].includes(kind) ? { type: 'True', theoremName: kind === 'goal' ? 'Original.target' : `Original.${id}`,
      proofPath: 'Submission.lean' } : {}) },
  status: 'pending', attempts: 0,
});
const fixture = () => {
  const core = node('core'); core.status = 'blocked'; core.attempts = 2;
  const seed = node('seed'), collar = node('collar', 'lemma', ['seed']);
  const probe = node('probe', 'research', ['core', 'collar']);
  const goal = node('private_original_goal', 'goal', ['core']);
  const cooperation: CooperationState = { canonicalCommit: seedCommit, tasks: [core, seed, collar, probe, goal] };
  return { core, seed, collar, probe, goal, cooperation };
};
const actionFor = (record: TaskRecord): CooperativeAction => ({ kind: 'task', task: record.task,
  assignment: { taskId: record.task.id, taskDigest: taskVersion(record.task), workerId: 'researcher', seedCommit } });
const contextFor = (cooperation: CooperationState, action: CooperativeAction) => buildResearchContext(problem,
  { problem, cooperation, environmentDigest: 'environment' } as SolverRunState, {
    root: '/runtime', worktree: '/proof', environment: {}, taskText: 'Prove the original target.',
    retrievalRoot: '/library', assignment: action,
    frozenContexts: { 'Submission.lean': contextCompiler.frozenSourceContext(problem, 'Submission.lean', formal) },
  });
const packet = (message: string) => JSON.parse(message.split('Original-goal focus (advisory, not proof acceptance):\n')[1].split('\n\n')[0]);
/** Compiles every task context with no optional context allowance. */
const withoutOptionalContext = () => {
  const compile = contextCompiler.compileTaskContext;
  vi.spyOn(contextCompiler, 'compileTaskContext').mockImplementation(input => compile({ ...input, maxOptionalContextBytes: 0 }));
};

afterEach(() => vi.restoreAllMocks());

it.each(['lemma', 'goal', 'research', 'sketch'] as const)(
  'retains the complete %s delivery protocol without optional context or repeated protocol text', kind => {
    withoutOptionalContext();
    const record = node('assigned', kind), action = actionFor(record);
    if (action.kind !== 'task') throw new Error('fixture_assignment');
    const context = contextFor({ canonicalCommit: seedCommit, tasks: [record] }, action);

    expect(context.manifest).toMatchObject({ maxOptionalBytes: 0, optionalBytes: 0 });
    expect(context.manifest!.included).toContainEqual(expect.objectContaining({ id: 'assignment-policy', required: true }));
    expect(context.instructions).toContain(assignmentDeliveryFile(action.assignment));
    expect(context.instructions).toContain('"kind":"research","finding":');
    expect(context.instructions).toContain('publishing does not finish or park your proof task');
    expect(context.instructions).toContain('The host freezes the saved sources and independently checks and integrates them');
    expect(context.instructions).toContain('Do not truncate the delivery log');
    expect((context.instructions + context.message).match(/To share before returning/g)).toHaveLength(1);
    expect(context.message).toContain(`Your role: ${kind === 'goal' ? 'engineer' : 'researcher'}`);
    expect(context.message).toContain('Delivery protocol: see session instructions.');
    expect(context.message).toContain(formal);
  });

it('retains the complete initial plan publication protocol without optional context or repeated protocol text', () => {
  withoutOptionalContext();
  const action: CooperativeAction = { kind: 'lead', seedCommit, initialPlanNonce: 'publication', planVersion: 'plan-version' };
  const context = contextFor({ canonicalCommit: seedCommit, tasks: [] }, action);

  expect(context.manifest).toMatchObject({ maxOptionalBytes: 0, optionalBytes: 0 });
  expect(context.instructions).toContain(initialPlanDeliveryFile(action));
  expect(context.instructions).toContain('"kind":"plan","baseVersion":"plan-version"');
  expect(context.instructions).toContain('Only the first valid initial publication is accepted');
  expect(context.instructions).toContain('Do not truncate the log');
  expect((context.instructions + context.message).match(/Once a minimal executable initial plan is ready/g)).toHaveLength(1);
  expect(context.message).toContain('Your role: lead');
  expect(context.message).toContain('Delivery protocol: see session instructions.');
  expect(context.message).toContain(formal);
});

it('retains the assigned support task, its actual consumer and open frontier without optional hints', () => {
  withoutOptionalContext();
  const { seed, cooperation } = fixture();
  const context = contextFor(cooperation, actionFor(seed));

  expect(context.manifest).toMatchObject({ maxOptionalBytes: 0, optionalBytes: 0 });
  expect(context.manifest!.included).toContainEqual(expect.objectContaining({ id: 'frontier-focus', required: true }));
  expect(context.manifest!.omitted).toContainEqual({ id: 'proof-continuation', kind: 'continuation', reason: 'optional-budget' });
  expect(packet(context.message)).toEqual({ goalTaskIds: ['private_original_goal'], frontierTaskIds: ['core'],
    assignedTaskId: 'seed', relationship: 'frontier-support', plannedConsumers: ['collar'] });
  expect(context.manifest!.requiredTaskIds).toContain('seed');
});

it('keeps concrete concurrent questions mandatory while preserving private route scope and independent review', () => {
  withoutOptionalContext();
  const { seed, core, probe, cooperation } = fixture();
  core.status = 'running'; probe.status = 'running';
  const hidden = node('private_question', 'research'); hidden.status = 'running';
  hidden.task = { ...hidden.task, groupId: 'private-route', sharing: 'group', objective: 'PRIVATE_CONCURRENT_QUESTION' };
  cooperation.tasks.push(hidden);
  const context = contextFor(cooperation, actionFor(seed));
  expect(context.manifest!.included).toContainEqual(expect.objectContaining({ id: 'parallel-questions', required: true }));
  const questions = JSON.parse(context.message.split('Current in-flight questions (scope-visible assignments; advisory, retrieve exact interfaces from COOPERATION.json):\n')[1]
    .split('\n\n')[0]);
  expect(questions.map((question: { taskId: string }) => question.taskId)).toEqual(['core', 'probe']);
  expect(context.instructions).toContain('Leave a slot waiting for input');
  probe.task = { ...probe.task, reviewScope: 'feasibility' };
  expect(contextFor(cooperation, actionFor(probe)).manifest!.included.some(section => section.id === 'parallel-questions')).toBe(false);
});

it('updates the advisory research focus when its original gap becomes checked', () => {
  const { core, probe, cooperation } = fixture();
  expect(packet(contextFor(cooperation, actionFor(probe)).message)).toMatchObject({
    frontierTaskIds: ['core'], relationship: 'targeted-investigation',
  });

  core.status = 'integrated';
  core.integratedCheck = { passed: true, taskDigest: taskVersion(core.task), conditions: [],
    verification: { status: 'kernel_verified', targetCommit: seedCommit, results: [
      { status: 'kernel_verified', targetCommit: seedCommit, receiptId: 'fixture-receipt' },
    ] } } as TaskRecord['integratedCheck'];

  expect(packet(contextFor(cooperation, actionFor(probe)).message)).toMatchObject({
    frontierTaskIds: ['private_original_goal'], relationship: 'independent-exploration',
  });
  expect(cooperation.tasks.find(record => record.task.kind === 'goal')!.status).toBe('pending');
});

it('builds mandatory Lead focus and task focus only from the supplied scoped graph', () => {
  const { seed, cooperation } = fixture();
  const lead = contextFor(cooperation, { kind: 'lead', seedCommit });
  expect(packet(lead.message)).toEqual({ goalTaskIds: ['private_original_goal'], frontierTaskIds: ['core'] });
  const scoped = { ...cooperation, tasks: [seed] };
  const context = contextFor(scoped, actionFor(seed));

  expect(packet(context.message)).toEqual({ goalTaskIds: [], frontierTaskIds: [],
    assignedTaskId: 'seed', relationship: 'independent-exploration', plannedConsumers: [] });
  expect(context.message).not.toContain('private_original_goal');
  expect(context.message).not.toContain('Original.core');
});

it('shows adopted research and its missing consumer connection to Lead without requiring an immediate consumer', () => {
  const source = node('investigation', 'research'), adopted = node('bridge'), goal = node('goal', 'goal');
  source.status = 'completed';
  const cooperation: CooperationState = { canonicalCommit: seedCommit, tasks: [source, adopted, goal], deliveries: [{
    id: 'proposal', producer: 'researcher', taskId: source.task.id, taskDigest: taskVersion(source.task),
    kind: 'research', status: 'advisory', summary: 'A reusable bridge.', statement: '', premises: [], dependencies: [],
    remainingObligations: [], evidenceRefs: [], createdAt: 1, lemmaRequests: [adopted.task],
  }] };
  const handoff = researchHandoffs(cooperation)[0];
  cooperation.researchDecisions = resolveResearchHandoffs(cooperation, [handoff.id], cooperation.tasks.map(item => item.task), undefined);
  const context = contextFor(cooperation, { kind: 'lead', seedCommit });
  const continuation = JSON.parse(context.message.split(
    'Proof continuation (stored evidence, not replayed; planned use and actual proof use are separate):\n')[1].split('\n\n')[0]);
  expect(continuation.adoptedResearch).toEqual([expect.objectContaining({
    sourceTaskId: source.task.id, taskId: adopted.task.id, recordedProof: 'none', plannedGoalIds: [],
    proofConsumers: [], referenceCoverage: 'unknown',
  })]);
  expect(context.instructions).toContain('continuation.adoptedResearch in COOPERATION.json');
  expect(context.instructions).toContain('does not prove a target or require every exploratory proposal to have a consumer immediately');
  expect(adopted.status).toBe('pending');

  withoutOptionalContext();
  const compact = contextFor(cooperation, { kind: 'lead', seedCommit });
  expect(compact.manifest!.omitted).toContainEqual({ id: 'proof-continuation', kind: 'continuation', reason: 'optional-budget' });
  expect(compact.instructions).toContain('continuation.adoptedResearch in COOPERATION.json');
});

it('gives an early feasibility reviewer complete unproved interfaces even with no optional context budget', () => {
  withoutOptionalContext();
  const { core, probe, goal, cooperation } = fixture();
  const exactType = '∀ (n : Nat), n > 0 → ∃ N : Nat, ∀ m ≥ N, m + n > m';
  core.task = { ...core.task, type: exactType };
  probe.task = { ...probe.task, reviewScope: 'feasibility', dependsOn: [goal.task.id, core.task.id] };
  const context = contextFor(cooperation, actionFor(probe));

  expect(context.workContract).toMatchObject({ stage: 'feasibility-review', owner: 'independent-researcher',
    consumer: 'lead-route-decision', acceptance: 'advisory-only', sourcePolicy: 'read-only' });
  expect(context.manifest).toMatchObject({ maxOptionalBytes: 0, optionalBytes: 0 });
  expect(context.manifest!.requiredTaskIds).toEqual(expect.arrayContaining([probe.task.id, goal.task.id, core.task.id]));
  expect(context.message).toContain(JSON.stringify(exactType));
  expect(context.message).toContain('theorem target : True');
  expect(context.message).toContain('Your role: reviewer');
  expect(context.instructions).toContain('quantifier order, uniform constants, quantitative strength, boundary cases');
  expect(context.instructions).toContain('First test whether the proposed inputs would actually suffice for the consumer');
  expect(core.status).toBe('blocked');
  expect(goal.integratedCheck).toBeUndefined();
});

it.each([10, 100, 500])('keeps local mandatory route focus bounded across %i alternatives', count => {
  withoutOptionalContext();
  const goal = node('goal', 'goal');
  const inputs = Array.from({ length: count }, (_, index) => node(`input_${index}`));
  const closing = inputs.map(input => node(`closing_${input.task.id}`, 'lemma', [input.task.id]));
  const proofRoutes = inputs.map((input, index) => ({ id: `route_${index}`, targetTaskId: goal.task.id,
    prerequisiteTaskIds: [input.task.id], closingTaskId: closing[index].task.id }));
  goal.alternativeRoutes = proofRoutes;
  const active = inputs.at(-1)!;
  closing.at(-1)!.task = { ...closing.at(-1)!.task, type: 'And True True' };
  const cooperation: CooperationState = { canonicalCommit: seedCommit, tasks: [...inputs, ...closing, goal], proofRoutes };
  const context = contextFor(cooperation, actionFor(active)), focus = packet(context.message);
  expect(context.manifest!.mandatoryBytes).toBeLessThan(20 * 1024);
  expect((context.instructions + context.message).match(/Prioritize a ready typed step/g)).toHaveLength(1);
  expect(focus.routePriority).toMatchObject({ selection: 'bounded-preview', totalCount: count, selectedCount: 4,
    omittedCount: count - 4, index: { path: 'COOPERATION.json', field: 'routePriority.routes', count } });
  expect(focus.routePriority.routes[0].routeId).toBe(proofRoutes.at(-1)!.id);
  expect(focus.frontierTaskIds).toContain(active.task.id);
  expect(focus.frontierTaskIds.length).toBeLessThanOrEqual(4);
  expect(focus.frontierSet).toEqual({ count, digest: mathDigest(canonicalMathJson(inputs.map(input => input.task.id))),
    reference: { path: 'COOPERATION.json', field: 'frontierFocus.taskIds' } });
  expect(context.message).toContain('And True True');
  expect(focus.plannedConsumers).toEqual(expect.arrayContaining([goal.task.id, closing.at(-1)!.task.id]));
  expect(context.manifest!.included).toContainEqual(expect.objectContaining({ id: 'consumer-interfaces', required: true }));

  const action = actionFor(goal);
  if (action.kind !== 'task') throw new Error('fixture_assignment');
  action.assignment.routeId = proofRoutes.at(-1)!.id;
  const assigned = packet(contextFor(cooperation, action).message);
  expect(assigned.routePriority.routes[0].routeId).toBe(action.assignment.routeId);
  expect(assigned.routePriority.selectedCount).toBe(5);
});
