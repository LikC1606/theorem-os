import { expect, it } from 'vitest';
import { compileTaskContext, frozenSourceContext, type TaskContextInput } from '../src/solver/contextCompiler';
import { CooperativeResearch, type CooperationState } from '../src/solver/cooperation';
import { directSolverModules } from '../src/solver/modules';
import { buildResearchContext } from '../src/solver/modules/context';
import { cooperativeWorkContract } from '../src/solver/modules/contracts';
import type { ResearchWorker } from '../src/solver/modules/organization';
import type { SolverRunState } from '../src/solver/archive';
import type { SolverProblem } from '../src/solver/problem';
import type { ProofRoute } from '../src/solver/proofRoutes';
import { contextTaskConsumers, taskConsumerInterfaces, taskConsumerProjection } from '../src/solver/taskConsumers';
import { taskVersion, type CooperativeAction, type CooperativeTask, type TaskRecord } from '../src/solver/tasks';

const seedCommit = 'a'.repeat(40);
const formal = 'namespace Original\nvariable (n : Nat)\ntheorem target (h : n > 0) : n > 0 := by sorry\nend Original';
const frozenHeader = 'target (h : n > 0) : n > 0';
const problem = {
  projectRelative: 'generated/p', ownedFiles: ['Submission.lean'],
  declarations: { 'Submission.lean': [{ name: 'target', header: frozenHeader }] },
  sourceImports: { 'Submission.lean': ['Mathlib.Data.Nat.Basic'] },
  sourceStructure: { 'Submission.lean': 'frozen-context' },
  targets: [{ proofPath: 'Submission.lean', theoremName: 'Original.target', declarationHash: 'original-type' }],
  receiptDigest: 'problem-receipt', baseCommit: seedCommit,
  contract: { formalStatement: formal, informalStatement: 'Positive n remains positive.', assumptions: ['n is natural', 'n > 0'],
    statementHash: 'statement', leanStatementHash: 'lean-statement' },
} as unknown as SolverProblem;
const node = (id: string, dependsOn: readonly string[] = [], overrides: Partial<CooperativeTask> = {}): TaskRecord => ({
  task: { id, kind: 'lemma', objective: `Prove ${id}`, theoremName: `Original.${id}`,
    type: 'True', proofPath: 'Submission.lean', revision: 0, dependsOn, ...overrides },
  status: 'pending', attempts: 0,
});
const goal = (id: string, overrides: Partial<CooperativeTask> = {}) => node(id, [], {
  kind: 'goal', theoremName: 'Original.target', ...overrides,
});
const actionFor = (active: TaskRecord): Extract<CooperativeAction, { kind: 'task' }> => ({
  kind: 'task', task: active.task,
  assignment: { taskId: active.task.id, taskDigest: taskVersion(active.task), workerId: 'researcher', seedCommit },
});
const inputFor = (active: TaskRecord, cooperation: CooperationState): TaskContextInput => ({
  problem, cooperation, action: actionFor(active), instructions: 'Preserve exact proof obligations.',
  taskText: 'Prove the original target.', maxOptionalContextBytes: 0,
  frozenContexts: { 'Submission.lean': frozenSourceContext(problem, 'Submission.lean', formal) },
});
const consumerRows = (message: string): Array<Record<string, any>> => {
  for (const line of message.split('\n')) {
    try {
      const value: unknown = JSON.parse(line);
      if (Array.isArray(value) && value.length && value.every(item => Array.isArray(item.uses))) return value;
    } catch { /* Section labels and prose are not JSON. */ }
  }
  throw new Error('Missing complete consumer interface array');
};

it('selects direct consumers using their own sharing policy without following reverse transitive edges', () => {
  const active = node('helper', [], { groupId: 'main', sharing: 'problem' });
  const local = node('local', ['helper'], { sharing: 'group' });
  const shared = node('shared', ['helper'], { groupId: 'other', sharing: 'problem' });
  const privateConsumer = node('private', ['helper'], { groupId: 'other', sharing: 'group' });
  const later = node('later', ['local']);
  const unrelated = node('unrelated');
  const interfaces = taskConsumerInterfaces(active.task, [active, local, shared, privateConsumer, later, unrelated]);

  expect(interfaces.map(item => item.task.id)).toEqual(['local', 'shared']);
  expect(interfaces.every(item => item.status === 'pending')).toBe(true);
  expect(interfaces.map(item => item.uses)).toEqual([[{ kind: 'dependency' }], [{ kind: 'dependency' }]]);
  expect(taskConsumerInterfaces(active.task, [active])).toEqual([]);
});

it('merges global and legacy route uses without duplicating the same route relationship', () => {
  const prerequisite = node('prerequisite'), closing = node('closing', ['prerequisite']);
  const target = goal('original_goal');
  const route: ProofRoute = { id: 'main_route', targetTaskId: target.task.id,
    prerequisiteTaskIds: [prerequisite.task.id], closingTaskId: closing.task.id };
  target.alternativeRoutes = [route];
  const tasks = [prerequisite, closing, target];

  const forPrerequisite = taskConsumerInterfaces(prerequisite.task, tasks, [route]);
  expect(forPrerequisite.find(item => item.task.id === closing.task.id)?.uses).toEqual([{ kind: 'dependency' }]);
  expect(forPrerequisite.find(item => item.task.id === target.task.id)?.uses)
    .toEqual([{ kind: 'route-prerequisite', routeId: route.id }]);
  expect(taskConsumerInterfaces(closing.task, tasks, [route]).find(item => item.task.id === target.task.id)?.uses)
    .toEqual([{ kind: 'route-closing', routeId: route.id }]);
});

it('supports global-only routes and restored node-local routes', () => {
  const closing = node('closing'), target = goal('original_goal');
  const route: ProofRoute = { id: 'closing_route', targetTaskId: target.task.id,
    prerequisiteTaskIds: [], closingTaskId: closing.task.id };
  const globalOnly = taskConsumerInterfaces(closing.task, [closing, target], [route]);
  expect(globalOnly).toHaveLength(1);
  expect(globalOnly[0].uses).toEqual([{ kind: 'route-closing', routeId: route.id }]);

  target.alternativeRoutes = [route];
  expect(taskConsumerInterfaces(closing.task, [closing, target])).toEqual(globalOnly);
});

it('does not reveal a cross-group private route target through a public closing lemma', () => {
  const closing = node('closing', [], { sharing: 'problem' });
  const target = goal('private_goal', { groupId: 'other', sharing: 'group', objective: 'PRIVATE_CONSUMER_OBJECTIVE' });
  const route: ProofRoute = { id: 'private_route', targetTaskId: target.task.id,
    prerequisiteTaskIds: [], closingTaskId: closing.task.id };
  target.alternativeRoutes = [route];
  expect(taskConsumerInterfaces(closing.task, [closing, target], [route])).toEqual([]);
});

it('binds the current consumer contract and never includes its proof, findings or host acceptance', () => {
  const active = node('helper'), consumer = node('consumer', ['helper']);
  consumer.status = 'running';
  consumer.finding = 'NONCONTRACT_RESEARCH';
  consumer.proof = { passed: true, commit: 'NONCONTRACT_PROOF_COMMIT' } as TaskRecord['proof'];
  const original = structuredClone(consumer);
  const first = taskConsumerInterfaces(active.task, [active, consumer])[0];

  expect(first.taskDigest).toBe(taskVersion(consumer.task));
  expect(first.status).toBe('running');
  expect(first).not.toHaveProperty('proof');
  expect(first).not.toHaveProperty('finding');
  expect(first).not.toHaveProperty('integratedCheck');
  expect(JSON.stringify(first)).not.toContain('NONCONTRACT_');
  expect(consumer).toEqual(original);

  consumer.task = { ...consumer.task, revision: 1, type: '\u2200 n : Nat, n = n' };
  const revised = taskConsumerInterfaces(active.task, [active, consumer])[0];
  expect(revised.taskDigest).toBe(taskVersion(consumer.task));
  expect(revised.taskDigest).not.toBe(first.taskDigest);
  expect(revised.task.type).toBe(consumer.task.type);
});

it('keeps a complete long consumer type, assumptions and intended inference mandatory with zero optional bytes', () => {
  const active = node('helper');
  const exactType = '\u2200 (n : Nat) (h : n > 0), ' + 'n = n \u2227 '.repeat(2500) + 'n > 0';
  const consumer = node('consumer', ['helper', 'private_sibling'], {
    type: exactType, premises: ['CONSUMER_EXACT_ASSUMPTION'],
    objective: 'Apply helper to the exact missing estimate before closing the original target.',
  });
  const consumerInterfaces = taskConsumerProjection(active.task, [active, consumer]);
  const context = compileTaskContext(inputFor(active, { tasks: [active], consumerInterfaces }));
  const rows = consumerRows(context.message);

  expect(rows).toEqual([{ ...consumer.task, taskDigest: taskVersion(consumer.task), status: 'pending', uses: [{ kind: 'dependency' }] }]);
  expect(rows[0].type).toBe(exactType);
  expect(context.manifest).toMatchObject({ maxOptionalBytes: 0, optionalBytes: 0, requiredTaskIds: ['helper'] });
  expect(context.manifest.included).toContainEqual(expect.objectContaining({ id: 'consumer-interfaces', required: true }));
  expect(context.manifest.requiredTaskIds).not.toContain('consumer');
  expect(context.manifest.requiredTaskIds).not.toContain('private_sibling');
});

it('derives visible consumer interfaces when no host-scoped projection was supplied', () => {
  const active = node('helper'), consumer = node('consumer', ['helper', 'unavailable_sibling']);
  const context = compileTaskContext(inputFor(active, { tasks: [active, consumer] }));

  expect(consumerRows(context.message).map(item => item.id)).toEqual(['consumer']);
  expect(context.manifest.requiredTaskIds).toEqual(['helper']);
});

it('supplies the frozen original header for a goal consuming a route closing lemma', () => {
  const active = node('closing'), target = goal('original_goal');
  const route: ProofRoute = { id: 'original_route', targetTaskId: target.task.id,
    prerequisiteTaskIds: [], closingTaskId: active.task.id };
  const consumerInterfaces = taskConsumerProjection(active.task, [active, target], [route]);
  const context = compileTaskContext(inputFor(active, { tasks: [active], consumerInterfaces }));

  expect(consumerRows(context.message)).toEqual([{ ...target.task, taskDigest: taskVersion(target.task), status: 'pending',
    uses: [{ kind: 'route-closing', routeId: route.id }], exactFrozenHeader: frozenHeader }]);
  expect(context.manifest.requiredTaskIds).toEqual(['closing']);
});

it('rejects a stale consumer contract before dispatch instead of showing an unbound type', () => {
  const active = node('helper'), consumer = node('consumer', ['helper']);
  const projection = taskConsumerProjection(active.task, [active, consumer]);
  const consumerInterfaces = { ...projection,
    interfaces: projection.interfaces.map(item => ({ ...item, taskDigest: 'stale-consumer-version' })) };
  expect(() => compileTaskContext(inputFor(active, { tasks: [active], consumerInterfaces })))
    .toThrow('math_context_stale_required');
});

it('uses the same global-only route consumer for the work contract and mathematical focus packet', () => {
  const active = node('closing'), target = goal('original_goal');
  const route: ProofRoute = { id: 'original_route', targetTaskId: target.task.id,
    prerequisiteTaskIds: [], closingTaskId: active.task.id };
  const consumerInterfaces = taskConsumerProjection(active.task, [active, target], [route]);
  const cooperation: CooperationState = { tasks: [active], consumerInterfaces };
  const action = actionFor(active);
  expect(cooperativeWorkContract(action, cooperation.tasks, cooperation).plannedConsumers).toEqual([target.task.id]);
  const context = buildResearchContext(problem, { problem, cooperation, environmentDigest: 'environment' } as SolverRunState, {
    root: '/runtime', worktree: '/proof', environment: {}, taskText: 'Prove the original target.',
    retrievalRoot: '/library', assignment: action, frozenContexts: inputFor(active, cooperation).frozenContexts,
  });
  const focus = JSON.parse(context.message.split('Original-goal focus (advisory, not proof acceptance):\n')[1].split('\n\n')[0]);

  expect(context.workContract?.plannedConsumers).toEqual([target.task.id]);
  expect(focus.plannedConsumers).toEqual([target.task.id]);
  expect(consumerRows(context.message)[0].id).toBe(target.task.id);
});

it('exposes public pending consumer contracts through a context-only bypass without expanding visible tasks', () => {
  const active = node('helper', [], { groupId: 'main', sharing: 'problem' });
  const shared = node('public_consumer', ['helper', 'private_sibling'], { groupId: 'other', sharing: 'problem' });
  const privateSibling = node('private_sibling', [], { groupId: 'other', sharing: 'group', objective: 'PRIVATE_SIBLING_MATHEMATICS' });
  const privateConsumer = node('private_consumer', ['helper'], { groupId: 'other', sharing: 'group', objective: 'PRIVATE_CONSUMER_MATHEMATICS' });
  const cooperation: CooperationState = { canonicalCommit: seedCommit, tasks: [active, shared, privateSibling, privateConsumer] };
  const state = { environmentDigest: 'environment', problem, cooperation } as SolverRunState;
  const lead: ResearchWorker = { id: 'solver', role: 'lead', worktree: '/proof', ownedFiles: ['Submission.lean'] };
  const researcher: ResearchWorker = { ...lead, id: 'researcher', role: 'researcher' };
  const cooperative = new CooperativeResearch({ state, workers: [lead, researcher], access: new Map(),
    signal: new AbortController().signal, save: () => {}, emit: () => {}, modules: directSolverModules,
    exclusiveCheck: async check => check() });
  const scoped = cooperative.contextState(actionFor(active), researcher);

  expect(scoped.tasks.map(item => item.task.id)).toEqual([active.task.id]);
  expect(scoped.consumerInterfaces).toMatchObject({ taskId: active.task.id, taskDigest: taskVersion(active.task) });
  expect(scoped.consumerInterfaces?.interfaces.map(item => item.task.id)).toEqual([shared.task.id]);
  expect(cooperation).not.toHaveProperty('consumerInterfaces');
  expect(JSON.stringify(scoped)).not.toContain('PRIVATE_SIBLING_MATHEMATICS');
  expect(JSON.stringify(scoped)).not.toContain('PRIVATE_CONSUMER_MATHEMATICS');
  const context = compileTaskContext(inputFor(active, scoped));
  expect(consumerRows(context.message)[0].id).toBe(shared.task.id);
  expect(context.manifest.requiredTaskIds).toEqual([active.task.id]);
});

it('rejects a valid consumer projection reused for another same-group assignment', () => {
  const earlier = node('earlier_helper'), current = node('current_helper');
  const earlierConsumer = node('earlier_consumer', [earlier.task.id]);
  const currentConsumer = node('current_consumer', [current.task.id]);
  const consumerInterfaces = taskConsumerProjection(earlier.task, [earlier, earlierConsumer]);
  const cooperation: CooperationState = { tasks: [current, currentConsumer], consumerInterfaces };

  expect(() => compileTaskContext(inputFor(current, cooperation)))
    .toThrow(`math_context_stale_required:consumer-assignment:${current.task.id}`);
  expect(() => cooperativeWorkContract(actionFor(current), cooperation.tasks, cooperation))
    .toThrow(`math_context_stale_required:consumer-assignment:${current.task.id}`);
});

it('rejects a projection after the assigned mathematical type changes under the same task id', () => {
  const earlier = node('helper'), consumer = node('consumer', [earlier.task.id]);
  const consumerInterfaces = taskConsumerProjection(earlier.task, [earlier, consumer]);
  const current: TaskRecord = { ...earlier, task: { ...earlier.task, type: '\u2200 n : Nat, n = n' } };

  expect(() => compileTaskContext(inputFor(current, { tasks: [current], consumerInterfaces })))
    .toThrow(`math_context_stale_required:consumer-assignment:${current.task.id}`);
});

it.each(['taskId', 'taskDigest'] as const)('rejects an empty projection with a mismatched %s instead of hiding current consumers', mismatched => {
  const active = node('helper'), consumer = node('consumer', [active.task.id]);
  const empty = taskConsumerProjection(active.task, [active]);
  const consumerInterfaces = { ...empty, [mismatched]: 'another-assignment' };

  expect(consumerInterfaces.interfaces).toEqual([]);
  expect(() => contextTaskConsumers(active.task, [active, consumer], { consumerInterfaces }))
    .toThrow(`math_context_stale_required:consumer-assignment:${active.task.id}`);
  expect(() => compileTaskContext(inputFor(active, { tasks: [active, consumer], consumerInterfaces })))
    .toThrow(`math_context_stale_required:consumer-assignment:${active.task.id}`);
});

it('preserves correctly bound consumer interfaces after JSON serialization and restoration', () => {
  const active = node('helper'), consumer = node('consumer', [active.task.id, 'private_sibling']);
  const projection = taskConsumerProjection(active.task, [active, consumer]);
  const restored = JSON.parse(JSON.stringify(projection)) as typeof projection;
  const cooperation: CooperationState = { tasks: [active], consumerInterfaces: restored };
  const context = compileTaskContext(inputFor(active, cooperation));

  expect(restored).toEqual(projection);
  expect(consumerRows(context.message)).toEqual([{ ...consumer.task, taskDigest: taskVersion(consumer.task), status: 'pending', uses: [{ kind: 'dependency' }] }]);
  expect(context.manifest.requiredTaskIds).toEqual([active.task.id]);
  expect(cooperativeWorkContract(actionFor(active), cooperation.tasks, cooperation).plannedConsumers).toEqual([consumer.task.id]);
});

it('does not import a saved task projection into a fixed candidate review action', () => {
  const active = node('helper'), earlier = node('earlier_helper');
  const consumer = node('private_consumer', [earlier.task.id], { objective: 'UNRELATED_SAVED_CONSUMER_ARGUMENT' });
  const consumerInterfaces = taskConsumerProjection(earlier.task, [earlier, consumer]);
  const input = inputFor(active, { tasks: [active], consumerInterfaces });
  const context = compileTaskContext({ ...input, action: { kind: 'review', seedCommit, sourceDigest: 'fixed-candidate' } });

  expect(context.manifest.included.some(section => section.id === 'consumer-interfaces')).toBe(false);
  expect(context.message).not.toContain('UNRELATED_SAVED_CONSUMER_ARGUMENT');
});
