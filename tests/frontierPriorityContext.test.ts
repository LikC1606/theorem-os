import { afterEach, expect, it, vi } from 'vitest';
import * as contextCompiler from '../src/solver/contextCompiler';
import type { CooperationState } from '../src/solver/cooperation';
import type { SolverRunState } from '../src/solver/archive';
import type { SolverProblem } from '../src/solver/problem';
import { buildResearchContext } from '../src/solver/modules/context';
import { taskVersion, type CooperativeAction, type TaskRecord } from '../src/solver/tasks';

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

afterEach(() => vi.restoreAllMocks());

it('retains the assigned support task, its actual consumer and open frontier without optional hints', () => {
  const compile = contextCompiler.compileTaskContext;
  vi.spyOn(contextCompiler, 'compileTaskContext').mockImplementation(input => compile({ ...input, maxOptionalContextBytes: 0 }));
  const { seed, cooperation } = fixture();
  const context = contextFor(cooperation, actionFor(seed));

  expect(context.manifest).toMatchObject({ maxOptionalBytes: 0, optionalBytes: 0 });
  expect(context.manifest!.included).toContainEqual(expect.objectContaining({ id: 'frontier-focus', required: true }));
  expect(context.manifest!.omitted).toContainEqual({ id: 'proof-continuation', kind: 'continuation', reason: 'optional-budget' });
  expect(packet(context.message)).toEqual({ goalTaskIds: ['private_original_goal'], frontierTaskIds: ['core'],
    assignedTaskId: 'seed', relationship: 'frontier-support', plannedConsumers: ['collar'] });
  expect(context.manifest!.requiredTaskIds).toContain('seed');
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

it('gives an early feasibility reviewer complete unproved interfaces even with no optional context budget', () => {
  const compile = contextCompiler.compileTaskContext;
  vi.spyOn(contextCompiler, 'compileTaskContext').mockImplementation(input => compile({ ...input, maxOptionalContextBytes: 0 }));
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
