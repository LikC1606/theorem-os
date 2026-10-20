import { afterEach, expect, it, vi } from 'vitest';
import * as contextCompiler from '../src/solver/contextCompiler';
import { CooperativeResearch, type CooperationState } from '../src/solver/cooperation';
import { buildResearchContext } from '../src/solver/modules/context';
import type { ResearchWorker } from '../src/solver/modules/organization';
import type { SolverRunState } from '../src/solver/archive';
import type { SolverProblem } from '../src/solver/problem';
import { taskVersion, type CooperativeAction, type TaskRecord } from '../src/solver/tasks';
import { cooperativeResearch } from './helpers/cooperation';

const baseCommit = 'a'.repeat(40), seedCommit = 'b'.repeat(40);
const formal = 'namespace Original\ntheorem target : True := by sorry\nend Original';
const problem = {
  projectRelative: 'generated/p', ownedFiles: ['Submission.lean'],
  declarations: { 'Submission.lean': [{ name: 'target', header: 'target : True' }] },
  sourceImports: { 'Submission.lean': ['Mathlib.Data.Nat.Basic'] },
  sourceStructure: { 'Submission.lean': 'frozen-context' },
  targets: [{ proofPath: 'Submission.lean', theoremName: 'Original.target', declarationHash: 'original-type' }],
  receiptDigest: 'problem-receipt', baseCommit,
  contract: { formalStatement: formal, informalStatement: 'Prove the original proposition.', assumptions: [],
    statementHash: 'statement', leanStatementHash: 'lean-statement' },
} as unknown as SolverProblem;
const node = (id: string, dependsOn: string[] = []): TaskRecord => ({
  task: { id, kind: 'lemma', objective: `Prove ${id}`, theoremName: `Original.${id}`,
    type: 'True', proofPath: 'Submission.lean', revision: 0, dependsOn },
  status: 'pending', attempts: 0,
});
const fixture = () => {
  const failed = node('failed_construction');
  failed.status = 'blocked'; failed.attempts = 2;
  failed.feedback = 'math_task_missing_declaration: the assigned exterior witness is absent.';
  failed.assignment = { taskId: failed.task.id, taskDigest: taskVersion(failed.task),
    workerId: 'researcher', seedCommit };
  const prerequisite = node('unattempted_collar'); prerequisite.status = 'blocked';
  const supporting = node('ambient_extension', [prerequisite.task.id]);
  const paused = node('paused_premise'); paused.status = 'blocked';
  paused.task = { ...paused.task, status: 'paused' };
  const goal = node('original_goal', [failed.task.id]);
  goal.task = { ...goal.task, kind: 'goal', theoremName: 'Original.target' };
  const recovery = { id: 'private-global-frontier-recovery', taskIds: [failed.task.id], goalIds: [goal.task.id] };
  const action = { kind: 'lead' as const, seedCommit, recovery } satisfies CooperativeAction;
  const cooperation: CooperationState = { canonicalCommit: seedCommit,
    tasks: [failed, prerequisite, supporting, paused, goal],
    frontierRecoveries: [{ ...recovery, status: 'requested', taskInputDigests: ['private-global-recovery-input'] }],
  };
  const state = { environmentDigest: 'environment', problem, cooperation } as SolverRunState;
  return { failed, prerequisite, supporting, paused, action, cooperation, state };
};
const access = (assignment: CooperativeAction) => ({
  root: '/runtime', worktree: '/proof', environment: {}, taskText: 'Prove the original target.',
  retrievalRoot: '/library', assignment,
  frozenContexts: { 'Submission.lean': contextCompiler.frozenSourceContext(problem, 'Submission.lean', formal) },
});

afterEach(() => vi.restoreAllMocks());

it('keeps the M4 recovery packet mandatory with no optional budget, including failure inputs and unattempted prerequisites', () => {
  const compile = contextCompiler.compileTaskContext;
  vi.spyOn(contextCompiler, 'compileTaskContext').mockImplementation(input =>
    compile({ ...input, maxOptionalContextBytes: 0 }));
  const { failed, prerequisite, supporting, paused, action, state } = fixture();
  const context = buildResearchContext(problem, state, access(action));

  expect(context.manifest).toMatchObject({ maxOptionalBytes: 0, optionalBytes: 0 });
  expect(context.manifest!.included).toContainEqual(expect.objectContaining({ id: 'frontier-recovery', required: true }));
  expect(context.manifest!.omitted).toContainEqual({ id: 'proof-continuation', kind: 'continuation', reason: 'optional-budget' });
  const prefix = 'Targeted recovery request (advisory; no proof acceptance):\n';
  const encoded = context.message.split(prefix)[1];
  expect(encoded).toBeDefined();
  const packet = JSON.parse(encoded.split('\n\n')[0]);
  expect(packet).toMatchObject({ ...action.recovery, failures: [{ taskId: failed.task.id, status: 'blocked', attempts: 2,
    feedback: failed.feedback, assignment: { workerId: 'researcher', seedCommit } }] });
  expect(packet.unattemptedSupportingTasks).toContainEqual({ taskId: prerequisite.task.id, status: 'blocked', dependsOn: [] });
  expect(packet.unattemptedSupportingTasks).toContainEqual({ taskId: supporting.task.id, status: 'pending', dependsOn: [prerequisite.task.id] });
  expect(packet.unattemptedSupportingTasks.map((item: { taskId: string }) => item.taskId)).not.toContain(paused.task.id);
  expect(packet.unattemptedSupportingTasks.map((item: { taskId: string }) => item.taskId)).not.toContain(failed.task.id);
});

it('withholds global frontier recovery records from a scoped task worker and its M4 context', () => {
  const { failed, action: leadAction, cooperation, state } = fixture();
  const lead: ResearchWorker = { id: 'solver', role: 'lead', worktree: '/proof', ownedFiles: ['Submission.lean'] };
  const researcher: ResearchWorker = { ...lead, id: 'researcher', role: 'researcher' };
  vi.spyOn(CooperativeResearch.prototype as any, 'planningInputDigest').mockReturnValue('fixture-planning-input');
  const cooperative = cooperativeResearch({ state, workers: [lead, researcher], retrievalRoot: '', access: new Map() });
  const assignment: Extract<CooperativeAction, { kind: 'task' }> = {
    kind: 'task', task: failed.task, assignment: failed.assignment!,
  };

  expect(cooperative.contextState(leadAction, lead).frontierRecoveries).toEqual(cooperation.frontierRecoveries);
  const scoped = cooperative.contextState(assignment, researcher);
  expect(scoped.frontierRecoveries).toBeUndefined();
  expect(cooperation.frontierRecoveries).toHaveLength(1);
  expect(JSON.stringify(scoped)).not.toContain('private-global-frontier-recovery');
  expect(JSON.stringify(scoped)).not.toContain('private-global-recovery-input');
  const context = buildResearchContext(problem, { ...state, cooperation: scoped }, access(assignment));
  expect(context.manifest!.included.some(item => item.id === 'frontier-recovery')).toBe(false);
  expect(context.message).not.toContain('private-global-frontier-recovery');
  expect(context.message).not.toContain('private-global-recovery-input');
});
