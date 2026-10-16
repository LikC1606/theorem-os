import { expect, it } from 'vitest';
import { buildResearchContext } from '../src/solver/modules/context';
import type { SolverProblem } from '../src/solver/problem';
import type { SolverRunState } from '../src/solver/archive';
import type { DeliveryRecord } from '../src/solver/deliveries';
import type { CooperativeTask } from '../src/solver/tasks';
import { taskVersion } from '../src/solver/tasks';
import { setTaskDiagnostic } from '../src/solver/taskDiagnostics';
import type { TaskRecord } from '../src/solver/tasks';
import { buildTaskObligationSummary } from '../src/solver/taskObligations';

it('deduplicates repeated findings and progress while preserving exact Lean types and version references', () => {
  const exactType = '∀ (n : Nat), ' + 'True ∧ '.repeat(2100) + 'True';
  const task: CooperativeTask = { id: 'core', kind: 'lemma', objective: 'Prove the core lemma',
    dependsOn: ['library'], revision: 0, theoremName: 'core', proofPath: 'Submission.lean', type: exactType };
  const problem = { projectRelative: '.', ownedFiles: ['Submission.lean'], declarations: {}, targets: [], receiptDigest: 'problem',
    contract: { formalStatement: 'theorem target : True := by sorry' } } as unknown as SolverProblem;
  const delivery = (kind: DeliveryRecord['kind'], summary: string, id: string): DeliveryRecord => ({
    id, kind, taskId: 'library', taskDigest: 'fixed-task-version', producer: 'researcher', status: 'advisory',
    statement: '', premises: [], dependencies: [], remainingObligations: ['core'], summary, evidenceRefs: [], createdAt: 1 });
  const finding = 'library-finding: ' + 'long advisory explanation '.repeat(500);
  const state = { cooperation: { tasks: [{ task, status: 'pending', attempts: 0 },
    { task: { id: 'library', kind: 'research', objective: 'Search library', dependsOn: [], revision: 0 },
      status: 'completed', attempts: 1, finding }], deliveries: [delivery('progress', 'obsolete-progress', 'old'),
      delivery('research', finding, 'research'), delivery('progress', 'latest-progress', 'new')] } } as unknown as SolverRunState;
  const context = buildResearchContext(problem, state, { root: '/runtime', worktree: '/proof', environment: {},
    taskText: 'Prove the target', retrievalRoot: '/library', assignment: { kind: 'lead', seedCommit: 'fixed-commit' } });
  expect(context.message).toContain(JSON.stringify(exactType));
  expect(context.message).toContain('fixed-task-version');
  expect(context.message).toContain('latest-progress');
  expect(context.message).not.toContain('obsolete-progress');
  expect(context.message.match(/library-finding:/gu)).toHaveLength(1);
  expect(Buffer.byteLength(context.message)).toBeLessThan(Buffer.byteLength(exactType) + 7000);
  const graph = context.message.split('Lead task graph and host feedback:\n')[1].split('\n\nRoute groups')[0];
  expect(JSON.parse(graph)[0].type).toBe(exactType);
});

it('omits an obsolete successful-task error while exposing a new current failure', () => {
  const task: CooperativeTask = { id: 'bridge', kind: 'lemma', objective: 'Prove the bridge', dependsOn: [], revision: 0,
    theoremName: 'Submission.bridge', proofPath: 'Submission.lean', type: 'True' };
  const node: TaskRecord = { task, status: 'integrated', attempts: 2, feedback: 'OBSOLETE_UNKNOWN_CONSTANT',
    integratedCheck: { passed: true, taskDigest: taskVersion(task) } as TaskRecord['integratedCheck'] };
  const problem = { projectRelative: '.', ownedFiles: ['Submission.lean'], declarations: {}, targets: [], receiptDigest: 'problem',
    contract: { formalStatement: 'theorem target : True := by sorry' } } as unknown as SolverProblem;
  const state = { environmentDigest: 'environment', cooperation: { tasks: [node] } } as unknown as SolverRunState;
  const access = { root: '/runtime', worktree: '/proof', environment: {}, taskText: 'Prove the target', retrievalRoot: '/library',
    assignment: { kind: 'lead' as const, seedCommit: 'fixed-commit' } };
  expect(buildResearchContext(problem, state, access).message).not.toContain('OBSOLETE_UNKNOWN_CONSTANT');
  node.status = 'blocked';
  setTaskDiagnostic(node, 'CURRENT_NEW_FAILURE', state.environmentDigest, undefined, 'new-candidate');
  const message = buildResearchContext(problem, state, access).message;
  expect(message).toContain('CURRENT_NEW_FAILURE');
  expect(message).not.toContain('OBSOLETE_UNKNOWN_CONSTANT');
});

it('provides current version references and advisory premise contracts without implying they are proved', () => {
  const producer: CooperativeTask = { id: 'producer', kind: 'lemma', objective: 'Prove the premise', dependsOn: [], revision: 0,
    theoremName: 'Submission.premise', proofPath: 'Submission.lean', type: 'True' };
  const consumer: CooperativeTask = { id: 'consumer', kind: 'lemma', objective: 'Use the premise', dependsOn: ['producer'], revision: 0,
    theoremName: 'Submission.consumer', proofPath: 'Submission.lean', type: 'True',
    obligations: [{ id: 'needed', type: 'True', source: { kind: 'task', taskId: producer.id, taskDigest: taskVersion(producer) } }] };
  const records: TaskRecord[] = [producer, consumer].map(task => ({ task, status: 'pending', attempts: 0 }));
  const problem = { projectRelative: '.', ownedFiles: ['Submission.lean'], declarations: {}, targets: [], receiptDigest: 'problem',
    contract: { formalStatement: 'theorem target : True := by sorry' } } as unknown as SolverProblem;
  const state = { environmentDigest: 'environment', cooperation: { tasks: records } } as unknown as SolverRunState;
  const context = buildResearchContext(problem, state, { root: '/runtime', worktree: '/proof', environment: {}, taskText: 'Prove',
    retrievalRoot: '/library', assignment: { kind: 'lead', seedCommit: 'commit' } });
  expect(context.message).toContain(taskVersion(producer));
  expect(context.message).toContain(JSON.stringify(buildTaskObligationSummary(records, { environmentDigest: state.environmentDigest })));
  expect(context.message).toContain('awaiting-proof');
  expect(context.message).not.toContain('checked-producer');
  expect(context.instructions).toContain('Metadata is advisory and never closes a dependency');
});
