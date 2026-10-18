import { expect, it } from 'vitest';
import { buildResearchContext } from '../src/solver/modules/context';
import type { SolverProblem } from '../src/solver/problem';
import type { SolverRunState } from '../src/solver/archive';
import type { DeliveryRecord } from '../src/solver/deliveries';
import { taskVersion, type CooperativeTask } from '../src/solver/tasks';

it('deduplicates repeated findings and progress while preserving exact Lean types and version references', () => {
  const exactType = '∀ (n : Nat), ' + 'True ∧ '.repeat(2100) + 'True';
  const task: CooperativeTask = { id: 'core', kind: 'lemma', objective: 'Prove the core lemma',
    dependsOn: ['library'], revision: 0, theoremName: 'core', proofPath: 'Submission.lean', type: exactType };
  const library: CooperativeTask = { id: 'library', kind: 'research', objective: 'Search library', dependsOn: [], revision: 0 };
  const problem = { projectRelative: '.', ownedFiles: ['Submission.lean'], declarations: {}, targets: [], receiptDigest: 'problem',
    baseCommit: 'fixed-commit', contract: { formalStatement: 'theorem target : True := by sorry', assumptions: [] } } as unknown as SolverProblem;
  const delivery = (kind: DeliveryRecord['kind'], summary: string, id: string): DeliveryRecord => ({
    id, kind, taskId: 'library', taskDigest: taskVersion(library), producer: 'researcher', status: 'advisory',
    statement: '', premises: [], dependencies: [], remainingObligations: ['core'], summary, evidenceRefs: [], createdAt: 1 });
  const finding = 'library-finding: ' + 'long advisory explanation '.repeat(500);
  const state = { cooperation: { tasks: [{ task, status: 'pending', attempts: 0 },
    { task: library,
      status: 'completed', attempts: 1, finding }], deliveries: [delivery('progress', 'obsolete-progress', 'old'),
      delivery('research', finding, 'research'), delivery('progress', 'latest-progress', 'new')] } } as unknown as SolverRunState;
  const context = buildResearchContext(problem, state, { root: '/runtime', worktree: '/proof', environment: {},
    taskText: 'Prove the target', retrievalRoot: '/library', frozenContexts: { 'Submission.lean': 'theorem target : True := /- body omitted -/' },
    assignment: { kind: 'lead', seedCommit: 'fixed-commit' } });
  expect(context.message).toContain(JSON.stringify(exactType));
  expect(context.message).toContain(taskVersion(library));
  expect(context.message).toContain('latest-progress');
  expect(context.message).not.toContain('obsolete-progress');
  expect(context.message.match(/library-finding:/gu)).toHaveLength(1);
  expect(context.message).toContain(finding);
  expect(context.manifest!.usedBytes).toBeLessThanOrEqual(context.manifest!.maxBytes);
  const graph = context.message.split('Lead task graph and host feedback:\n')[1].split('\n\nRoute groups')[0];
  expect(JSON.parse(graph)[0].type).toBe(exactType);
});
