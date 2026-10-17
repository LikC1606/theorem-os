import { describe, expect, it } from 'vitest';
import type { SolverProblem } from '../src/solver/problem';
import { taskVersion, type CooperativeTask } from '../src/solver/tasks';
import { validateLemmaRequests } from '../src/solver/taskProposals';

const problem = {
  ownedFiles: ['Submission.lean'],
  targets: [{ theoremName: 'Submission.goal', proofPath: 'Submission.lean' }],
  declarations: { 'Submission.lean': [{ name: 'goal', header: 'goal : True' }] },
} as unknown as SolverProblem;
const groups = [{ id: 'main', objective: 'Prove the original problem', status: 'active' as const, revision: 0 }];
const research: CooperativeTask = { id: 'explore', kind: 'research', objective: 'Find a usable bridge', dependsOn: [], revision: 0 };
const goal: CooperativeTask = { id: 'goal', kind: 'goal', theoremName: 'Submission.goal', proofPath: 'Submission.lean',
  objective: 'Prove the original goal', dependsOn: [], revision: 0 };
const request = { id: 'bridge', kind: 'lemma', objective: 'Prove the exact bridge consumed by the goal',
  theoremName: 'Submission.bridge', type: '∀ (P : Prop), P → P', dependsOn: [] };

describe('research to typed proof proposals', () => {
  it('validates a new closed target without adopting it or changing accepted tasks', () => {
    const tasks = [research, goal], versions = tasks.map(taskVersion);
    expect(validateLemmaRequests(problem, tasks, groups, research, [request])).toEqual([
      { ...request, proofPath: 'Submission.lean', revision: 0, groupId: 'main' },
    ]);
    expect(tasks).toEqual([research, goal]);
    expect(tasks.map(taskVersion)).toEqual(versions);
    expect(validateLemmaRequests(problem, tasks, groups, research, undefined)).toEqual([]);
  });

  it.each([
    { ...request, id: 'goal' },
    { ...request, theoremName: 'Submission.goal' },
    { ...request, proofPath: '../Solution.lean' },
    { ...request, type: 'FULL_CLOSED_LEAN_TYPE' },
    { ...request, groupId: 'other' },
    { ...request, dependsOn: ['missing'] },
    { ...request, dependsOn: ['bridge'] },
    { ...request, kind: 'research' },
  ])('rejects a conflicting, incomplete, cyclic or out-of-scope request: %j', invalid => {
    expect(() => validateLemmaRequests(problem, [research, goal], groups, research, [invalid]))
      .toThrow('math_research_lemma_requests_invalid');
  });
});
