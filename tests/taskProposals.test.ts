import { describe, expect, it } from 'vitest';
import type { SolverProblem } from '../src/solver/problem';
import { parseCooperationPlan, taskVersion, type TaskRecord } from '../src/solver/tasks';
import { proposeResearchLemmas, researchLemmaProposalSummary } from '../src/solver/taskProposals';

const problem = { ownedFiles: ['Submission.lean'], targets: [{ proofPath: 'Submission.lean', theoremName: 'Submission.target' }],
  declarations: { 'Submission.lean': [{ name: 'Submission.target' }] } } as unknown as SolverProblem;
function fixture() {
  const plan = parseCooperationPlan(problem, { groups: [{ id: 'private', objective: 'Investigate this route' }], tasks: [
    { id: 'research', kind: 'research', objective: 'Find an exact bridge', groupId: 'private', sharing: 'group' },
    { id: 'target', kind: 'goal', objective: 'Prove the original', theoremName: 'Submission.target', groupId: 'private' },
  ] });
  const records: TaskRecord[] = plan.tasks.map(task => ({ task, status: 'pending', attempts: 0 }));
  const task = records[0].task;
  const source = { task, assignment: { taskId: task.id, taskDigest: taskVersion(task), workerId: 'researcher', seedCommit: 'a'.repeat(40) } };
  const request = { id: 'bridge', kind: 'lemma', objective: 'Prove the discovered bridge', theoremName: 'Submission.bridge',
    type: '∀ (n : Nat), n = n', dependsOn: ['research'] };
  const propose = (requests: unknown = [request]) => proposeResearchLemmas(problem, records, plan.groups, source, 'researcher', 'b'.repeat(40), requests);
  return { ...plan, records, source, request, propose };
}

describe('research to typed task proposals', () => {
  it('keeps an exact validated contract advisory and leaves the active graph unchanged', () => {
    const f = fixture(), before = JSON.stringify(f.records);
    const proposal = f.propose()!;
    expect(proposal.tasks).toHaveLength(1);
    expect(proposal.tasks[0]).toMatchObject({ id: 'bridge', kind: 'lemma', type: f.request.type,
      groupId: 'private', sharing: 'group', proofPath: 'Submission.lean' });
    expect(proposal.source).toMatchObject({ taskId: 'research', taskDigest: f.source.assignment.taskDigest, commit: 'b'.repeat(40) });
    expect(JSON.stringify(f.records)).toBe(before);
    expect(researchLemmaProposalSummary([proposal], f.records)[0]).toMatchObject({ evidence: 'advisory-proposal', status: 'proposed' });
  });

  it.each([
    { id: 'research' }, { kind: 'goal' }, { groupId: 'other' }, { sharing: 'problem' }, { ownerId: 'lead' },
    { type: 'FULL_CLOSED_LEAN_TYPE' }, { dependsOn: ['missing'] }, { dependsOn: ['bridge'] },
  ])('rejects an invalid or out of scope contract %j', change => {
    const f = fixture();
    expect(() => f.propose([{ ...f.request, ...change }])).toThrow(/math_(?:research_lemma_proposal|plan_)/u);
    expect(f.records).toHaveLength(2);
  });

  it('rejects a proposal from a changed source version', () => {
    const f = fixture(); f.source.assignment.taskDigest = '0'.repeat(64);
    expect(() => f.propose()).toThrow('math_research_lemma_proposal_source_changed');
  });

  it('tracks adoption as task graph state without claiming proof acceptance', () => {
    const f = fixture(), proposal = f.propose()!;
    f.records.push({ task: proposal.tasks[0], status: 'pending', attempts: 0 });
    expect(researchLemmaProposalSummary([proposal], f.records)[0].status).toBe('adopted');
    f.records[2].task = { ...f.records[2].task, revision: 1 };
    expect(researchLemmaProposalSummary([proposal], f.records)[0].status).toBe('stale');
    expect(f.records[2].status).toBe('pending');
  });

  it('invalidates proposals when the research inputs change', () => {
    const f = fixture(), proposal = f.propose()!;
    f.records[0].task = { ...f.records[0].task, revision: 1 };
    expect(researchLemmaProposalSummary([proposal], f.records)[0].status).toBe('stale');
  });
});
