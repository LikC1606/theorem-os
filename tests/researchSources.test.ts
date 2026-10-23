import { describe, expect, it } from 'vitest';
import type { SolverProblem } from '../src/solver/problem';
import type { TaskProof } from '../src/solver/cooperativeProof';
import { researchSourceTasks, scopedResearchSources } from '../src/solver/researchSources';
import { researchSourceDigest } from '../src/solver/researchRecords';
import { taskVersion, type CooperativeTask, type TaskRecord } from '../src/solver/tasks';

const current: CooperativeTask = { id: 'route_question', kind: 'research', objective: 'Find the missing route',
  dependsOn: [], revision: 0, groupId: 'current' };
const lemma = (id: string, groupId: string, sharing: 'group' | 'problem' = 'group', dependsOn: readonly string[] = []): CooperativeTask => ({
  id, groupId, sharing, dependsOn, kind: 'lemma', objective: `Prove ${id}`, revision: 0,
  theoremName: `Fixture.${id}`, proofPath: 'Helpers.lean', type: 'True' });
const node = (task: CooperativeTask, status: TaskRecord['status'] = 'pending'): TaskRecord => ({ task, status, attempts: 0 });
const problem: SolverProblem = {
  kind: 'example', workspace: '/fixture', projectRelative: 'project', baseCommit: 'fixture-seed', receiptDigest: 'fixture-receipt',
  activeProblemPath: '/fixture/active-problem.json', ownedFiles: ['Helpers.lean', 'Submission.lean', 'fixture.json'], trustedFiles: {},
  declarations: { 'Helpers.lean': [], 'Submission.lean': [{ name: 'Fixture.original', header: 'theorem original : True :=', body: 'by sorry' }] },
  sourceStructure: {}, contract: { problemId: 'fixture', informalStatement: 'Prove the original claim',
    formalStatement: 'theorem original : True := by sorry', assumptions: [], knownTraps: [], acceptanceCriteria: [],
    officialVerificationCommand: 'lake test', statementHash: 'fixture-statement', leanStatementHash: 'fixture-formal' },
  targets: [{ proofPath: 'Submission.lean', theoremName: 'Fixture.original', declarationHash: 'fixture-original' }],
};
const sources = (helpers: string): Record<string, string> => ({ 'Helpers.lean': `namespace Fixture\n${helpers}end Fixture\n`,
  'Submission.lean': 'import Helpers\nnamespace Fixture\ntheorem original : True := by sorry\nend Fixture\n', 'fixture.json': '{"frozen":true}\n' });
function freeze<T>(value: T): T {
  if (value && typeof value === 'object') { Object.values(value).forEach(freeze); Object.freeze(value); }
  return value;
}
const project = (task: CooperativeTask | undefined, text: Record<string, string>, tasks: TaskRecord[]) =>
  scopedResearchSources(problem, task, text, researchSourceTasks(tasks));

describe('research source projection', () => {
  it('preserves every same-group helper and the original source', () => {
    const privateHelper = lemma('same_group_helper', 'current'), text = sources('lemma same_group_helper : True := by trivial\n');
    const projected = project(current, text, [node(current), node(privateHelper)]);
    expect(projected).toEqual(text);
    expect(projected['Submission.lean']).toBe(text['Submission.lean']);
  });

  it('keeps the current projection stable when another private group edits its helper or extra implementation', () => {
    const own = lemma('own', 'current'), secret = lemma('secret', 'private');
    const privateNode = node(secret);
    privateNode.proof = { changes: [{ file: 'Helpers.lean', name: 'Fixture.private_extra', after: 'lemma private_extra : True := by trivial' }] } as TaskProof;
    const tasks = [node(current), node(own), privateNode];
    const first = sources('lemma own : True := by trivial\nlemma secret : True := by trivial\nlemma private_extra : True := by trivial\n');
    const next = sources('lemma own : True := by trivial\nlemma secret : True := by exact True.intro\nlemma private_extra : True := by exact True.intro\n');
    const before = project(current, first, tasks), after = project(current, next, tasks);
    expect(before).toEqual(after);
    expect(researchSourceDigest(before)).toBe(researchSourceDigest(after));
    expect(after['Helpers.lean']).toContain('lemma own');
    expect(after['Helpers.lean']).not.toContain('lemma secret');
    expect(after['Helpers.lean']).not.toContain('lemma private_extra');
  });

  it('retains a shared checked wrapper and its transitive private implementation prerequisites', () => {
    const base = lemma('private_base', 'other'), implementation = lemma('private_impl', 'other', 'group', [base.id]);
    const wrapper = lemma('shared_wrapper', 'other', 'problem', [implementation.id]), unrelated = lemma('unrelated_private', 'other');
    const text = sources('lemma private_base : True := by trivial\nlemma private_impl : True := by exact private_base\n' +
      'lemma shared_wrapper : True := by exact private_impl\nlemma unrelated_private : True := by trivial\n');
    const projected = project(current, text, [node(current), node(base, 'integrated'), node(implementation, 'integrated'),
      node(wrapper, 'integrated'), node(unrelated, 'integrated')]);
    expect(projected['Helpers.lean']).toContain('lemma shared_wrapper');
    expect(projected['Helpers.lean']).toContain('lemma private_impl');
    expect(projected['Helpers.lean']).toContain('lemma private_base');
    expect(projected['Helpers.lean']).not.toContain('lemma unrelated_private');
  });

  it('includes a declared cross-group public dependency before completion, and hides an undeclared pending peer', () => {
    const dependency = lemma('public_dependency', 'other', 'problem'), peer = lemma('unrelated_pending', 'other', 'problem');
    const consumer = { ...current, dependsOn: [dependency.id] };
    const text = sources('lemma public_dependency : True := by trivial\nlemma unrelated_pending : True := by trivial\n');
    const projected = project(consumer, text, [node(consumer), node(dependency), node(peer)]);
    expect(projected['Helpers.lean']).toContain('lemma public_dependency');
    expect(projected['Helpers.lean']).not.toContain('lemma unrelated_pending');
  });

  it('retains the existing seed algorithm private implementation closure for an explicitly declared dependency', () => {
    // Plan validation forbids direct cross-group private dependencies. Source
    // projection still preserves its old compile-closure behavior if given one.
    const dependency = lemma('private_dependency', 'other', 'group'), consumer = { ...current, dependsOn: [dependency.id] };
    const text = sources('lemma private_dependency : True := by trivial\n');
    expect(project(consumer, text, [node(consumer), node(dependency)])['Helpers.lean']).toContain('lemma private_dependency');
    expect(project(current, text, [node(current), node(dependency)])['Helpers.lean']).not.toContain('lemma private_dependency');
  });

  it('keeps public completed research implementation helpers visible and hides pending public work', () => {
    const completed: CooperativeTask = { ...current, id: 'completed_route', groupId: 'other', sharing: 'problem' };
    const completedNode = node(completed, 'completed');
    completedNode.proof = { changes: [{ file: 'Helpers.lean', name: 'Fixture.route_probe', after: 'lemma route_probe : True := by trivial' }] } as TaskProof;
    const pending = lemma('pending_public', 'other', 'problem');
    const projected = project(current, sources('lemma route_probe : True := by trivial\nlemma pending_public : True := by trivial\n'),
      [node(current), completedNode, node(pending)]);
    expect(projected['Helpers.lean']).toContain('lemma route_probe');
    expect(projected['Helpers.lean']).not.toContain('lemma pending_public');
  });

  it('does not mutate frozen problem/source/task inputs or turn semantic proof metadata into proof acceptance', () => {
    const own = lemma('own', 'current'), secret = lemma('secret', 'other'), text = sources('lemma own : True := by trivial\nlemma secret : True := by trivial\n');
    const ownNode = node(own, 'integrated');
    ownNode.integratedCheck = { passed: true, taskDigest: taskVersion(own), conditions: [], changes: [], commit: 'checked',
      sourceDigest: 'checked-source', seedCommit: 'seed', verification: { status: 'kernel_verified', results: [] } } as TaskProof;
    const tasks = freeze([node(current), ownNode, node(secret)]), immutableProblem = freeze(structuredClone(problem));
    const immutableSources = freeze(text), before = JSON.stringify({ immutableProblem, immutableSources, tasks });
    const semanticTasks = researchSourceTasks(tasks), projected = scopedResearchSources(immutableProblem, current, immutableSources, semanticTasks);
    expect(projected['Helpers.lean']).not.toContain('lemma secret');
    expect(JSON.stringify({ immutableProblem, immutableSources, tasks })).toBe(before);
    expect(semanticTasks.find(item => item.task.id === own.id)?.integratedCheck).toEqual({ passed: true, taskDigest: taskVersion(own), conditions: [] });
    expect(semanticTasks.find(item => item.task.id === own.id)?.integratedCheck).not.toHaveProperty('verification');
    expect(semanticTasks.find(item => item.task.id === own.id)?.integratedCheck).not.toHaveProperty('commit');
    const full = scopedResearchSources(immutableProblem, undefined, immutableSources, semanticTasks);
    expect(full).toEqual(immutableSources);
    expect(full).not.toBe(immutableSources);
  });
});
