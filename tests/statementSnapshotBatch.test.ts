import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { LOCAL_EXAMPLE_STATEMENT } from '../src/math/localExample';
import type { LeanStatementContext } from '../src/math/leanStatementContext';
import type { SolverRunState } from '../src/solver/archive';
import type { CooperativeResearch } from '../src/solver/cooperation';
import { commitSolverSources, type SolverProblem } from '../src/solver/problem';
import { createStatementSnapshotter, statementSnapshot } from '../src/solver/statementReview';
import { taskVersion, type CooperativeTask } from '../src/solver/tasks';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, solverState } from './helpers/solver';

const host = vi.hoisted(() => ({ reads: vi.fn(), inspections: vi.fn(), masks: vi.fn(), capture: vi.fn(), sessions: vi.fn() }));
vi.mock('../src/solver/problem', async importOriginal => {
  const original = await importOriginal<typeof import('../src/solver/problem')>();
  return { ...original, committedSource: (...args: Parameters<typeof original.committedSource>) => {
    host.reads(...args); return original.committedSource(...args);
  } };
});
vi.mock('../src/math/leanSource', async importOriginal => {
  const original = await importOriginal<typeof import('../src/math/leanSource')>();
  return { ...original, inspectLeanDeclarationRegions: (...args: Parameters<typeof original.inspectLeanDeclarationRegions>) => {
    host.inspections(...args); return original.inspectLeanDeclarationRegions(...args);
  } };
});
vi.mock('../src/math/leanSyntax', async importOriginal => {
  const original = await importOriginal<typeof import('../src/math/leanSyntax')>();
  return { ...original, maskLeanComments: (source: string) => { host.masks(source); return original.maskLeanComments(source); } };
});
vi.mock('../src/solver/statementReview', async importOriginal => ({
  ...await importOriginal<typeof import('../src/solver/statementReview')>(), captureStatementContexts: host.capture,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.sessions }));

describe('statement snapshot preparation within a single call', () => {
  let directory: string, workspace: string, commit: string, problem: SolverProblem, tasks: CooperativeTask[];
  let cooperative: CooperativeResearch, controller: AbortController, state: SolverRunState, sources: string[];
  const environmentDigest = 'statement-batch-environment';
  const dependencies = (task: CooperativeTask) => tasks.filter(item => task.dependsOn.includes(item.id))
    .map(item => ({ task: item, taskDigest: taskVersion(item) }));
  const snapshot = (task: CooperativeTask, context?: LeanStatementContext) =>
    statementSnapshot(problem, task, workspace, commit, environmentDigest, dependencies(task), context);
  const context = (task: CooperativeTask): LeanStatementContext => ({
    type: task.type ?? '∀ (n : Nat), n + 0 = n', constants: [], omitted: [],
  });
  const clearCounts = () => { host.reads.mockClear(); host.inspections.mockClear(); host.masks.mockClear(); };
  const expectSinglePreparation = () => {
    expect(host.reads).toHaveBeenCalledTimes(2);
    expect(host.inspections).toHaveBeenCalledTimes(2);
    expect(host.masks.mock.calls.filter(([source]) => sources.includes(source))).toHaveLength(2);
  };

  beforeEach(() => {
    host.capture.mockReset().mockImplementation(async (_problem: SolverProblem, requested: CooperativeTask[]) =>
      new Map(requested.map(task => [task.id, context(task)])));
    host.sessions.mockReset().mockImplementation(() => { throw new Error('fixture_real_models_forbidden'); });
    ({ directory, workspace, problem } = localExample('statement-snapshot-batch-'));
    const source = LOCAL_EXAMPLE_STATEMENT.replace('theorem add_zero',
      'def kept : String := "visible definition"\nlemma helper : True := by trivial /- COMMENT_SECRET PROOF_SECRET -/\ntheorem add_zero');
    fs.writeFileSync(path.join(workspace, problem.projectRelative, 'Submission.lean'), source);
    commit = commitSolverSources(problem, workspace);
    sources = [LOCAL_EXAMPLE_STATEMENT, source];
    tasks = [
      ...problem.targets.map((target, index) => ({ id: `goal_${index}`, kind: 'goal' as const,
        theoremName: target.theoremName, proofPath: target.proofPath, dependsOn: [], revision: 0 })),
      { id: 'helper', kind: 'lemma', theoremName: 'Tutorial.helper', proofPath: 'Submission.lean', type: 'True',
        dependsOn: ['goal_0'], revision: 0 },
    ].map(task => ({ ...task, objective: 'INTENT_SECRET', informalStatement: 'INTENT_SECRET', statementReview: true }));
    state = solverState(problem, workspace, { runId: 'statement-batch-fixture', phase: 'running', environmentDigest,
      cooperation: { canonicalCommit: commit, tasks: tasks.map(task => ({ task, status: 'pending', attempts: 0 })) } });
    controller = new AbortController();
    cooperative = cooperativeResearch({ state, workers: [leadWorker(problem, workspace, 'lead')], retrievalRoot: directory,
      signal: controller.signal, exclusiveCheck: operation => operation() });
    clearCounts();
  });
  afterEach(async () => {
    controller?.abort(); await cooperative?.stop(); expect(host.sessions).not.toHaveBeenCalled();
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it('reads and inspects two sources once while preparing three cached statement keys', () => {
    for (const task of tasks) (cooperative as any).statementContexts.set(snapshot(task).snapshotDigest, context(task));
    clearCounts();
    expect((cooperative as any).prepareStatementContexts()).toBeUndefined();
    expectSinglePreparation();
    expect(host.capture).not.toHaveBeenCalled();
  });

  it('shares two source preparations across both synchronization passes without changing snapshots', () => {
    const expected = tasks.map(task => snapshot(task, context(task)));
    for (const task of tasks) (cooperative as any).statementContexts.set(snapshot(task).snapshotDigest, context(task));
    clearCounts();
    (cooperative as any).syncStatementReviews();
    expectSinglePreparation();
    expect(state.cooperation!.statementReviews).toHaveLength(3);
    for (const [index, review] of state.cooperation!.statementReviews!.entries()) {
      const actual = expected[index]!;
      expect(review.snapshotDigest).toBe(actual.snapshotDigest);
      expect(JSON.parse(fs.readFileSync(path.join(review.workspace, 'STATEMENT.json'), 'utf8')))
        .toEqual(JSON.parse(JSON.stringify({ ...actual.input, snapshotDigest: actual.snapshotDigest })));
      for (const [fileIndex, definition] of actual.definitions.entries())
        expect(fs.readFileSync(path.join(review.workspace, `definitions/${fileIndex}.lean`), 'utf8')).toBe(definition.source);
    }
    expect(host.capture).not.toHaveBeenCalled();
  });

  it('keeps each blind goal and helper snapshot complete and independent', () => {
    const expected = tasks.map(task => snapshot(task, context(task)));
    const build = createStatementSnapshotter(problem, workspace, commit, environmentDigest);
    clearCounts();
    const actual = tasks.map(task => build(task, dependencies(task), context(task)));
    expectSinglePreparation();
    expect(actual).toEqual(expected);
    for (const [index, value] of actual.entries()) {
      expect(value.input.definitions.map(file => file.originalFile)).toEqual(['Challenge.lean', 'Submission.lean']);
      const trusted = value.definitions[0]!.source, owned = value.definitions[1]!.source;
      expect(trusted).not.toMatch(/\b(?:theorem|lemma)\b/u);
      expect(owned).toContain('def kept : String := "visible definition"');
      if (tasks[index]!.kind === 'goal') {
        const name = tasks[index]!.theoremName!.split('.').at(-1)!;
        const other = tasks.find(task => task.kind === 'goal' && task.id !== tasks[index]!.id)!.theoremName!.split('.').at(-1)!;
        expect(owned).toContain(`theorem ${name}`);
        expect(owned).not.toContain(`theorem ${other}`);
        expect(value.input.dependencies).toEqual([]);
      } else {
        expect(owned).not.toMatch(/\b(?:theorem|lemma)\b/u);
        expect(value.input.dependencies[0]!.taskDigest).toBe(taskVersion(tasks[0]!));
      }
      expect(JSON.stringify(value)).not.toMatch(/COMMENT_SECRET|PROOF_SECRET|INTENT_SECRET|by sorry|by trivial/u);
    }
    actual[0]!.definitions[0]!.source = 'mutated';
    actual[0]!.input.definitions[0]!.path = 'mutated';
    actual[2]!.input.dependencies[0]!.taskDigest = 'mutated';
    expect(actual[1]).toEqual(expected[1]);
    expect(build(tasks[0]!, [], context(tasks[0]!))).toEqual(expected[0]);
    expect(build(tasks[2]!, dependencies(tasks[2]!), context(tasks[2]!))).toEqual(expected[2]);
  });

  it('does not share mutable elaboration or audit versions between returned snapshots', () => {
    const build = createStatementSnapshotter(problem, workspace, commit, environmentDigest), task = tasks[2]!;
    const elaboration: LeanStatementContext = { type: 'True', constants: [
      { name: 'Nat', module: 'Init', type: 'Type' }], omitted: ['a bounded dependency'] };
    const before = build(task, dependencies(task), elaboration);
    tasks[0] = { ...tasks[0]!, objective: 'A new explanation of the same contract.', revision: 1 };
    const after = build(task, dependencies(task), elaboration);
    expect(after.snapshotDigest).toBe(before.snapshotDigest);
    expect(after.input.dependencies[0]!.taskDigest).not.toBe(before.input.dependencies[0]!.taskDigest);
    before.input.elaboration!.constants[0]!.type = 'mutated';
    before.input.elaboration!.omitted.push('mutated');
    expect(after.input.elaboration).toEqual(elaboration);
    expect(build(task, dependencies(task), elaboration)).toEqual(after);
  });

  it('prepares new committed sources on later calls without altering a fixed earlier batch', () => {
    const task = tasks[2]!, build = createStatementSnapshotter(problem, workspace, commit, environmentDigest);
    const before = build(task, dependencies(task));
    fs.writeFileSync(path.join(workspace, problem.projectRelative, 'Submission.lean'),
      sources[1]!.replace('visible definition', 'updated definition'));
    commit = commitSolverSources(problem, workspace);
    clearCounts();
    expect(build(task, dependencies(task))).toEqual(before);
    expect(host.reads).not.toHaveBeenCalled();
    const after = createStatementSnapshotter(problem, workspace, commit, environmentDigest)(task, dependencies(task));
    expect(host.reads).toHaveBeenCalledTimes(2);
    expect(host.inspections).toHaveBeenCalledTimes(2);
    expect(after.definitions[1]!.source).toContain('updated definition');
    expect(after.snapshotDigest).not.toBe(before.snapshotDigest);
  });

  it('keeps size accounting per target when one prepared source is reused', () => {
    const largeHelpers = `def large : String := "${'é'.repeat(370_000)}"\n`;
    fs.writeFileSync(path.join(workspace, problem.projectRelative, 'Submission.lean'),
      sources[1]!.replace('theorem add_zero', largeHelpers + 'theorem add_zero'));
    commit = commitSolverSources(problem, workspace);
    const build = createStatementSnapshotter(problem, workspace, commit, environmentDigest);
    const values = [...tasks, ...tasks].map(task => build(task, dependencies(task)));
    expect(values.every(value => value.definitions.reduce((total, file) => total + Buffer.byteLength(file.source), 0) < 4_000_000)).toBe(true);
    expect(values.reduce((total, value) => total + value.definitions.reduce((size, file) => size + Buffer.byteLength(file.source), 0), 0)).toBeGreaterThan(4_000_000);
    expect(values[0]!.definitions[1]!.source).toContain('é'.repeat(10));
  });
});
