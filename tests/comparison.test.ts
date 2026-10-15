import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, describe, expect, it } from 'vitest';
import { comparisonOrder, comparisonReport, comparisonTotals } from '../scripts/mathematics/compareMathRuns';
import { configuredSolverModules, directSolverModules, solverMethodDigest } from '../src/solver/modules';
import { readyResearchTasks } from '../src/solver/modules/search';
import { researchWorkers } from '../src/solver/modules/organization';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';
import type { RouteRecord, TaskRecord } from '../src/solver/tasks';

const directories: string[] = [];
afterEach(() => { for (const directory of directories.splice(0)) fs.rmSync(directory, { recursive: true, force: true }); });

describe('configured research comparisons', () => {
  const node = (id: string, kind: 'lemma' | 'goal', dependsOn: string[] = [], status?: 'paused'): TaskRecord => ({
    task: { id, kind, objective: id, dependsOn, revision: 0, status }, status: 'pending', attempts: 0 });

  it('replaces only M3 ordering while retaining dependency and pause gates', () => {
    const tasks = [node('helper', 'lemma'), node('blocked-goal', 'goal', ['helper']), node('ready-goal', 'goal'), node('paused', 'goal', [], 'paused')];
    const modules = configuredSolverModules('direct', 'goals-first');
    expect(readyResearchTasks(tasks).map(node => node.task.id)).toEqual(['helper', 'ready-goal']);
    expect(modules.M3.ready(tasks).map(node => node.task.id)).toEqual(['ready-goal', 'helper']);
    for (const module of ['M1', 'M2', 'M4', 'M5']) expect(modules[module]).toBe(directSolverModules[module]);
    expect(configuredSolverModules('direct', 'plan')).toBe(directSolverModules);
    expect(() => configuredSolverModules('direct', 'typo')).toThrow('invalid --scheduler');
  });

  it('prioritizes unfinished goal dependency depth, then distinct goal coverage, with stable ties', () => {
    const tasks = [node('unneeded', 'lemma'), node('ready-goal', 'goal'), node('short', 'lemma'),
      node('shared', 'lemma'), node('deep', 'lemma'), node('tie', 'lemma'),
      node('short-goal', 'goal', ['short', 'tie']), node('shared-goal-1', 'goal', ['shared']),
      node('shared-goal-2', 'goal', ['shared']), node('middle', 'lemma', ['deep']), node('long-goal', 'goal', ['middle'])];
    const modules = configuredSolverModules('direct', 'critical-path');
    expect(modules.M3.ready(tasks).map(record => record.task.id)).toEqual([
      'deep', 'shared', 'short', 'tie', 'ready-goal', 'unneeded',
    ]);
    tasks.find(record => record.task.id === 'long-goal')!.status = 'integrated';
    const paused = tasks.find(record => record.task.id === 'shared-goal-2')!;
    paused.task = { ...paused.task, status: 'paused' };
    expect(modules.M3.ready(tasks).map(record => record.task.id)).toEqual([
      'short', 'shared', 'tie', 'ready-goal', 'unneeded', 'deep',
    ]);
  });

  it('retains route readiness gates and does not prioritize paths through inactive work', () => {
    const tasks = [node('unneeded', 'lemma'), node('stopped-path', 'lemma'), node('active', 'lemma'),
      node('paused-middle', 'lemma', ['stopped-path'], 'paused'), node('paused-goal', 'goal', ['paused-middle']),
      node('active-goal', 'goal', ['active']), node('full-route', 'goal'), node('spent-route', 'goal')];
    tasks[6].task = { ...tasks[6].task, groupId: 'full' }; tasks[7].task = { ...tasks[7].task, groupId: 'spent' };
    const groups: RouteRecord[] = [
      { group: { id: 'main', objective: 'main', status: 'active', revision: 0 }, turns: 0 },
      { group: { id: 'full', objective: 'full', status: 'active', revision: 0, maxConcurrent: 1 }, turns: 0, busy: 1 },
      { group: { id: 'spent', objective: 'spent', status: 'active', revision: 0, maxTurns: 1 }, turns: 1 },
    ];
    expect(configuredSolverModules('direct', 'critical-path').M3.ready(tasks, groups).map(record => record.task.id))
      .toEqual(['active', 'unneeded', 'stopped-path']);
  });

  it('shares ranked work across proof roles while preserving explicit and resumed ownership', () => {
    const modules = configuredSolverModules('direct', 'critical-path');
    const workers = researchWorkers('/worktree', [], 4), engineer = workers.at(-1)!, researcher = workers[1];
    const helper = node('helper', 'lemma'), goal = node('goal', 'goal');
    expect(modules.M5.assign([helper, goal], engineer, workers)).toBe(helper);
    expect(modules.M5.assign([goal, helper], researcher, workers)).toBe(goal);
    expect(modules.M5.assign([helper], workers[0], workers)).toBeUndefined();
    expect(modules.M5.assign([helper], { ...researcher, role: 'reviewer' }, workers)).toBeUndefined();
    helper.task = { ...helper.task, ownerId: researcher.id };
    expect(modules.M5.assign([helper], engineer, workers)).toBeUndefined();
    helper.task = { ...helper.task, ownerId: undefined };
    helper.assignment = { taskId: 'helper', taskDigest: 'digest', workerId: researcher.id, seedCommit: 'seed' };
    expect(modules.M5.assign([helper], engineer, workers)).toBeUndefined();
    expect(modules.M5.assign([helper], researcher, workers)).toBe(helper);
    const groups: RouteRecord[] = [{ group: { id: 'main', objective: 'main', status: 'active', revision: 0,
      engineerId: engineer.id }, turns: 0 }];
    expect(modules.M5.assign([goal], researcher, workers, groups)).toBeUndefined();
    expect(modules.M5.assign([goal], engineer, workers, groups)).toBe(goal);
  });

  it.each(['direct', 'lemma'])('binds critical-path search and assignment versions for %s', method => {
    const base = configuredSolverModules(method, 'plan'), modules = configuredSolverModules(method, 'critical-path');
    for (const module of ['M1', 'M2', 'M4']) expect(modules[module]).toBe(base[module]);
    expect(modules.M3.select).toBe(base.M3.select);
    expect(modules.M5.workers).toBe(base.M5.workers);
    expect(modules.M5.reviewer).toBe(base.M5.reviewer);
    const digests = ['plan', 'goals-first', 'critical-path'].map(scheduler =>
      solverMethodDigest(configuredSolverModules(method, scheduler), 'cooperative'));
    expect(new Set(digests).size).toBe(3);
  });

  it('preserves historical default module hashes and distinguishes the new configurations', () => {
    const previous = mathDigest(canonicalMathJson({ id: directSolverModules.id, versions: Object.entries(directSolverModules)
      .filter(([key]) => key !== 'id').map(([key, module]) => [key, (module as { version: string }).version]) }));
    expect(solverMethodDigest(directSolverModules, 'cooperative')).toBe(previous);
    expect(solverMethodDigest(directSolverModules, 'independent')).not.toBe(previous);
    expect(solverMethodDigest(configuredSolverModules('direct', 'goals-first'), 'cooperative')).not.toBe(previous);
  });

  it('binds primary-led assistance to distinct context and assignment versions', () => {
    const modules = configuredSolverModules('direct', 'primary-led');
    expect(modules.M5.primaryLed).toBe(true);
    for (const module of ['M1', 'M2', 'M3']) expect(modules[module]).toBe(directSolverModules[module]);
    expect(modules.M4.version).not.toBe(directSolverModules.M4.version);
    expect(modules.M5.version).not.toBe(directSolverModules.M5.version);
    expect(solverMethodDigest(modules, 'cooperative')).not.toBe(solverMethodDigest(directSolverModules, 'cooperative'));
  });

  it('rotates arm order and includes missing runs in the planned denominator', () => {
    expect(comparisonOrder(3).map(row => row.arm)).toEqual([
      'single', 'independent', 'cooperative', 'independent', 'cooperative', 'single', 'cooperative', 'single', 'independent']);
    const totals = comparisonTotals([{ arm: 'single', accepted: true, totalTokens: 100 },
      { arm: 'single', accepted: false, totalTokens: null }, { arm: 'independent', accepted: false, totalTokens: 200 }]);
    expect(totals[0]).toMatchObject({ planned: 2, accepted: 1, acceptanceRate: 0.5, missingTokenRuns: 1, reportedTokens: 100 });
    expect(totals[2]).toMatchObject({ planned: 0, acceptanceRate: null });
  });

  it('reports failed usage, partial usage and missing results without manufacturing acceptance', () => {
    const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'math-comparison-')); directories.push(directory);
    const plan = { schema: 'deepscientist.math.comparison.v1' as const, problem: 'p', sourceCommit: 'source',
      taskDigest: 'task', buildDigest: 'build', environmentDigest: 'environment',
      configuration: { model: 'fixture', effort: 'xhigh', method: 'direct', scheduler: 'plan', workers: 2,
        maxTurns: 20, maxRunSeconds: 1800, maxTurnSeconds: 180 },
      jobs: comparisonOrder(1).map(item => ({ ...item, launch: path.join(directory, item.arm + '-launch.json'),
        launchDigest: 'launch', output: path.join(directory, item.arm + '.json'), receiptDigest: 'receipt', methodDigest: 'method' })) };
    for (const job of plan.jobs.slice(0, 2)) {
      const runtime = job.output + '.runtime'; fs.mkdirSync(runtime);
      const stateFile = path.join(runtime, 'state.json');
      fs.writeFileSync(stateFile, JSON.stringify({ schema: 'deepscientist.math.solver.v1', runId: job.arm,
        problem: { workspace: directory, receiptDigest: 'receipt' }, taskDigest: 'task', buildDigest: 'build',
        environmentDigest: 'environment', evaluatorDigest: mathDigest('host-default'), methodDigest: 'method', model: 'fixture', effort: 'xhigh',
        worktree: directory, phase: 'finished', turns: 2, coordination: 'independent', workerCount: job.arm === 'single' ? 1 : 2,
        dispatchCounts: { proof: 2 }, solveStartedAt: 1000, solveFinishedAt: 5500,
        usage: { totalTokens: 100 }, workers: job.arm === 'single' ? undefined : [
          { id: 'solver', role: 'lead', worktree: directory, phase: 'finished', turns: 1, usage: { totalTokens: 100 } },
          { id: 'engineer', role: 'engineer', worktree: directory, phase: 'finished', turns: 1, error: 'provider failed' }] }));
      fs.writeFileSync(job.output, JSON.stringify({ schema: 'deepscientist.math.run.v2', runId: job.arm,
        stateFile, status: 'runtime_error', reason: 'fixture failure' }));
    }
    const report = comparisonReport(directory, plan);
    expect(report.runs.map(row => row.status)).toEqual(['runtime_error', 'runtime_error', 'missing']);
    expect(report.runs.map(row => row.totalTokens)).toEqual([100, null, null]);
    expect(report.runs[0]).toMatchObject({ dispatches: 2, dispatchCounts: { proof: 2 }, solveWallMs: 4500 });
    expect(report.runs[1].missingUsageWorkers).toEqual(['engineer']);
    expect(report.runs.every(row => !row.accepted)).toBe(true);
    expect(report.totals.every(row => row.planned === 1)).toBe(true);
    const stateFile = plan.jobs[0].output + '.runtime/state.json';
    const state = JSON.parse(fs.readFileSync(stateFile, 'utf8'));
    const check = { commit: 'commit', sourceDigest: 'source', passed: true,
      verification: { status: 'kernel_verified', targetCommit: 'commit', results: [{ status: 'kernel_verified', targetCommit: 'commit',
        proofPath: 'Submission.lean', theoremName: 'target', statementHash: 'informal', leanStatementHash: 'formal',
        claim: 'statement', sourceDeclarationHash: 'declaration' }] } };
    fs.writeFileSync(stateFile, JSON.stringify({ ...state, check, problem: { ...state.problem,
      targets: [{ proofPath: 'Submission.lean', theoremName: 'target', declarationHash: 'declaration' }],
      contract: { statementHash: 'informal', leanStatementHash: 'formal' } } }));
    fs.writeFileSync(plan.jobs[0].output, JSON.stringify({ schema: 'deepscientist.math.run.v2', runId: 'single', stateFile,
      status: 'evaluated_passed', completion_signal_valid: true, solver_ready_receipt_valid: true, solution_commit: 'commit',
      evaluator: { status: 'passed', method: 'host-lean-kernel-all-targets', official: false, verification: check } }));
    expect(comparisonReport(directory, plan).runs[0].accepted).toBe(true);
    const result = JSON.parse(fs.readFileSync(plan.jobs[0].output, 'utf8'));
    result.evaluator.verification.verification.results[0].theoremName = 'wrong-target';
    fs.writeFileSync(plan.jobs[0].output, JSON.stringify(result));
    expect(comparisonReport(directory, plan).runs[0]).toMatchObject({ accepted: false, error: 'comparison_acceptance_evidence_incomplete' });
    fs.writeFileSync(stateFile, JSON.stringify({ ...state, methodDigest: 'another method' }));
    expect(comparisonReport(directory, plan).runs[0]).toMatchObject({ status: 'invalid', accepted: false });
  });
});
