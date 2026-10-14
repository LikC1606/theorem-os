import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, describe, expect, it } from 'vitest';
import { comparisonOrder, comparisonReport, comparisonTotals } from '../scripts/mathematics/compareMathRuns';
import { configuredSolverModules, directSolverModules, solverMethodDigest } from '../src/solver/modules';
import { readyResearchTasks } from '../src/solver/modules/search';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';
import type { TaskRecord } from '../src/solver/tasks';

const directories: string[] = [];
afterEach(() => { for (const directory of directories.splice(0)) fs.rmSync(directory, { recursive: true, force: true }); });

describe('configured research comparisons', () => {
  it('replaces only M3 ordering while retaining dependency and pause gates', () => {
    const node = (id: string, kind: 'lemma' | 'goal', dependsOn: string[] = [], status?: 'paused'): TaskRecord => ({
      task: { id, kind, objective: id, dependsOn, revision: 0, status }, status: 'pending', attempts: 0 });
    const tasks = [node('helper', 'lemma'), node('blocked-goal', 'goal', ['helper']), node('ready-goal', 'goal'), node('paused', 'goal', [], 'paused')];
    const modules = configuredSolverModules('direct', 'goals-first');
    expect(readyResearchTasks(tasks).map(node => node.task.id)).toEqual(['helper', 'ready-goal']);
    expect(modules.M3.ready(tasks).map(node => node.task.id)).toEqual(['ready-goal', 'helper']);
    for (const module of ['M1', 'M2', 'M4', 'M5']) expect(modules[module]).toBe(directSolverModules[module]);
    expect(configuredSolverModules('direct', 'plan')).toBe(directSolverModules);
    expect(() => configuredSolverModules('direct', 'typo')).toThrow('invalid --scheduler');
  });

  it('preserves historical default module hashes and distinguishes the new configurations', () => {
    const previous = mathDigest(canonicalMathJson({ id: directSolverModules.id, versions: Object.entries(directSolverModules)
      .filter(([key]) => key !== 'id').map(([key, module]) => [key, (module as { version: string }).version]) }));
    expect(solverMethodDigest(directSolverModules, 'cooperative')).toBe(previous);
    expect(solverMethodDigest(directSolverModules, 'independent')).not.toBe(previous);
    expect(solverMethodDigest(configuredSolverModules('direct', 'goals-first'), 'cooperative')).not.toBe(previous);
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
        usage: { totalTokens: 100 }, workers: job.arm === 'single' ? undefined : [
          { id: 'solver', role: 'lead', worktree: directory, phase: 'finished', turns: 1, usage: { totalTokens: 100 } },
          { id: 'engineer', role: 'engineer', worktree: directory, phase: 'finished', turns: 1, error: 'provider failed' }] }));
      fs.writeFileSync(job.output, JSON.stringify({ schema: 'deepscientist.math.run.v2', runId: job.arm,
        stateFile, status: 'runtime_error', reason: 'fixture failure' }));
    }
    const report = comparisonReport(directory, plan);
    expect(report.runs.map(row => row.status)).toEqual(['runtime_error', 'runtime_error', 'missing']);
    expect(report.runs.map(row => row.totalTokens)).toEqual([100, null, null]);
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
