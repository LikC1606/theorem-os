import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, describe, expect, it, vi } from 'vitest';
import { compareMathRuns, comparisonReport, comparisonReportFreshness, writeComparisonReport } from '../scripts/mathematics/compareMathRuns';
import { writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { buildTokenBudget } from '../src/solver/usageBudget';

const directories: string[] = [];
afterEach(() => {
  vi.restoreAllMocks();
  for (const directory of directories.splice(0)) fs.rmSync(directory, { recursive: true, force: true });
});

function fixture() {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'math-comparison-snapshot-')); directories.push(directory);
  const output = path.join(directory, 'result.json'), stateFile = `${output}.runtime/state.json`;
  fs.mkdirSync(path.dirname(stateFile));
  const plan: Parameters<typeof comparisonReport>[1] = {
    schema: 'deepscientist.math.comparison.v1', problem: 'example', sourceCommit: 'source', taskDigest: 'task',
    buildDigest: 'build', environmentDigest: 'environment',
    configuration: { model: 'fixture', effort: 'fixture', method: 'direct', scheduler: 'plan', workers: 1,
      maxTurns: 20, maxRunSeconds: 600, maxTurnSeconds: 180, maxTotalTokens: 30000 },
    jobs: [{ arm: 'cooperative', repetition: 1, launch: path.join(directory, 'launch.json'), launchDigest: 'launch',
      output, receiptDigest: 'problem', methodDigest: 'method' }],
  };
  const state = {
    schema: 'deepscientist.math.solver.v1', runId: 'resumable-run', worktree: directory, phase: 'finished', turns: 1,
    model: 'fixture', effort: 'fixture', taskDigest: 'task', buildDigest: 'build', environmentDigest: 'environment',
    evaluatorDigest: mathDigest('host-default'), methodDigest: 'method', workerCount: 1, coordination: 'cooperative',
    problem: { workspace: directory, receiptDigest: 'problem', targets: [{ proofPath: 'Submission.lean', theoremName: 'goal', declarationHash: 'declaration' }],
      contract: { statementHash: 'statement', leanStatementHash: 'lean-statement' } },
    tokenBudget: buildTokenBudget(30000, []),
  } as unknown as SolverRunState;
  let result: Record<string, unknown> = { schema: 'deepscientist.math.run.v2', runId: state.runId, stateFile,
    status: 'limit_reached', reason: 'math_total_token_limit', solution_commit: null };
  const save = () => {
    writeSolverRunState(stateFile, state); fs.writeFileSync(output, JSON.stringify(result));
  };
  const pass = () => {
    const commit = 'checked-commit';
    state.check = { commit, sourceDigest: 'checked-source', passed: true,
      verification: { status: 'kernel_verified', targetCommit: commit, results: [{ status: 'kernel_verified', targetCommit: commit,
        proofPath: 'Submission.lean', theoremName: 'goal', statementHash: 'statement', leanStatementHash: 'lean-statement',
        claim: 'statement', sourceDeclarationHash: 'declaration' }] } } as never;
    result = { schema: 'deepscientist.math.run.v2', runId: state.runId, stateFile, status: 'evaluated_passed',
      solution_commit: commit, completion_signal_valid: true, solver_ready_receipt_valid: true,
      evaluator: { status: 'passed', method: 'host-lean-kernel-all-targets', official: false, verification: state.check } };
    save();
  };
  save(); fs.writeFileSync(path.join(directory, 'comparison.json'), JSON.stringify(plan));
  return { directory, output, stateFile, state, plan, save, pass };
}

describe('comparison report observations', () => {
  it.each(['state', 'result'])('detects changed %s evidence even with the same run ID, turn count and terminal status', channel => {
    const f = fixture(), report = comparisonReport(f.directory, f.plan);
    expect(comparisonReportFreshness(f.directory, f.plan, report).freshness).toBe('current');
    if (channel === 'state') { f.state.error = 'new-observation'; f.save(); }
    else {
      const result = JSON.parse(fs.readFileSync(f.output, 'utf8'));
      fs.writeFileSync(f.output, JSON.stringify({ ...result, reason: 'different-terminal-reason' }));
    }
    const checked = comparisonReportFreshness(f.directory, f.plan, report);
    expect(checked).toMatchObject({ freshness: 'stale', runs: [{ freshness: 'stale',
      previous: { status: 'limit_reached' }, current: { status: 'limit_reached' } }] });
  });

  it('shows a passed unlimited continuation without counting it under the original fixed budget', () => {
    const f = fixture(), report = comparisonReport(f.directory, f.plan);
    f.state.tokenBudget = buildTokenBudget(0, []); f.state.turns = 6; f.pass();
    const current = comparisonReport(f.directory, f.plan);
    expect(current.runs[0]).toMatchObject({ status: 'invalid', accepted: false, totalTokens: null,
      error: 'comparison_token_budget_mismatch', comparisonIdentityMatches: false,
      currentObservation: { runId: f.state.runId, status: 'evaluated_passed', maxTotalTokens: 0,
        localAcceptanceEvidenceMatches: true } });
    expect(current.totals.find(total => total.arm === 'cooperative')).toMatchObject({ planned: 1, accepted: 0, missingTokenRuns: 1 });
    expect(comparisonReportFreshness(f.directory, f.plan, report)).toMatchObject({ freshness: 'stale', runs: [{
      previous: { status: 'limit_reached', accepted: false }, current: { accepted: false,
        observation: { status: 'evaluated_passed', localAcceptanceEvidenceMatches: true } } }] });
  });

  it('keeps the existing independent local acceptance requirements for matching inputs', () => {
    const f = fixture(); f.pass();
    expect(comparisonReport(f.directory, f.plan).runs[0]).toMatchObject({ status: 'evaluated_passed', accepted: true,
      comparisonIdentityMatches: true, currentObservation: { localAcceptanceEvidenceMatches: true } });
    f.state.check!.verification.results[0].sourceDeclarationHash = 'different-declaration'; f.save();
    expect(comparisonReport(f.directory, f.plan).runs[0]).toMatchObject({ accepted: false,
      error: 'comparison_acceptance_evidence_incomplete' });
  });

  it('treats legacy unbound reports as unknown and detects modified bound reports', () => {
    const f = fixture(), report = comparisonReport(f.directory, f.plan);
    const { reportHash: _hash, generatedAt: _at, sourcePlanDigest: _plan, sourceBatchDigest: _batch, ...legacy } = report;
    expect(comparisonReportFreshness(f.directory, f.plan, legacy).freshness).toBe('unknown');
    expect(comparisonReportFreshness(f.directory, f.plan, { ...report, official: true }).freshness).toBe('invalid');
  });

  it('binds batch observations and retains a previous report before replacing its latest file', () => {
    const f = fixture(), report = comparisonReport(f.directory, f.plan), file = path.join(f.directory, 'report.json');
    writeComparisonReport(file, report); const before = fs.readFileSync(file, 'utf8');
    writeComparisonReport(file, { ...report, generatedAt: report.generatedAt + 1 });
    expect(fs.existsSync(`${file}.history`)).toBe(false);
    fs.writeFileSync(path.join(f.directory, 'batch.json'), JSON.stringify({ jobs: [] }));
    expect(comparisonReportFreshness(f.directory, f.plan, report).freshness).toBe('stale');
    f.state.turns = 2; f.save();
    const previous = fs.readFileSync(file, 'utf8');
    writeComparisonReport(file, comparisonReport(f.directory, f.plan));
    const history = fs.readdirSync(`${file}.history`);
    expect(history).toHaveLength(1);
    expect(fs.readFileSync(path.join(`${file}.history`, history[0]), 'utf8')).toBe(previous);
    expect(JSON.parse(before).runs[0].status).toBe('limit_reached');
  });

  it('checks a saved report through the CLI without modifying run or report files', async () => {
    const f = fixture(), file = path.join(f.directory, 'report.json');
    writeComparisonReport(file, comparisonReport(f.directory, f.plan));
    f.state.tokenBudget = buildTokenBudget(0, []); f.pass();
    const before = [file, f.stateFile, f.output].map(name => fs.readFileSync(name));
    const log = vi.spyOn(console, 'log').mockImplementation(() => {});
    await expect(compareMathRuns(['--phase', 'check-report', '--directory', f.directory])).resolves.toBe(0);
    expect(JSON.parse(String(log.mock.calls.at(-1)![0]))).toMatchObject({ freshness: 'stale', runs: [{
      current: { observation: { status: 'evaluated_passed' } } }] });
    expect([file, f.stateFile, f.output].map(name => fs.readFileSync(name))).toEqual(before);
    expect(fs.existsSync(`${file}.history`)).toBe(false);
  });
});
