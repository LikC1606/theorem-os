import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { afterEach, describe, expect, it } from 'vitest';
import { writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import { buildRunInspection, exportRunPlan, readRunInspection, renderRunInspection } from '../src/solver/inspection';
import { queueRunEdit } from '../src/solver/humanEdit';
import { taskVersion } from '../src/solver/tasks';
import type { TaskProof } from '../src/solver/cooperativeProof';
import { researchFailureCategory } from '../src/solver/modules/search';

const roots: string[] = [];
function fixture() {
  const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'math-inspect-'))); roots.push(root);
  const run = path.join(root, 'result.json'), stateFile = `${run}.runtime/state.json`;
  fs.mkdirSync(path.dirname(stateFile), { mode: 0o700 });
  const task = { id: 'goal', kind: 'goal' as const, objective: 'Prove the original goal', dependsOn: [], revision: 0,
    theoremName: 'Original.goal', proofPath: 'Submission.lean' };
  const state: SolverRunState = {
    schema: 'deepscientist.math.solver.v1', runId: 'example-run', taskDigest: 'task', buildDigest: 'build',
    environmentDigest: 'environment', evaluatorDigest: 'evaluation', model: 'gpt-6.1-sol', effort: 'xhigh',
    worktree: path.join(root, 'worktree'), phase: 'running', turns: 3, workerCount: 2,
    workers: [{ id: 'solver', role: 'lead', worktree: root, phase: 'running', turns: 1 },
      { id: 'engineer', role: 'engineer', worktree: root, phase: 'running', turns: 2 }],
    problem: { kind: 'imo2026', workspace: root, projectRelative: 'generated/example', baseCommit: 'a'.repeat(40),
      receiptDigest: 'problem', activeProblemPath: path.join(root, 'active-problem.json'),
      contract: { problemId: 'example', informalStatement: 'Prove the original goal.', formalStatement: 'theorem goal : True := by sorry',
        assumptions: [], knownTraps: [], acceptanceCriteria: [], statementHash: 's', leanStatementHash: 'l', officialVerificationCommand: 'lean' },
      targets: [{ proofPath: 'Submission.lean', theoremName: 'Original.goal', declarationHash: 'declaration' }],
      ownedFiles: ['Submission.lean'], trustedFiles: {}, declarations: {}, sourceStructure: {} },
    cooperation: { planVersion: 'version-1', canonicalCommit: 'b'.repeat(40),
      tasks: [{ task, status: 'running', attempts: 1 }], groups: [{ group: {
        id: 'main', objective: 'Original proof', status: 'active', revision: 0, engineerId: 'engineer' }, turns: 2 }] },
  };
  writeSolverRunState(stateFile, state);
  return { root, run, stateFile, state };
}
afterEach(() => { for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });

describe('run inspection', () => {
  it('reports infrastructure failures and dispatches without counting them as mathematical progress', () => {
    const { state } = fixture();
    state.cooperation!.tasks[0].attempts = 12;
    state.workers![1].lastFailure = { at: 1234, reason: 'math_model_request_failed', taskId: 'goal' };
    state.workers![1].error = 'math_lean_toolchain_unavailable';
    const report = buildRunInspection(state);
    expect(report.progress).toMatchObject({ checkedProofTasks: 0, completedResearchTasks: 0, openProofTasks: ['goal'] });
    expect(report.workers[1]).toMatchObject({ failureCategory: 'environment', lastFailure: { category: 'network' } });
    expect(renderRunInspection(report)).toContain('dispatches (including retries): 12');
    expect(researchFailureCategory('unsolved goals')).toBe('proof');
    expect(researchFailureCategory('math_original_context_changed')).toBe('source');
    expect(researchFailureCategory('math_model_authentication_failed')).toBe('authentication');
    expect(researchFailureCategory('math_model_concurrency_limit')).toBe('rate_limit');
    expect(researchFailureCategory('math_verifier_unavailable')).toBe('environment');
    expect(researchFailureCategory('math_codex_provider_unreachable')).toBe('network');
  });

  it('reads a running checkpoint without a final receipt and exports a versioned plan', () => {
    const f = fixture(), before = fs.readFileSync(f.stateFile);
    const { state, result } = readRunInspection(f.run);
    expect(result).toBeUndefined();
    expect(buildRunInspection(state).recordedOutcome).toBeUndefined();
    expect(exportRunPlan(state)).toMatchObject({ baseVersion: 'version-1', tasks: [{ id: 'goal' }] });
    expect(readRunInspection(f.stateFile).state.runId).toBe(state.runId);
    expect(fs.readFileSync(f.stateFile)).toEqual(before);
  });

  it('preserves activity timestamps in checkpoints and exposes the current wait reason', () => {
    const f = fixture();
    f.state.workers![1].lastActivity = { at: 1234, event: 'lean_lock_waiting', itemType: 'commandExecution' };
    writeSolverRunState(f.stateFile, f.state);
    const { state } = readRunInspection(f.run);
    expect(buildRunInspection(state).workers[1].lastActivity).toEqual(f.state.workers![1].lastActivity);
    expect(renderRunInspection(buildRunInspection(state))).toContain('lean_lock_waiting');
  });

  it('distinguishes stale, conditional and missing proof receipts', () => {
    const { state } = fixture(), node = state.cooperation!.tasks[0];
    const proof = { taskDigest: taskVersion(node.task), passed: true, commit: 'b'.repeat(40), sourceDigest: 'source',
      verification: { status: 'kernel_verified', targetCommit: 'b'.repeat(40), results: [] }, changes: [], seedCommit: 'a'.repeat(40) } as TaskProof;
    node.proof = proof;
    expect(buildRunInspection(state).tasks[0].proof.status).toBe('unverified');
    proof.verification.results.push({ status: 'kernel_verified', targetCommit: proof.commit, receiptId: 'recorded-receipt' } as TaskProof['verification']['results'][number]);
    expect(buildRunInspection(state).tasks[0].proof.status).toBe('checked');
    proof.conditions = [{ taskId: 'helper', taskDigest: 'helper-v1' }];
    expect(buildRunInspection(state).tasks[0].proof.status).toBe('conditional');
    node.task = { ...node.task, revision: 1 };
    expect(buildRunInspection(state).tasks[0].proof.status).toBe('stale');
  });

  it('keeps edit application separate from proof rechecks and renders escaped tables', () => {
    const { state } = fixture();
    state.problem.contract = { ...state.problem.contract, problemId: 'example|table' };
    state.cooperation!.edits = [{ id: 'human-1', status: 'applied', affectedTasks: ['goal'], recheck: { status: 'pending', tasks: [] } }];
    const report = renderRunInspection(buildRunInspection(state));
    expect(report).toContain('example\\|table');
    expect(report).toContain('| human-1 | applied | pending |');
    expect(report).toContain('does not rerun Lean');
    expect(report).not.toContain('evaluated_passed');
  });

  it('rejects unrelated results and hides results from an earlier phase or source version', () => {
    const f = fixture();
    fs.writeFileSync(f.run, JSON.stringify({ schema: 'deepscientist.math.run.v2', runId: 'other', stateFile: f.stateFile }));
    expect(() => readRunInspection(f.run)).toThrow('identity_mismatch');
    const result = { runId: f.state.runId, status: 'evaluated_passed', solution_commit: 'other-source', evaluator: { status: 'passed' } };
    expect(buildRunInspection(f.state, result).evaluator).toBeUndefined();
    f.state.phase = 'finished';
    expect(buildRunInspection(f.state, result).recordedOutcome).toBeUndefined();
  });

  it('exposes the CLI without invoking a model and refuses to overwrite an export', () => {
    const f = fixture(), exported = path.join(f.root, 'plan.json');
    const invoke = () => spawnSync('bun', ['bin/math.ts', 'inspect', '--run', f.run, '--format', 'plan', '--output', exported],
      { encoding: 'utf8', timeout: 10_000, maxBuffer: 16_384 });
    expect(invoke().status).toBe(0);
    expect(JSON.parse(fs.readFileSync(exported, 'utf8')).baseVersion).toBe('version-1');
    expect(invoke().status).toBe(1);
  });
});

describe('human plan edits', () => {
  it('validates and queues through the host log without changing the checkpoint', async () => {
    const f = fixture(), before = fs.readFileSync(f.stateFile);
    const plan = { ...exportRunPlan(f.state), id: 'pause-goal' };
    plan.tasks[0] = { ...plan.tasks[0], status: 'paused' };
    expect(await queueRunEdit(f.run, plan, true)).toMatchObject({ status: 'validated' });
    const log = path.join(path.dirname(f.stateFile), 'edits.jsonl');
    expect(fs.existsSync(log)).toBe(false);
    expect(await queueRunEdit(f.run, plan)).toMatchObject({ status: 'queued' });
    expect(JSON.parse(fs.readFileSync(log, 'utf8')).tasks[0].status).toBe('paused');
    expect(await queueRunEdit(f.run, plan)).toMatchObject({ status: 'already_queued' });
    expect(fs.readFileSync(log, 'utf8').trim().split('\n')).toHaveLength(1);
    expect(fs.readFileSync(f.stateFile)).toEqual(before);
    await expect(queueRunEdit(f.run, { ...plan, tasks: [{ ...plan.tasks[0], status: 'active' }] })).rejects.toThrow('id_conflict');
  });

  it('rejects stale versions, cyclic plans and missing original goals before appending', async () => {
    const f = fixture(), plan = exportRunPlan(f.state);
    await expect(queueRunEdit(f.run, { ...plan, baseVersion: 'old' })).rejects.toThrow('version_conflict');
    await expect(queueRunEdit(f.run, { ...plan, tasks: [{ ...plan.tasks[0], dependsOn: ['goal'] }] })).rejects.toThrow('dependency_cycle');
    await expect(queueRunEdit(f.run, { ...plan, tasks: [{ id: 'research', kind: 'research', objective: 'Explore' }] })).rejects.toThrow('incomplete_original_coverage');
    await expect(queueRunEdit(f.run, { ...plan, tasks: [{ ...plan.tasks[0], ownerId: 'solver' }] })).rejects.toThrow('owner_unavailable');
    expect(fs.existsSync(path.join(path.dirname(f.stateFile), 'edits.jsonl'))).toBe(false);
  });

  it('rejects linked or partially written logs instead of appending to them', async () => {
    const f = fixture(), log = path.join(path.dirname(f.stateFile), 'edits.jsonl');
    const other = path.join(f.root, 'other'); fs.writeFileSync(other, 'outside'); fs.symlinkSync(other, log);
    await expect(queueRunEdit(f.run, exportRunPlan(f.state))).rejects.toThrow();
    expect(fs.readFileSync(other, 'utf8')).toBe('outside');
    fs.unlinkSync(log); fs.writeFileSync(log, '{"id":');
    await expect(queueRunEdit(f.run, exportRunPlan(f.state))).rejects.toThrow('incomplete_log');
  });
});
