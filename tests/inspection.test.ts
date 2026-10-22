import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { afterEach, describe, expect, it } from 'vitest';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import { buildRunInspection, exportRunPlan, readRunInspection, renderRunInspection } from '../src/solver/inspection';
import { queueRunEdit } from '../src/solver/humanEdit';
import { taskVersion, type TaskRecord } from '../src/solver/tasks';
import type { TaskProof } from '../src/solver/cooperativeProof';
import { researchFailureCategory } from '../src/solver/modules/search';
import type { RequestUsageAccounting } from '../src/solver/usageBudget';
import { researchHandoffs, resolveResearchHandoffs } from '../src/solver/researchHandoffs';

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
  it('uses saved dispatch state for concurrency and hides tasks left over from an idle session', () => {
    const { state, stateFile } = fixture();
    state.workers![0].phase = 'checking';
    state.workers![0].sessionTaskId = 'old-finished-task';
    state.workers![0].scheduling = { status: 'idle', since: 1000 };
    state.workers![1].scheduling = { status: 'working', since: 1001, action: 'task', taskId: 'goal' };
    writeSolverRunState(stateFile, state);
    const report = buildRunInspection(readSolverRunState(stateFile));
    expect(report.scheduling).toMatchObject({ observedWorkers: 2, working: 1, proofAssignments: 1, idle: 1 });
    expect(report.workers[0].task).toBeUndefined();
    expect(report.workers[1].task).toBe('goal');
    expect(renderRunInspection(report)).toContain('| solver | lead | — | idle | checking |');
  });

  it('shows pinned knowledge activation and observations after restore without claiming current proof acceptance', () => {
    const { state, stateFile } = fixture(), consumer = state.cooperation!.tasks[0]!.task;
    expect(buildRunInspection(state).knowledge).toMatchObject({ status: 'disabled', retrievalCoverage: 'unknown' });
    state.knowledgeDigest = 'c'.repeat(64);
    state.knowledgeRetrievals = { dropped: 2, observations: [{ sectionId: 'knowledge:query', catalogDigest: state.knowledgeDigest,
      searchInputDigest: 'query', consumer: { taskId: consumer.id, taskDigest: taskVersion(consumer) },
      candidateIds: ['saved-theorem'], routeFindingIds: [], included: true, workerId: 'engineer', workerTurn: 1,
      runTurn: 1, contextDigest: 'context', at: 1234 }] };
    state.knowledgeUses = [{ id: 'saved-theorem', catalogDigest: state.knowledgeDigest,
      consumer: { taskId: consumer.id, taskDigest: taskVersion(consumer) }, declaration: { name: 'Original.bridge', file: 'Submission.lean' },
      status: 'checked-reference', attribution: 'model-reported-origin', checkedCommit: 'fixed-commit', checkedSourceDigest: 'fixed-source',
      workerId: 'engineer', commit: 'fixed-commit' }];
    writeSolverRunState(stateFile, state);
    const restored = readSolverRunState(stateFile), report = buildRunInspection(restored), markdown = renderRunInspection(report);
    expect(restored.knowledgeUses).toEqual(state.knowledgeUses);
    expect(report.knowledge).toMatchObject({ status: 'enabled', retrievalCoverage: 'recorded', droppedRetrievals: 2,
      originalUses: [{ status: 'checked-reference', attribution: 'model-reported-origin' }] });
    expect(markdown).toContain('Knowledge observations');
    expect(markdown).toContain('| enabled | recorded | 1 | 0 | 0 | 1 |');
    expect(markdown).toContain('not historical authorship or current acceptance');
    expect(report.progress.checkedProofTasks).toBe(0);
  });

  it('keeps protocol failures separate from mathematical proof failures', () => {
    const { state } = fixture();
    state.cooperation!.tasks[0].attempts = 48;
    state.cooperation!.tasks[0].feedback = 'math_codex_rpc_failed:-32600:turn/start';
    const report = buildRunInspection(state);
    expect(report.tasks[0]).toMatchObject({ attempts: 48, feedbackCategory: 'protocol', proof: { status: 'none' } });
    expect(report.snapshot.stateDigest).toMatch(/^[a-f0-9]{64}$/u);
    expect(researchFailureCategory('math_delivery_invalid_json')).toBe('protocol');
    expect(researchFailureCategory('math_research_delivery_invalid')).toBe('protocol');
    expect(researchFailureCategory('math_review_delivery_invalid')).toBe('protocol');
    expect(researchFailureCategory('unsolved goals')).toBe('proof');
  });

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

  it.each(['math_total_token_limit', 'math_model_usage_unavailable', 'math_initial_planning_limit'])
  ('reports %s as budget stopping without changing proof progress', reason => {
    const { state } = fixture();
    state.workers![0].error = reason;
    state.workers![0].lastFailure = { at: 1234, reason };
    const report = buildRunInspection(state);
    expect(report.workers[0]).toMatchObject({ failureCategory: 'budget', lastFailure: { reason, category: 'budget' } });
    expect(report.progress).toMatchObject({ checkedProofTasks: 0, completedResearchTasks: 0, openProofTasks: ['goal'] });
    expect(renderRunInspection(report)).toContain(`| solver | budget | ${reason} |`);
    expect(researchFailureCategory('math_model_request_stopped')).toBe('unknown');
    expect(researchFailureCategory(`HTTP 403 Forbidden; ${reason}`)).toBe('authentication');
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

  it.each(['provider-observed-dispatch-limit', 'provider-observed-upstream-request-limit'] as const)
  ('preserves archived %s enforcement when inspecting reported usage', enforcement => {
    const f = fixture();
    for (const [index, worker] of f.state.workers!.entries()) {
      worker.usage = { totalTokens: (index + 1) * 20 };
      worker.usageAccounting = { startedTurns: worker.turns, reportedTurns: worker.turns, pending: false, incomplete: false };
    }
    f.state.usage = { totalTokens: 60 };
    f.state.tokenBudget = { maxTotalTokens: 100, enforcement, status: 'available', reportedTotalTokens: 60,
      usageComplete: true, overrunTokens: 0 };
    writeSolverRunState(f.stateFile, f.state);
    const before = fs.readFileSync(f.stateFile), { state } = readRunInspection(f.run);
    expect(state.tokenBudget).toEqual(f.state.tokenBudget);
    expect(buildRunInspection(state).tokenBudget).toEqual(f.state.tokenBudget);
    expect(fs.readFileSync(f.stateFile)).toEqual(before);
  });

  it.each<{
    scope: 'single' | 'workers'; accounting: RequestUsageAccounting;
    status: 'available' | 'usage-unavailable'; complete: boolean;
  }>([
    { scope: 'single', accounting: { startedRequests: 3, reportedRequests: 3, pendingRequests: 0, incomplete: false },
      status: 'available', complete: true },
    { scope: 'workers', accounting: { startedRequests: 3, reportedRequests: 2, pendingRequests: 1, incomplete: false },
      status: 'available', complete: false },
    { scope: 'single', accounting: { startedRequests: 3, reportedRequests: 2, pendingRequests: 0, incomplete: true },
      status: 'usage-unavailable', complete: false },
    { scope: 'workers', accounting: { startedRequests: 3, reportedRequests: 2, pendingRequests: 0, incomplete: false },
      status: 'usage-unavailable', complete: false },
  ])('retains $scope request receipts across checkpoint reads (status: $status, complete: $complete)', ({ scope, accounting, status, complete }) => {
    const f = fixture();
    if (scope === 'single') { f.state.workers = undefined; f.state.workerCount = 1; }
    else f.state.workers![1].turns = 0;
    const record = scope === 'single' ? f.state : f.state.workers![0];
    record.turns = 1;
    record.usage = { totalTokens: 40 };
    record.usageAccounting = { startedTurns: 1, reportedTurns: 0, pending: false, incomplete: true };
    record.requestUsageAccounting = accounting;
    f.state.tokenBudget = { maxTotalTokens: 100, enforcement: 'provider-observed-upstream-request-limit',
      status: 'available', reportedTotalTokens: 40, usageComplete: true, overrunTokens: 0 };
    writeSolverRunState(f.stateFile, f.state);
    const { state } = readRunInspection(f.run), restored = scope === 'single' ? state : state.workers![0];
    expect(restored.requestUsageAccounting).toEqual(accounting);
    expect(buildRunInspection(state).tokenBudget).toMatchObject({
      enforcement: 'provider-observed-upstream-request-limit', reportedTotalTokens: 40, status, usageComplete: complete,
      ...(status === 'usage-unavailable' ? { reason: 'math_model_usage_unavailable' } : {}),
    });
  });

  it.each([
    { startedRequests: 1, reportedRequests: 2, pendingRequests: 0, incomplete: false },
    { startedRequests: 2, reportedRequests: 1, pendingRequests: 2, incomplete: false },
  ])('rejects impossible persisted request counts %j', accounting => {
    const f = fixture();
    f.state.workers![0].requestUsageAccounting = accounting;
    writeSolverRunState(f.stateFile, f.state);
    expect(() => readRunInspection(f.run)).toThrow('math_resume_state_invalid:workers.0.requestUsageAccounting');
  });

  it('preserves activity timestamps in checkpoints and exposes the current wait reason', () => {
    const f = fixture();
    f.state.workers![1].lastActivity = { at: 1234, event: 'lean_lock_waiting', itemType: 'commandExecution' };
    writeSolverRunState(f.stateFile, f.state);
    const { state } = readRunInspection(f.run);
    expect(buildRunInspection(state).workers[1].lastActivity).toEqual(f.state.workers![1].lastActivity);
    expect(renderRunInspection(buildRunInspection(state))).toContain('lean_lock_waiting');
  });

  it.each(['cooling-down', 'retrying', 'recovered'] as const)('reads and renders persisted %s recovery without treating old retries as pending', phase => {
    const f = fixture(), nextRetryAt = Date.UTC(2026, 9, 19, 1, 0);
    f.state.workers![1].recovery = { phase, reason: 'math_model_request_failed', cycles: 2,
      startedAt: nextRetryAt - 180_000, nextRetryAt, waitedMs: 60_000,
      ...(phase === 'recovered' ? { recoveredAt: nextRetryAt + 1_000 } : {}) };
    f.state.workers![1].lastFailure = { at: nextRetryAt - 1_000, reason: 'math_model_request_failed', taskId: 'goal' };
    writeSolverRunState(f.stateFile, f.state);
    const restored = readSolverRunState(f.stateFile), report = buildRunInspection(restored);
    expect(report.evidence).toBe('recorded-not-replayed');
    expect(report.workers[1].recovery).toEqual({ ...f.state.workers![1].recovery, category: 'network' });
    expect(report.workers[1].lastFailure?.reason).toBe('math_model_request_failed');
    expect(report.progress.checkedProofTasks).toBe(0);
    const markdown = renderRunInspection(report);
    expect(markdown).toContain('## Session recovery');
    expect(markdown).toContain(`| engineer | ${phase === 'recovered' ? 'recovered (history)' : phase} | network | math_model_request_failed | 2 |`);
    expect(markdown).toContain('60000 |');
    if (phase === 'cooling-down') expect(markdown).toContain(new Date(nextRetryAt).toISOString());
    else expect(markdown).not.toContain(new Date(nextRetryAt).toISOString());
    expect(markdown).toContain('does not rerun Lean');
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

  it('reports adoption and planned use independently from proof evidence after JSON restore', () => {
    const { state, stateFile } = fixture(), cooperative = state.cooperation!;
    const source: TaskRecord = { task: { id: 'investigation', kind: 'research', objective: 'Find a bridge',
      dependsOn: [], revision: 0 }, status: 'completed', attempts: 1 };
    const adopted: TaskRecord = { task: { id: 'bridge', kind: 'lemma', objective: 'Prove the bridge', dependsOn: [],
      revision: 0, theoremName: 'Original.bridge', proofPath: 'Submission.lean', type: 'True' }, status: 'pending', attempts: 0 };
    cooperative.tasks.push(source, adopted);
    cooperative.deliveries = [{ id: 'proposal', producer: 'researcher', taskId: source.task.id,
      taskDigest: taskVersion(source.task), kind: 'research', status: 'advisory', summary: 'A reusable bridge.',
      statement: '', premises: [], dependencies: [], remainingObligations: [], evidenceRefs: [], createdAt: 1,
      lemmaRequests: [adopted.task] }];
    const handoff = researchHandoffs(cooperative)[0];
    cooperative.researchDecisions = resolveResearchHandoffs(cooperative, [handoff.id], cooperative.tasks.map(item => item.task), undefined);
    state.knowledgeDigest = 'c'.repeat(64);
    writeSolverRunState(stateFile, state);
    const restored = readSolverRunState(stateFile), before = JSON.stringify(restored), report = buildRunInspection(restored);
    expect(report.configuration.knowledgeDigest).toBe(state.knowledgeDigest);
    expect(report.continuation.adoptedResearch).toEqual([expect.objectContaining({ sourceTaskId: source.task.id,
      taskId: adopted.task.id, recordedProof: 'none', plannedGoalIds: [], referenceCoverage: 'unknown' })]);
    expect(report.progress.checkedProofTasks).toBe(0);
    expect(renderRunInspection(report)).toContain('| investigation | bridge | none | none | none recorded | none recorded | none recorded | unknown |');
    expect(JSON.stringify(restored)).toBe(before);
    restored.cooperation!.tasks[0].task.dependsOn = [adopted.task.id];
    expect(buildRunInspection(restored).continuation.adoptedResearch[0].plannedGoalIds).toEqual(['goal']);
  });

  it.each(['proof', 'integratedCheck'] as const)('recognizes %s receipts bound to a verification projection', field => {
    const { state } = fixture(), node = state.cooperation!.tasks[0];
    const targetCommit = 'c'.repeat(40);
    const proof = { taskDigest: taskVersion(node.task), passed: true, commit: 'b'.repeat(40), sourceDigest: 'source',
      verification: { status: 'kernel_verified', targetCommit, results: [
        { status: 'kernel_verified', targetCommit, receiptId: 'projection-receipt' },
      ] }, changes: [], seedCommit: 'a'.repeat(40) } as TaskProof;
    node[field] = proof;
    const report = buildRunInspection(state);
    expect(report.tasks[0].proof).toMatchObject({ status: 'checked', commit: proof.commit, receiptIds: ['projection-receipt'] });
    expect(report.progress).toMatchObject({ checkedProofTasks: 1, openProofTasks: [] });
    proof.conditions = [{ taskId: 'helper', taskDigest: 'helper-v1' }];
    expect(buildRunInspection(state).progress.conditionalProofTasks).toBe(1);
    proof.verification.results[0].targetCommit = proof.commit;
    expect(buildRunInspection(state).tasks[0].proof.status).toBe('unverified');
    proof.verification.targetCommit = '';
    proof.verification.results[0].targetCommit = '';
    expect(buildRunInspection(state).tasks[0].proof.status).toBe('unverified');
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

  it('shows each alternative branch parking without parking the entire original goal or hiding its frontier', () => {
    const { state } = fixture(), goal = state.cooperation!.tasks[0]; goal.status = 'pending';
    const input: TaskRecord = { task: { id: 'input', kind: 'lemma', objective: 'Needed lemma', dependsOn: [], revision: 0,
      theoremName: 'Original.input', proofPath: 'Submission.lean', type: 'True' }, status: 'pending', attempts: 0 };
    const closing: TaskRecord = { task: { ...input.task, id: 'closing', theoremName: 'Original.closing', dependsOn: ['input'] },
      status: 'pending', attempts: 0 };
    goal.alternativeRoutes = [{ id: 'branch', targetTaskId: 'goal', prerequisiteTaskIds: ['input'], closingTaskId: 'closing' }];
    goal.parkedRoutes = { branch: ['branch-blocker'] }; goal.routeParking = [];
    state.cooperation!.tasks.push(input, closing); state.cooperation!.proofRoutes = [...goal.alternativeRoutes];
    state.cooperation!.blockers = [{ id: 'branch-blocker', taskId: 'goal', taskDigest: taskVersion(goal.task), groupId: 'main',
      routeId: 'branch', mechanism: 'missing estimate', scope: 'this closing implication', evidenceStatus: 'advisory',
      evidenceRefs: [], reopenOn: [{ kind: 'contract-changed' }], basis: { contractDigest: 'contract',
        environmentDigest: state.environmentDigest, dependencies: {} }, fingerprint: 'fingerprint', count: 2,
      status: 'parked', createdAt: 1, updatedAt: 2 }];
    const report = buildRunInspection(state), markdown = renderRunInspection(report);
    expect(report.tasks.find(task => task.id === 'goal')).toMatchObject({ parkedBy: [], parkedRoutes: { branch: ['branch-blocker'] } });
    expect(report.continuation.goals[0].alternatives![0]).toMatchObject({ frontier: ['input'], parkedBy: ['branch-blocker'] });
    expect(report.mathematics.snapshot.routes[0]).toMatchObject({ routeId: 'branch', ready: false, parkedBy: ['branch-blocker'] });
    expect(markdown).toContain('| branch | goal | input | input | closing | none | false | parked | branch-blocker | awaiting-original-check |');
    expect(markdown).toContain('| branch-blocker | goal | branch | missing estimate |');
    expect(markdown).toContain('Alternative branch branch parked by local blockers: branch-blocker');
    expect(markdown).toContain('Other branches can continue.');
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
