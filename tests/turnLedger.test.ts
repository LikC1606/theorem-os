import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, describe, expect, it, vi } from 'vitest';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import { MODEL_TURN_LEDGER_LIMIT, recoverModelTurnLedger, WorkerTurnLedger } from '../src/solver/turnLedger';
import { recordThreadUsage } from '../src/solver/usageBudget';
import { taskVersion, type CooperativeAction, type TaskRecord } from '../src/solver/tasks';
import type { TaskProof } from '../src/solver/cooperativeProof';

const roots: string[] = [];
afterEach(() => { for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });
const node = (id: string, kind: TaskRecord['task']['kind'] = 'lemma', dependsOn: string[] = []): TaskRecord => ({
  task: { id, kind, objective: id, dependsOn, revision: 0, proofPath: 'Submission.lean', theoremName: id, type: 'True' },
  status: 'pending', attempts: 0,
});
const checked = (record: TaskRecord) => {
  record.status = 'integrated';
  record.integratedCheck = { taskDigest: taskVersion(record.task), passed: true, commit: 'checked', sourceDigest: 'source',
    changes: [], conditions: [], seedCommit: 'seed', verification: { status: 'kernel_verified', targetCommit: 'projection', results: [
      { status: 'kernel_verified', targetCommit: 'projection', receiptId: 'receipt-' + record.task.id },
    ] }, references: { root: { file: record.task.proofPath!, name: record.task.theoremName! },
      environmentDigest: 'env', sourceCommit: 'projection', contextDigest: 'context', inputs: [], tasks: [], statement: [], proof: [] } } as TaskProof;
};
const fixture = () => {
  const question = node('question', 'research');
  question.task = { ...question.task, proofPath: undefined, theoremName: undefined, type: undefined };
  const state = { schema: 'deepscientist.math.solver.v1', runId: 'ledger-fixture', worktree: '/fixture', phase: 'running',
    model: 'fixture', effort: 'fixture', taskDigest: 'task', buildDigest: 'build', environmentDigest: 'env', evaluatorDigest: 'evaluator',
    turns: 1, usageAccounting: { startedTurns: 0, reportedTurns: 0, pending: false, incomplete: false },
    problem: { workspace: '/fixture', receiptDigest: 'problem' },
    cooperation: { tasks: [question, node('goal', 'goal', ['question']), node('unrelated', 'goal')] },
  } as unknown as SolverRunState;
  const action: Extract<CooperativeAction, { kind: 'task' }> = { kind: 'task', task: question.task,
    assignment: { taskId: question.task.id, taskDigest: taskVersion(question.task), workerId: 'peer', assignmentId: 'dispatch-1',
      routeId: 'route-a', groupId: 'main', seedCommit: 'a'.repeat(40) } };
  question.assignment = action.assignment;
  const emit = vi.fn(), ledger = new WorkerTurnLedger(state, 'peer', state, emit);
  const report = (totalTokens: number, sessionId = 'session') => ledger.usage(sessionId, recordThreadUsage(state, { totalTokens }));
  return { state, action, question, ledger, emit, report, receipt: () => state.turnLedger!.turns.at(-1)! };
};

describe('model turn consumption and retained evidence ledger', () => {
  it('keeps the immutable assignment identity and observes cumulative deltas without claiming exact attribution', () => {
    const { state, action, ledger, receipt, report } = fixture();
    state.usage = { totalTokens: 40 }; state.usageAccounting!.startedTurns = 1;
    ledger.begin('session', 'thread', 'direct', action); ledger.started('provider-turn');
    action.assignment.routeId = 'later-route';
    for (const total of [50, 100, 100]) report(total);
    ledger.finish('completed'); ledger.settle();
    expect(receipt()).toMatchObject({ workerId: 'peer', threadId: 'thread', turnId: 'provider-turn', execution: 'completed',
      scope: { taskId: 'question', assignmentId: 'dispatch-1', routeId: 'route-a', taskDigest: taskVersion(action.task) },
      usage: { basis: 'provider-thread-window', attribution: 'unverified', coverage: 'reported',
        beforeTotalTokens: 40, afterTotalTokens: 100, observedDeltaTokens: 60, reportedUpdates: 3 }, outcomeStatus: 'recorded' });
    expect(receipt().outcome!.retainedWork.value).toBe('not-assessed');
  });

  it('does not turn missing reports or repeated cumulative totals into known zero-cost work', () => {
    const { state, ledger, receipt, report } = fixture();
    ledger.begin('session', 'thread', 'direct'); ledger.finish('completed'); ledger.settle();
    expect(receipt().usage).toMatchObject({ coverage: 'unknown', afterTotalTokens: null, observedDeltaTokens: null });
    state.usage = { totalTokens: 20 }; state.usageAccounting!.startedTurns = 1;
    ledger.begin('session', 'thread', 'direct'); report(20); ledger.finish('completed'); ledger.settle();
    expect(receipt().usage).toMatchObject({ coverage: 'partial', observedDeltaTokens: 0 });
    expect(receipt().usage.uncertainReasons).toEqual(expect.arrayContaining(['prior-turn-usage-incomplete', 'unchanged-thread-total']));
  });

  it('retains partial failed consumption and leaves a late update unallocated to a new session', () => {
    const { state, ledger, receipt, report, emit } = fixture();
    ledger.begin('session', 'thread', 'direct'); report(10); ledger.finish('failed'); ledger.settle();
    const failed = receipt();
    state.usageAccounting!.startedTurns = 1;
    ledger.begin('fresh-session', 'fresh-thread', 'direct');
    report(30);
    ledger.finish('completed'); ledger.settle();
    expect(failed.usage).toMatchObject({ coverage: 'partial', observedDeltaTokens: 10 });
    expect(failed.usage.uncertainReasons).toContain('late-or-unscoped-usage-report');
    expect(receipt().usage).toMatchObject({ coverage: 'unknown', observedDeltaTokens: null });
    expect(receipt().usage.uncertainReasons).toContain('cross-session-usage-report');
    expect(state.turnLedger!.unscopedReports).toBe(1);
    expect(emit).toHaveBeenCalledWith('model_turn_ledger_updated', expect.objectContaining({ receipt: expect.objectContaining({ id: failed.id }) }));
  });

  it('keeps late same-thread reports ambiguous and marks regressive totals incomplete', () => {
    const { state, ledger, receipt, report } = fixture();
    ledger.begin('session', 'thread', 'direct'); report(10); ledger.finish('completed'); ledger.settle();
    report(25);
    expect(receipt().usage.coverage).toBe('partial');
    state.usageAccounting!.startedTurns = 1;
    ledger.begin('session', 'thread', 'direct'); report(15); ledger.finish('completed'); ledger.settle();
    expect(receipt().usage).toMatchObject({ coverage: 'unknown', observedDeltaTokens: null });
    expect(receipt().usage.uncertainReasons).toContain('invalid-or-regressive-usage-report');
    expect(state.usage!.totalTokens).toBe(25);
  });

  it('retains advisory drafts, negative route reports and failed-input fingerprints without scoring them as proof progress', () => {
    const { state, action, question, ledger, receipt } = fixture();
    ledger.begin('session', 'thread', 'direct', action);
    const taskDigest = taskVersion(question.task), commit = 'b'.repeat(40);
    state.cooperation!.researchDrafts = { question: { taskDigest, workerId: 'peer', assignmentId: 'dispatch-1',
      seedCommit: 'a'.repeat(40), commit, outputDigest: 'notes-changed', artifacts: { scope: 'advisory-unverified' } as never } };
    state.cooperation!.researchCheckpoints = { question: { taskDigest, inputDigest: 'input', outputDigest: 'output', count: 1,
      paused: false, candidateStatus: 'candidate' } as never };
    state.cooperation!.deliveries = [{ id: 'negative-finding', producer: 'peer', taskId: 'question', taskDigest, kind: 'research',
      status: 'advisory', commit, dependencies: [], summary: 'The proposed estimate has a boundary counterexample.',
      findingDigest: 'negative-finding-digest', evidenceRefs: ['RESEARCH.md'] } as never];
    state.cooperation!.blockers = [{ id: 'negative-route', taskId: 'question', taskDigest, status: 'open', mechanism: 'counterexample',
      scope: 'uniform estimate', evidenceRefs: ['RESEARCH.md'], count: 1, evidenceStatus: 'advisory', basis: {}, reopenOn: [] } as never];
    state.cooperation!.failedTaskInputs = [{ id: 'failed-source', taskId: 'question', taskDigest, attemptFingerprint: 'local-inference',
      relatedFailureIds: ['older-failure'], feedback: 'The trial failed.' } as never];
    ledger.finish('interrupted'); ledger.settle();
    expect(receipt().outcome).toMatchObject({ acceptance: 'not-assessed', observedProgress: { obligations: { closed: [] } },
      retainedWork: { value: 'not-assessed', drafts: [{ commit, evidenceStatus: 'advisory-unverified' }],
        blockers: [{ id: 'negative-route', evidenceStatus: 'advisory' }], deliveries: [{ id: 'negative-finding' }],
        checkpoint: { candidateStatus: 'candidate', evidenceStatus: 'candidate-not-scored' },
        failedInputs: [{ id: 'failed-source', attemptFingerprint: 'local-inference', relatedFailureIds: ['older-failure'] }] } });
    expect(question.proof).toBeUndefined(); expect(question.integratedCheck).toBeUndefined();
  });

  it('separates the assignment cone from unrelated concurrent proofs and replacement task versions', () => {
    const { state, action, ledger, receipt } = fixture();
    ledger.begin('session', 'thread', 'direct', action);
    checked(state.cooperation!.tasks.find(node => node.task.id === 'unrelated')!);
    ledger.finish('completed'); ledger.settle();
    expect(receipt().outcome!.observedProgress).toMatchObject({ scope: 'assignment-cone', obligations: { closed: [] } });
    const goal = state.cooperation!.tasks.find(node => node.task.id === 'goal')!;
    ledger.begin('session', 'thread', 'direct', action);
    checked(goal);
    ledger.finish('completed'); ledger.settle();
    expect(receipt().outcome!.observedProgress.obligations.closed).toEqual(['goal']);
    expect(receipt().outcome!.attribution).toBe('observed-not-causal');
    expect(receipt().outcome!.retainedWork.deliveries).toEqual([]);
    ledger.begin('session', 'thread', 'direct', action);
    const question = state.cooperation!.tasks[0]; question.task = { ...question.task, revision: 1 };
    ledger.finish('completed'); ledger.settle();
    expect(receipt().outcome!.observedProgress.taskVersionMatches).toBe(false);
    expect(receipt().outcome!.observedProgress.obligations.closed).toEqual([]);
  });

  it('recovers unfinished persisted windows without assigning their missing usage or later evidence', () => {
    const { state, ledger, receipt, report } = fixture();
    ledger.begin('session', 'thread', 'direct'); report(15);
    const root = fs.mkdtempSync(path.join(os.tmpdir(), 'turn-ledger-')); roots.push(root);
    const file = path.join(root, 'state.json'); writeSolverRunState(file, state);
    const restored = readSolverRunState(file); recoverModelTurnLedger(restored, () => {});
    expect(restored.turnLedger!.turns[0]).toMatchObject({ execution: 'recovered', usage: { coverage: 'partial', observedDeltaTokens: 15 },
      outcomeStatus: 'unavailable-after-restart' });
    expect(restored.turnLedger!.turns[0].outcome).toBeUndefined();
    expect(restored.turnLedger!.turns[0].settledAt).toBeTypeOf('number');
    expect(receipt().execution).toBe('running');
    restored.usageAccounting = { startedTurns: 1, reportedTurns: 0, pending: false, incomplete: true };
    const resumed = new WorkerTurnLedger(restored, 'peer', restored, () => {});
    resumed.begin('new-session-id', 'thread', 'direct');
    resumed.usage('new-session-id', recordThreadUsage(restored, { totalTokens: 40 }));
    resumed.finish('completed'); resumed.settle();
    expect(restored.turnLedger!.turns[1].usage).toMatchObject({ coverage: 'partial', observedDeltaTokens: 25, attribution: 'unverified' });
    expect(restored.turnLedger!.turns[1].usage.uncertainReasons).toContain('prior-thread-usage-incomplete');
  });

  it('archives proof deliveries that have no advisory evidence references', () => {
    const { state, ledger, receipt } = fixture();
    ledger.begin('session', 'thread', 'direct');
    state.cooperation!.deliveries = [{ id: 'proof-delivery', producer: 'peer', taskId: 'goal',
      taskDigest: taskVersion(state.cooperation!.tasks[1].task), kind: 'proof', status: 'verified',
      commit: 'b'.repeat(40), dependencies: [], summary: 'A checked helper.' } as never];
    ledger.finish('completed'); ledger.settle();
    expect(receipt().outcome!.retainedWork.deliveries[0].evidenceRefs).toEqual([]);
    const root = fs.mkdtempSync(path.join(os.tmpdir(), 'turn-ledger-')); roots.push(root);
    const file = path.join(root, 'state.json'); writeSolverRunState(file, state);
    expect(readSolverRunState(file).turnLedger!.turns[0].outcome).toEqual(receipt().outcome);
    expect(receipt().outcome!.acceptance).toBe('not-assessed');
  });

  it('keeps a bounded state tail while emitting immutable receipts for every turn', () => {
    const { state, ledger, emit } = fixture();
    for (let index = 0; index < MODEL_TURN_LEDGER_LIMIT + 2; index++) {
      ledger.begin('session', 'thread', 'direct'); ledger.finish('completed'); ledger.settle();
    }
    expect(state.turnLedger).toMatchObject({ retainedLimit: MODEL_TURN_LEDGER_LIMIT, dropped: 2 });
    expect(state.turnLedger!.turns).toHaveLength(MODEL_TURN_LEDGER_LIMIT);
    expect(emit.mock.calls.filter(([event]) => event === 'model_turn_ledger_recorded')).toHaveLength(MODEL_TURN_LEDGER_LIMIT + 2);
    expect(emit.mock.calls[0][1].receipt.execution).toBe('running');
  });

  it('bounds completed history even while the oldest concurrent model call remains active', () => {
    const { state, ledger, receipt } = fixture();
    ledger.begin('slow-session', 'slow-thread', 'direct');
    const active = receipt(), peer = new WorkerTurnLedger(state, 'other-peer', state, () => {});
    for (let index = 0; index < MODEL_TURN_LEDGER_LIMIT + 2; index++) {
      peer.begin('peer-session', 'peer-thread', 'direct'); peer.finish('completed'); peer.settle();
    }
    expect(state.turnLedger!.turns).toHaveLength(MODEL_TURN_LEDGER_LIMIT);
    expect(state.turnLedger!.dropped).toBe(3);
    expect(state.turnLedger!.turns[0]).toBe(active);
    expect(active.execution).toBe('running');
    ledger.finish('completed'); ledger.settle();
    expect(active.outcomeStatus).toBe('recorded');
  });
});
