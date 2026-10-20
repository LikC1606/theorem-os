import fs from 'node:fs';
import path from 'node:path';
import { afterEach, describe, expect, it, vi } from 'vitest';
import type { MathAgentOptions, MathAgentSession } from '../src/runtime/codexSession';
import { directSolverModules } from '../src/solver/modules';
import type { SolverModules } from '../src/solver/modules';
import type { ProofCheck } from '../src/solver/modules/evidence';
import { commitSolverSources } from '../src/solver/problem';
import { runResearchWorkers } from '../src/solver/research';
import { workerAccess } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';

vi.mock('../src/math/mathBuildManifest', () => ({ readMathBuildManifest: vi.fn() }));
const roots: string[] = [];
afterEach(() => { vi.restoreAllMocks(); for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });
function fixture(cooperative = false) {
  const example = localExample('turn-ledger-research-', 'lead'), { directory, workspace, problem } = example; roots.push(directory);
  const workers = [leadWorker(problem, workspace), ...cooperative ? [peerWorker(example, 'peer')] : []];
  const state = solverState(problem, workspace, { runId: 'turn-ledger-integration', model: 'fixture', effort: 'fixture', phase: 'running',
    ...(cooperative ? { workers: workers.map(worker => ({ ...worker, phase: 'running' as const, turns: 0 })),
      cooperation: { canonicalCommit: problem.baseCommit, groups: [{ group: { id: 'main', objective: 'Prove originals',
        status: 'active' as const, revision: 0 }, turns: 0 }], tasks: [
        { task: { id: 'investigation', kind: 'research' as const, objective: 'Check the unresolved construction',
          ownerId: 'peer', dependsOn: ['goal_1'], revision: 0 }, status: 'pending' as const, attempts: 0 },
        ...problem.targets.map((target, index) => ({ task: { id: `goal_${index + 1}`, kind: 'goal' as const,
          objective: target.theoremName, proofPath: target.proofPath, theoremName: target.theoremName,
          status: 'paused' as const, dependsOn: [], revision: 0 }, status: 'pending' as const, attempts: 0 })),
      ] } } : {}) });
  const emit = vi.fn(), save = vi.fn();
  const run = (modules: SolverModules, maxTurns: number) => runResearchWorkers({ state, workers,
    access: workerAccess(workers, directory), modules,
    root: directory, buildFile: path.join(directory, 'mock-build.json'), taskText: 'Fixture', executable: 'unused-fixture', profile: 'unused-fixture',
    signal: new AbortController().signal, deadline: Infinity, maxTurnMs: Infinity, maxTurns, maxTotalTokens: 0, save, emit });
  const check = vi.fn(async (): Promise<ProofCheck> => {
    const commit = commitSolverSources(problem, workspace);
    return { commit, sourceDigest: 'source-' + commit, passed: false,
      verification: { schema: 'deepscientist.mathematics.verification-batch/v1', targetCommit: commit, status: 'failed',
        results: [{ status: 'failed', receiptId: 'failure-' + commit }], events: [], startedAt: 1, checkedAt: 2, durationMs: 1 } as never };
  });
  const modules = (open: (options: MathAgentOptions) => Promise<MathAgentSession>): SolverModules => ({ ...directSolverModules,
    M1: { ...directSolverModules.M1, open }, M2: { ...directSolverModules.M2, check,
      checkTask: async () => { throw new Error('fixture_unexpected_lean_check'); } },
    M3: { ...directSolverModules.M3, select: () => ({ operation: 'direct', reason: 'fixture' }),
      retry: (_error, attempts) => ({ attempt: attempts + 1, delayMs: 0, reason: 'math_model_tool_failed' }) },
    M4: { ...directSolverModules.M4, build: () => ({ instructions: 'fixture', message: 'fixture' }) } });
  return { state, workers, run, check, modules, emit, save };
}

describe('turn ledger at the real research worker boundary', () => {
  it('settles each model call after host checking and preserves usage totals and provider turn ids', async () => {
    const { state, run, modules, check, emit } = fixture(); let calls = 0;
    const open = vi.fn(async (options: MathAgentOptions): Promise<MathAgentSession> => ({ threadId: 'fixture-thread',
      run: async (_message, _messageId, workspace, onStarted) => {
        onStarted('provider-turn-' + ++calls);
        fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), 'A saved trial, number ' + calls);
        options.onUsage({ totalTokens: calls * 30 }); return 'completed';
      }, interrupt: async () => {}, close: async () => {} }));
    await expect(run(modules(open), 2)).resolves.toBeUndefined();
    expect(calls).toBe(2); expect(check).toHaveBeenCalledTimes(2);
    expect(state.usage!.totalTokens).toBe(60);
    expect(state.turnLedger!.turns).toHaveLength(2);
    for (const [index, turn] of state.turnLedger!.turns.entries()) {
      expect(turn).toMatchObject({ turnId: 'provider-turn-' + (index + 1), execution: 'completed', outcomeStatus: 'recorded',
        scope: { actionKind: 'independent', operation: 'direct' },
        usage: { observedDeltaTokens: 30, coverage: 'reported', attribution: 'unverified' },
        outcome: { acceptance: 'not-assessed', retainedWork: { check: { passed: false, status: 'failed' } } } });
    }
    expect(emit.mock.calls.filter(([event]) => event === 'model_turn_ledger_recorded')).toHaveLength(2);
  });

  it('keeps a recovered failed request and the new session consumption partial instead of charging the retry precisely', async () => {
    const { state, run, modules } = fixture(); let calls = 0, sessions = 0;
    const open = vi.fn(async (options: MathAgentOptions): Promise<MathAgentSession> => ({ threadId: 'thread-' + ++sessions,
      run: async (_message, _messageId, workspace, onStarted) => {
        onStarted('turn-' + ++calls); fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), 'Trial ' + calls);
        options.onUsage({ totalTokens: calls === 1 ? 10 : 3 }); return calls === 1 ? 'failed' : 'completed';
      }, interrupt: async () => {}, close: async () => {} }));
    await expect(run(modules(open), 2)).resolves.toBeUndefined();
    expect(sessions).toBe(2); expect(state.usage!.totalTokens).toBe(13);
    expect(state.turnLedger!.turns.map(turn => [turn.execution, turn.usage.coverage, turn.usage.observedDeltaTokens]))
      .toEqual([['failed', 'partial', 10], ['completed', 'partial', 3]]);
    expect(state.turnLedger!.turns[1].usage.uncertainReasons).toContain('prior-thread-usage-incomplete');
    expect(state.usageAccounting!.incomplete).toBe(true);
  });

  it('quarantines a closed session report without merging it into or satisfying the next model turn', async () => {
    const { state, run, modules, emit } = fixture(); let sessions = 0, calls = 0;
    const callbacks: MathAgentOptions['onUsage'][] = [];
    const open = vi.fn(async (options: MathAgentOptions): Promise<MathAgentSession> => {
      const serial = ++sessions; callbacks.push(options.onUsage);
      return { threadId: 'thread-' + serial,
        run: async (_message, _messageId, workspace, onStarted) => {
          onStarted('turn-' + ++calls); fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), 'Trial ' + calls);
          if (serial === 1) { options.onUsage({ totalTokens: 10 }); return 'failed'; }
          callbacks[0]({ totalTokens: 1000 });
          return 'completed';
        }, interrupt: async () => {}, close: async () => {} };
    });
    await expect(run(modules(open), 2)).resolves.toBeUndefined();
    expect(calls).toBe(2); expect(sessions).toBe(2);
    expect(state.usage!.totalTokens).toBe(10);
    expect(state.usageAccounting).toMatchObject({ startedTurns: 2, reportedTurns: 0, incomplete: true, pending: false });
    expect(state.turnLedger!.unscopedReports).toBe(1);
    expect(state.turnLedger!.turns[0].usage).toMatchObject({ coverage: 'partial', observedDeltaTokens: 10 });
    expect(state.turnLedger!.turns[0].usage.uncertainReasons).toContain('late-or-unscoped-usage-report');
    expect(state.turnLedger!.turns[1].usage).toMatchObject({ coverage: 'unknown', reportedUpdates: 0,
      afterTotalTokens: null, observedDeltaTokens: null });
    expect(state.turnLedger!.turns[1].usage.uncertainReasons)
      .toEqual(expect.arrayContaining(['cross-session-usage-report', 'missing-usage-report']));
    expect(emit).toHaveBeenCalledWith('worker_usage_unscoped', expect.objectContaining({ reportedTotalTokens: 1000 }));
  });

  it('invalidates a closed session before rotating the usage baseline or reopening the model', async () => {
    const { state, run, modules, emit } = fixture(); let sessions = 0, calls = 0, closed = false;
    const callbacks: MathAgentOptions['onUsage'][] = [];
    emit.mockImplementation((event: string) => {
      if (event !== 'context_restarted') return;
      expect(closed).toBe(true); expect(sessions).toBe(1);
      callbacks[0]({ totalTokens: 1000 });
    });
    const open = vi.fn(async (options: MathAgentOptions): Promise<MathAgentSession> => {
      const serial = ++sessions; callbacks.push(options.onUsage);
      return { threadId: 'thread-' + serial,
        run: async (_message, _messageId, workspace, onStarted) => {
          onStarted('turn-' + ++calls); fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), 'Trial ' + calls);
          options.onUsage({ totalTokens: serial === 1 ? 10 : 3 });
          return serial === 1 ? 'failed' : 'completed';
        }, interrupt: async () => {}, close: async () => { closed = true; } };
    });
    await expect(run(modules(open), 2)).resolves.toBeUndefined();
    expect(calls).toBe(2); expect(sessions).toBe(2);
    expect(state.usage!.totalTokens).toBe(13);
    expect(state.usageAccounting).toMatchObject({ startedTurns: 2, reportedTurns: 1, incomplete: true, pending: false });
    expect(state.turnLedger!.unscopedReports).toBe(1);
    expect(state.turnLedger!.turns.map(turn => turn.usage.observedDeltaTokens)).toEqual([10, 3]);
    expect(state.turnLedger!.turns[0].usage.uncertainReasons).toContain('late-or-unscoped-usage-report');
    expect(emit).toHaveBeenCalledWith('worker_usage_unscoped', expect.objectContaining({ reportedTotalTokens: 1000 }));
  });

  it('rejects a closed request gate without stopping its replacement or counting duplicate receipts', async () => {
    const { state, run, modules } = fixture();
    const callbacks: MathAgentOptions[] = [];
    const open = vi.fn(async (options: MathAgentOptions): Promise<MathAgentSession> => {
      const serial = callbacks.push(options);
      return { threadId: 'thread-' + serial, usageSource: 'upstream-requests',
        run: async (_message, _messageId, workspace, onStarted) => {
          onStarted('turn-' + serial); fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), 'Trial ' + serial);
          if (serial === 2) {
            expect(callbacks[0].requestGate!()).toEqual({ allowed: false, reason: 'math_model_request_stopped' });
            callbacks[0].onUsage({ totalTokens: 1000 });
          }
          const admission = options.requestGate!();
          expect(admission.allowed).toBe(true);
          if (admission.allowed) {
            const receipt = { complete: true, usage: { totalTokens: serial === 1 ? 10 : 3, inputTokens: serial === 1 ? 8 : 1, outputTokens: 2 } };
            admission.settle(receipt); admission.settle(receipt);
          }
          return serial === 1 ? 'failed' : 'completed';
        }, interrupt: async () => {}, close: async () => {} };
    });
    await expect(run(modules(open), 2)).resolves.toBeUndefined();
    expect(open).toHaveBeenCalledTimes(2);
    expect(state.usage!.totalTokens).toBe(13);
    expect(state.requestUsageAccounting).toEqual({ startedRequests: 2, reportedRequests: 2, pendingRequests: 0, incomplete: false });
    expect(state.usageAccounting).toEqual({ startedTurns: 2, reportedTurns: 2, pending: false, incomplete: false });
    expect(state.turnLedger!.turns.map(turn => turn.execution)).toEqual(['failed', 'completed']);
    expect(state.error).toBeUndefined();
  });

  it.each([{ timing: 'closing', complete: true }, { timing: 'replacement', complete: true },
    { timing: 'replacement', complete: false }])
  ('retains late request consumption during $timing (complete: $complete) without restoring missing coverage', async ({ timing, complete }) => {
    const { state, run, modules } = fixture(); let sessions = 0;
    let lateRequest = () => {};
    const open = vi.fn(async (options: MathAgentOptions): Promise<MathAgentSession> => {
      const serial = ++sessions;
      return { threadId: 'thread-' + serial, usageSource: 'upstream-requests',
        run: async (_message, _messageId, workspace, onStarted) => {
          onStarted('turn-' + serial); fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), 'Trial ' + serial);
          const admission = options.requestGate!();
          expect(admission.allowed).toBe(true);
          if (admission.allowed) {
            const settle = () => admission.settle({ complete: serial === 1 ? complete : true,
              usage: { totalTokens: serial === 1 ? 10 : 3, inputTokens: serial === 1 ? 8 : 1, outputTokens: 2 } });
            if (serial === 1) lateRequest = settle;
            else {
              if (timing === 'replacement') { lateRequest(); lateRequest(); }
              settle();
            }
          }
          return serial === 1 ? 'failed' : 'completed';
        }, interrupt: async () => {}, close: async () => {
          if (serial === 1 && timing === 'closing') { lateRequest(); lateRequest(); }
        } };
    });
    await expect(run(modules(open), 2)).resolves.toBeUndefined();
    expect(open).toHaveBeenCalledTimes(2);
    expect(state.usage!.totalTokens).toBe(13);
    expect(state.requestUsageAccounting).toEqual({ startedRequests: 2, reportedRequests: complete ? 2 : 1, pendingRequests: 0, incomplete: true });
    expect(state.usageAccounting).toEqual({ startedTurns: 2, reportedTurns: complete ? 1 : 0, pending: false, incomplete: true });
    expect(state.tokenBudget).toMatchObject({ status: 'unlimited', reportedTotalTokens: 13, usageComplete: false });
    expect(state.turnLedger!.turns[0].usage.uncertainReasons).toContain('late-or-unscoped-usage-report');
    expect(state.turnLedger!.turns[1].usage.reportedUpdates).toBe(1);
    if (timing === 'replacement') expect(state.turnLedger!.turns[1].usage.uncertainReasons).toContain('cross-session-usage-report');
  });

  it('settles an interrupted cooperative assignment only after the host has saved its advisory draft', async () => {
    const { state, run, modules, check } = fixture(true);
    const open = vi.fn(async (options: MathAgentOptions): Promise<MathAgentSession> => ({ threadId: 'advisory-thread',
      run: async (_message, _messageId, workspace, onStarted) => {
        onStarted('advisory-checkpoint');
        fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), 'A useful boundary-case argument with one remaining gap.');
        options.onUsage({ totalTokens: 20 }); return 'interrupted';
      }, interrupt: async () => {}, close: async () => {} }));
    await expect(run(modules(open), 1)).resolves.toBeUndefined();
    expect(open).toHaveBeenCalledTimes(1); expect(check).not.toHaveBeenCalled();
    const turn = state.turnLedger!.turns[0];
    expect(turn).toMatchObject({ workerId: 'peer', execution: 'interrupted', outcomeStatus: 'recorded',
      scope: { actionKind: 'task', taskId: 'investigation', groupId: 'main' },
      usage: { coverage: 'partial', observedDeltaTokens: 20 },
      outcome: { acceptance: 'not-assessed', retainedWork: { value: 'not-assessed', drafts: [{
        taskId: 'investigation', evidenceStatus: 'advisory-unverified',
      }] } } });
    expect(turn.scope.assignmentId).toBeTypeOf('string');
    expect(turn.outcome!.retainedWork.drafts[0].assignmentId).toBe(turn.scope.assignmentId);
    expect(state.cooperation!.tasks.find(node => node.task.id === 'investigation')!.status).toBe('pending');
    expect(state.cooperation!.tasks.filter(node => node.task.kind === 'goal').every(node => !node.integratedCheck)).toBe(true);
  });
});
