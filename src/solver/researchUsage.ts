import type { MathAgentOptions, MathAgentSession } from '../runtime/codexSession';
import type { ModelRequestAdmission, ModelRequestStopReason } from '../runtime/modelRequest';
import type { SolverRunState, SolverWorkerState } from './archive';
import type { CooperativeAction } from './tasks';
import { beginRequestUsage, initializeRequestUsageAccounting, modelDispatchAllowed,
  recordThreadUsage, reportedTotalTokens } from './usageBudget';

type UsageCallbacks = Pick<MathAgentOptions, 'onUsage' | 'onUsageIncomplete' | 'requestGate'>;

/** Owns session-scoped usage and request admission; proof and scheduling decisions stay in research. */
export class ResearchUsage {
  private active?: { reported: boolean; incomplete: boolean; initialPlanning: boolean };
  sessionId?: string;
  stopReason?: ModelRequestStopReason;

  constructor(private input: {
    state: SolverRunState; research: SolverRunState | SolverWorkerState;
    maxTotalTokens: number; signal: AbortSignal; remainingMs: () => number;
    changed: () => void; emit: (event: string, details: Record<string, unknown>) => void;
  }) {}

  resetTurn() { this.stopReason = undefined; }

  begin(assignment?: CooperativeAction) {
    const { state, research, maxTotalTokens } = this.input;
    research.usageAccounting!.startedTurns++;
    research.usageAccounting!.pending = true;
    this.active = { reported: false, incomplete: false,
      initialPlanning: assignment?.kind === 'lead' && state.cooperation?.tasks.length === 0 && maxTotalTokens > 0 };
    this.resetTurn();
    this.input.changed();
  }

  finish(completed: boolean) {
    const { research } = this.input;
    const turn = this.active!;
    const accounting = research.usageAccounting!, requests = research.requestUsageAccounting;
    accounting.pending = false;
    // Request receipts cover failed turns; native thread totals require a completed turn.
    if ((requests ? requests.pendingRequests === 0 : turn.reported && completed) && !turn.incomplete)
      accounting.reportedTurns++;
    else accounting.incomplete = true;
    if (requests?.pendingRequests) requests.incomplete = true;
    this.active = undefined;
    this.input.changed();
  }

  sessionOpened(session: MathAgentSession) {
    if (session.usageSource !== 'upstream-requests') return;
    initializeRequestUsageAccounting(this.input.research);
    this.input.changed();
  }

  sessionClosed(sessionId: string | undefined) {
    if (this.sessionId === sessionId) this.sessionId = undefined;
  }

  bindSession(sessionId: string, inputTokens: () => number | undefined): UsageCallbacks {
    this.sessionId = sessionId;
    const { research, emit, changed } = this.input;
    return {
      onUsage: usage => {
        if (research.requestUsageAccounting) {
          if (this.sessionId === sessionId) research.lastInputTokens = inputTokens() ?? research.lastInputTokens;
          return;
        }
        if (this.sessionId !== sessionId) {
          // A closed session's cumulative total has no safe baseline in the current thread.
          research.usageAccounting!.incomplete = true;
          emit('worker_usage_unscoped', { sessionId, reportedTotalTokens: reportedTotalTokens(usage) });
          changed(); return;
        }
        research.lastInputTokens = inputTokens() ?? research.lastInputTokens;
        const reported = recordThreadUsage(research, usage);
        if (this.active && reported) this.active.reported = true;
        changed();
      },
      onUsageIncomplete: () => {
        research.usageAccounting!.incomplete = true;
        if (research.requestUsageAccounting) research.requestUsageAccounting.incomplete = true;
        if (this.active) this.active.incomplete = true;
        changed();
      },
      requestGate: () => this.admitRequest(sessionId),
    };
  }

  private rejectRequest(sessionId: string, reason: ModelRequestStopReason): ModelRequestAdmission {
    if (this.sessionId === sessionId && this.active) {
      const changed = this.stopReason !== reason;
      this.stopReason = reason;
      if (changed && reason === 'math_initial_planning_limit') this.input.emit('planning_budget_stopped', {
        reason, maxPlanningTokens: Math.max(1, Math.floor(this.input.maxTotalTokens / 4)), maxRequests: 2,
        reportedTotalTokens: reportedTotalTokens(this.input.research.usage),
        startedRequests: this.input.research.requestUsageAccounting?.startedRequests ?? 0,
      });
    }
    return { allowed: false, reason };
  }

  private admitRequest(sessionId: string): ModelRequestAdmission {
    const { state, research, signal, remainingMs, maxTotalTokens, changed } = this.input;
    if (!modelDispatchAllowed(state.tokenBudget!)) return this.rejectRequest(sessionId, state.tokenBudget!.reason!);
    if (this.sessionId !== sessionId || !this.active || signal.aborted || remainingMs() <= 0)
      return this.rejectRequest(sessionId, 'math_model_request_stopped');
    const requests = research.requestUsageAccounting;
    if (this.active.initialPlanning && state.cooperation?.tasks.length === 0 && requests && (requests.startedRequests >= 2 ||
        (reportedTotalTokens(research.usage) ?? 0) >= Math.max(1, Math.floor(maxTotalTokens / 4))))
      // Only settled requests can yield a checkpoint with complete accounting.
      return this.rejectRequest(sessionId, requests.pendingRequests ? 'math_model_request_stopped' : 'math_initial_planning_limit');
    const settle = beginRequestUsage(research);
    let settled = false;
    changed();
    return { allowed: true, settle: receipt => {
      if (settled) return;
      settled = true;
      settle(receipt);
      if (this.active && !receipt.complete) this.active.incomplete = true;
      changed();
    } };
  }
}
