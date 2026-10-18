import crypto from 'node:crypto';
import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import type { SolverRunState, SolverWorkerState } from './archive';
import { captureObligationSnapshot, diffObligationProgress } from './obligationProgress';
import { reportedTotalTokens } from './usageBudget';
import { taskGroup, taskVersion, type CooperativeAction } from './tasks';

export const MODEL_TURN_LEDGER_LIMIT = 256;
type UsageCoverage = 'pending' | 'reported' | 'partial' | 'unknown';
export type ModelTurnReceipt = {
  schema: 'theoremos.model-turn.v1'; id: string; workerId: string; sessionId?: string; threadId?: string; turnId?: string;
  workerTurn: number; runTurn: number; startedAt: number; modelFinishedAt?: number; settledAt?: number;
  scope: { actionKind: string; operation: string; taskId?: string; taskDigest?: string; assignmentId?: string;
    groupId?: string; routeId?: string; seedCommit?: string; reviewId?: string; planVersion?: string };
  execution: 'running' | 'completed' | 'interrupted' | 'failed' | 'recovered';
  usage: { basis: 'provider-thread-window'; attribution: 'unverified'; coverage: UsageCoverage;
    beforeTotalTokens: number | null; afterTotalTokens: number | null; observedDeltaTokens: number | null;
    reportedUpdates: number; uncertainReasons: string[] };
  outcomeStatus: 'pending' | 'recorded' | 'unavailable-after-restart';
  outcome?: ModelTurnOutcome;
};
export type ModelTurnLedger = { retainedLimit: number; dropped: number; unscopedReports: number; turns: ModelTurnReceipt[] };
type EvidenceSnapshot = ReturnType<typeof captureTurnEvidence>;
export type ModelTurnOutcome = {
  evidence: 'recorded-not-replayed'; acceptance: 'not-assessed'; attribution: 'observed-not-causal';
  observedProgress: { scope: 'assignment-cone' | 'run'; taskVersionMatches: boolean;
    beforeDigest: string; afterDigest: string; obligations: { closed: string[]; reopened: string[]; changed: string[] };
    frontierChangedGoalIds: string[]; advisoryChangedTaskIds: string[] };
  retainedWork: { value: 'not-assessed'; deliveries: EvidenceSnapshot['deliveries']; drafts: EvidenceSnapshot['drafts'];
    blockers: EvidenceSnapshot['blockers']; failedInputs: EvidenceSnapshot['failedInputs'];
    checkpoint?: EvidenceSnapshot['checkpoint']; check?: EvidenceSnapshot['check'] };
};

const hash = (value: unknown) => mathDigest(canonicalMathJson(value));
const copy = <T>(value: T): T => JSON.parse(canonicalMathJson(value));
const reason = (receipt: ModelTurnReceipt, value: string) => {
  if (!receipt.usage.uncertainReasons.includes(value)) receipt.usage.uncertainReasons.push(value);
};

function captureTurnEvidence(state: SolverRunState, workerId: string, scope: ModelTurnReceipt['scope']) {
  const cooperation = state.cooperation, taskId = scope.taskId;
  const tasks = cooperation?.tasks ?? [];
  const root = tasks.find(node => node.task.id === taskId);
  const taskVersionMatches = !taskId || Boolean(root && taskVersion(root.task) === scope.taskDigest);
  const inputs = (id: string) => {
    const node = tasks.find(node => node.task.id === id);
    return [...(node?.task.dependsOn ?? []), ...(cooperation?.proofRoutes ?? node?.alternativeRoutes ?? [])
      .filter(route => route.targetTaskId === id).flatMap(route => [...route.prerequisiteTaskIds, route.closingTaskId])];
  };
  const related = new Set(taskId && taskVersionMatches ? [taskId] : []);
  if (taskId && taskVersionMatches) {
    // Observe the assigned inference and its consumers, including inputs needed to describe their frontier.
    let changed = true;
    while (changed) {
      changed = false;
      for (const node of tasks) if (!related.has(node.task.id) && inputs(node.task.id).some(id => related.has(id))) {
        related.add(node.task.id); changed = true;
      }
    }
    const visit = (id: string) => {
      for (const input of inputs(id)) if (!related.has(input)) { related.add(input); visit(input); }
    };
    for (const id of related) visit(id);
  }
  const scopedTasks = taskId ? tasks.filter(node => related.has(node.task.id)) : tasks;
  const snapshot = captureObligationSnapshot(scopedTasks, { environmentDigest: state.environmentDigest,
    groups: cooperation?.groups, proofRoutes: cooperation?.proofRoutes?.filter(route => !taskId || related.has(route.targetTaskId)),
    blockers: cooperation?.blockers?.filter(blocker => !taskId || related.has(blocker.taskId)) });
  const deliveries = (cooperation?.deliveries ?? []).filter(delivery => delivery.producer === workerId &&
    (!taskId || delivery.taskId === taskId && delivery.taskDigest === scope.taskDigest)).map(delivery => ({
    id: delivery.id, kind: delivery.kind, status: delivery.status, taskId: delivery.taskId, taskDigest: delivery.taskDigest,
    commit: delivery.commit, findingDigest: delivery.findingDigest, evidenceRefs: delivery.evidenceRefs ?? [],
    // Artifact changes retain inspectable work, not a claim of mathematical improvement.
    artifacts: delivery.artifacts && { scope: delivery.artifacts.scope, digest: hash(delivery.artifacts) },
  }));
  const drafts = Object.entries(cooperation?.researchDrafts ?? {}).filter(([id, draft]) => draft.workerId === workerId &&
    (!taskId || id === taskId && draft.taskDigest === scope.taskDigest && draft.assignmentId === scope.assignmentId))
    .map(([id, draft]) => ({ taskId: id, taskDigest: draft.taskDigest, assignmentId: draft.assignmentId,
      commit: draft.commit, outputDigest: draft.outputDigest, artifactDigest: hash(draft.artifacts),
      evidenceStatus: 'advisory-unverified' as const }));
  const blockers = (cooperation?.blockers ?? []).filter(blocker => taskId && blocker.taskId === taskId && blocker.taskDigest === scope.taskDigest)
    .map(blocker => ({ id: blocker.id, taskId: blocker.taskId, taskDigest: blocker.taskDigest, status: blocker.status,
      mechanism: blocker.mechanism, scope: blocker.scope, evidenceRefs: blocker.evidenceRefs,
      count: blocker.count, evidenceStatus: blocker.evidenceStatus }));
  const failedInputs = (cooperation?.failedTaskInputs ?? []).filter(failure => taskId && failure.taskId === taskId &&
    failure.taskDigest === scope.taskDigest).map(failure => ({ id: failure.id, taskId: failure.taskId,
    taskDigest: failure.taskDigest, attemptFingerprint: failure.attemptFingerprint, relatedFailureIds: failure.relatedFailureIds,
    feedbackDigest: hash(failure.feedback), evidenceStatus: 'recorded-failure' as const }));
  const checkpointRecord = taskId && cooperation?.researchCheckpoints?.[taskId];
  const checkpoint = checkpointRecord && checkpointRecord.taskDigest === scope.taskDigest ? {
    ...checkpointRecord, evidenceStatus: 'candidate-not-scored' as const } : undefined;
  const worker = state.workers?.find(worker => worker.id === workerId) ?? state;
  const proof = worker.check;
  const check = proof && { commit: proof.commit, sourceDigest: proof.sourceDigest, passed: proof.passed,
    status: proof.verification.status, receiptIds: proof.verification.results.map(receipt => receipt.receiptId).filter(Boolean) };
  return copy({ snapshot, taskVersionMatches, deliveries, drafts, blockers, failedInputs, checkpoint, check });
}

const changedItems = <T>(before: readonly T[], after: readonly T[], key: (item: T) => string) => {
  const old = new Map(before.map(item => [key(item), hash(item)]));
  return after.filter(item => old.get(key(item)) !== hash(item));
};

/** Ledger observations never authorize acceptance, change scheduling or assign a value to prose changes. */
export class WorkerTurnLedger {
  private current?: { receipt: ModelTurnReceipt; before: EvidenceSnapshot };
  private readonly uncertainSessions = new Set<string>();
  constructor(private state: SolverRunState, private workerId: string,
    private research: SolverRunState | SolverWorkerState,
    private emit: (event: string, details: Record<string, unknown>) => void) {}

  begin(sessionId: string | undefined, threadId: string | undefined, operation: string, action?: CooperativeAction) {
    this.settle();
    const ledger = this.state.turnLedger ??= { retainedLimit: MODEL_TURN_LEDGER_LIMIT, dropped: 0, unscopedReports: 0, turns: [] };
    ledger.retainedLimit = MODEL_TURN_LEDGER_LIMIT;
    const scope: ModelTurnReceipt['scope'] = { actionKind: action?.kind ?? 'independent', operation };
    if (action?.kind === 'task') Object.assign(scope, { taskId: action.task.id, taskDigest: action.assignment.taskDigest,
      assignmentId: action.assignment.assignmentId, groupId: action.assignment.groupId ?? taskGroup(action.task),
      routeId: action.assignment.routeId, seedCommit: action.assignment.seedCommit });
    else if (action) {
      if ('seedCommit' in action) scope.seedCommit = action.seedCommit;
      if ('planVersion' in action) scope.planVersion = action.planVersion;
      if ('reviewId' in action) Object.assign(scope, { reviewId: action.reviewId, taskId: action.taskId, taskDigest: action.taskDigest,
        assignmentId: action.assignmentId });
      else if ('assignmentId' in action) scope.assignmentId = action.assignmentId;
    }
    const baseline = reportedTotalTokens(this.research.usage) ?? (this.research.usageAccounting?.startedTurns === 0 ? 0 : null);
    // Even a fully observed window is not exact turn attribution: callbacks carry no provider turn ID.
    const receipt: ModelTurnReceipt = { schema: 'theoremos.model-turn.v1', id: crypto.randomUUID(), workerId: this.workerId,
      sessionId, threadId, workerTurn: this.research.turns, runTurn: this.state.turns, startedAt: Date.now(), scope: copy(scope),
      execution: 'running', outcomeStatus: 'pending', usage: { basis: 'provider-thread-window', attribution: 'unverified',
        coverage: 'pending', beforeTotalTokens: baseline, afterTotalTokens: null, observedDeltaTokens: null,
        reportedUpdates: 0, uncertainReasons: ['provider-turn-id-unavailable'] } };
    if (sessionId && (this.uncertainSessions.has(sessionId) || ledger.turns.some(turn => turn.sessionId === sessionId &&
        turn.usage.coverage !== 'reported'))) reason(receipt, 'prior-turn-usage-incomplete');
    if (this.research.usageAccounting?.incomplete) reason(receipt, 'prior-thread-usage-incomplete');
    this.current = { receipt, before: captureTurnEvidence(this.state, this.workerId, receipt.scope) };
    ledger.turns.push(receipt);
    while (ledger.turns.length > MODEL_TURN_LEDGER_LIMIT) {
      const settled = ledger.turns.findIndex(turn => turn.settledAt !== undefined);
      if (settled < 0) break;
      ledger.turns.splice(settled, 1); ledger.dropped++;
    }
    this.emit('model_turn_ledger_started', { receipt: copy(receipt) });
  }

  started(turnId: string) { if (this.current?.receipt.execution === 'running') this.current.receipt.turnId = turnId; }

  usage(sessionId: string, valid: boolean) {
    const receipt = this.current?.receipt, total = reportedTotalTokens(this.research.usage);
    if (!receipt || receipt.execution !== 'running' || receipt.sessionId !== sessionId) {
      const ledger = this.state.turnLedger ??= { retainedLimit: MODEL_TURN_LEDGER_LIMIT, dropped: 0, unscopedReports: 0, turns: [] };
      ledger.unscopedReports++;
      this.uncertainSessions.add(sessionId);
      const previous = ledger.turns.findLast(turn => turn.workerId === this.workerId && turn.sessionId === sessionId);
      if (previous) {
        reason(previous, 'late-or-unscoped-usage-report');
        if (previous.usage.coverage === 'reported') previous.usage.coverage = 'partial';
        this.emit('model_turn_ledger_updated', { receipt: copy(previous) });
      }
      if (receipt?.execution === 'running') reason(receipt, 'cross-session-usage-report');
      this.emit('model_turn_usage_unscoped', { sessionId, receiptId: previous?.id, reportedTotalTokens: total });
      return;
    }
    if (!valid || total === null) { reason(receipt, 'invalid-or-regressive-usage-report'); return; }
    receipt.usage.reportedUpdates++;
    receipt.usage.afterTotalTokens = total;
    const before = receipt.usage.beforeTotalTokens;
    receipt.usage.observedDeltaTokens = before !== null && total >= before ? total - before : null;
    if (receipt.usage.observedDeltaTokens === null) reason(receipt, 'unknown-usage-baseline');
    else if (receipt.usage.observedDeltaTokens === 0) reason(receipt, 'unchanged-thread-total');
  }

  finish(status: ModelTurnReceipt['execution']) {
    const receipt = this.current?.receipt;
    if (!receipt) return;
    receipt.execution = status;
    receipt.modelFinishedAt = Date.now();
    if (status !== 'completed') reason(receipt, 'request-did-not-complete');
    if (!receipt.usage.reportedUpdates) reason(receipt, 'missing-usage-report');
    receipt.usage.coverage = !receipt.usage.reportedUpdates ? 'unknown' : status === 'completed' &&
      receipt.usage.observedDeltaTokens !== null && receipt.usage.uncertainReasons.length === 1 ? 'reported' : 'partial';
    if (receipt.sessionId && receipt.usage.coverage !== 'reported') this.uncertainSessions.add(receipt.sessionId);
  }

  settle() {
    const active = this.current;
    if (!active) return false;
    const { receipt, before } = active, after = captureTurnEvidence(this.state, this.workerId, receipt.scope);
    const progress = diffObligationProgress(before.snapshot, after.snapshot);
    receipt.outcome = { evidence: 'recorded-not-replayed', acceptance: 'not-assessed', attribution: 'observed-not-causal',
      observedProgress: { scope: receipt.scope.taskId ? 'assignment-cone' : 'run', taskVersionMatches: after.taskVersionMatches,
        beforeDigest: before.snapshot.digest, afterDigest: after.snapshot.digest,
        obligations: { closed: progress?.obligations.closed.map(item => item.after.taskId) ?? [],
        reopened: progress?.obligations.reopened.map(item => item.after.taskId) ?? [],
        changed: progress?.obligations.changed.map(item => item.after.taskId) ?? [] },
        frontierChangedGoalIds: progress?.goalFrontiers.map(item => item.goalId) ?? [],
        advisoryChangedTaskIds: [...(progress?.advisory.completed ?? []), ...(progress?.advisory.changed ?? [])].map(item => item.after.taskId) },
      retainedWork: { value: 'not-assessed', deliveries: changedItems(before.deliveries, after.deliveries, item => item.id),
        drafts: changedItems(before.drafts, after.drafts, item => item.taskId),
        blockers: changedItems(before.blockers, after.blockers, item => item.id),
        failedInputs: changedItems(before.failedInputs, after.failedInputs, item => item.id),
        ...(after.checkpoint && hash(before.checkpoint ?? null) !== hash(after.checkpoint) ? { checkpoint: after.checkpoint } : {}),
        ...(after.check && hash(before.check ?? null) !== hash(after.check) ? { check: after.check } : {}) } };
    receipt.outcomeStatus = 'recorded'; receipt.settledAt = Date.now();
    this.current = undefined;
    this.emit('model_turn_ledger_recorded', { receipt: copy(receipt) });
    return true;
  }
}

/** A crashed process cannot reconstruct a missing observation window from restored JSON. */
export function recoverModelTurnLedger(state: SolverRunState, emit: (event: string, details: Record<string, unknown>) => void) {
  for (const receipt of state.turnLedger?.turns ?? []) {
    if (receipt.settledAt !== undefined) continue;
    if (receipt.execution === 'running') receipt.execution = 'recovered';
    reason(receipt, 'recovered-unsettled-turn');
    receipt.usage.coverage = receipt.usage.reportedUpdates ? 'partial' : 'unknown';
    receipt.outcomeStatus = 'unavailable-after-restart'; receipt.settledAt = Date.now();
    emit('model_turn_ledger_recovered', { receipt: copy(receipt) });
  }
}
