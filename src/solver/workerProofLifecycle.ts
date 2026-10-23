import type { MathAgentSession } from '../runtime/codexSession';
import type { SolverRunState } from './archive';
import type { CooperativeResearch } from './cooperation';
import { solverSourceFeedback } from './feedback';
import type { ResearchCandidate } from './modules/execution';
import type { ResearchWorker } from './modules/organization';
import type { ResearchOperation } from './modules/value';
import { commitSolverSources } from './problem';
import type { ProofReadyRecord } from './proofReady';
import type { CooperativeAction } from './tasks';

type TaskAction = Extract<CooperativeAction, { kind: 'task' }>;

/** Owns the writer-stop, immutable-snapshot, independent-check sequence for one worker. */
export class WorkerProofLifecycle {
  constructor(private readonly input: {
    state: SolverRunState;
    research: Pick<SolverRunState, 'phase' | 'check' | 'writerStopUnconfirmed'>;
    worker: ResearchWorker;
    cooperation: CooperativeResearch;
    close: () => Promise<void>;
    save: () => void;
    emit: (event: string, details?: Record<string, unknown>) => void;
    checked: () => void;
  }) {}

  /** A durable frozen commit can be checked after restart without reopening its writer. */
  async resumeFrozen(assignment: CooperativeAction | undefined): Promise<boolean> {
    if (assignment?.kind !== 'task') return false;
    const ready = this.input.cooperation.pendingProofReady(this.input.worker, assignment);
    if (!ready?.snapshotCommit) return false;
    await this.input.close();
    await this.checkSnapshot(assignment, ready);
    return true;
  }

  /** Only a settled turn's confirmed writer stop may authorize a new snapshot. */
  async settleTurn(assignment: CooperativeAction | undefined, candidate: ResearchCandidate,
    operation: ResearchOperation, session: MathAgentSession): Promise<boolean> {
    if (assignment?.kind !== 'task') return false;
    const { state, research, worker, cooperation, close, save, emit } = this.input;
    const ready = cooperation.pendingProofReady(worker, assignment);
    if (!ready) return false;
    if (candidate.worktree !== worker.worktree || candidate.problemReceiptDigest !== state.problem.receiptDigest ||
        candidate.operation !== operation || candidate.provenance.workerId !== worker.id)
      throw new Error('math_candidate_identity_changed');
    if (!ready.snapshotCommit) {
      let stopped: Awaited<ReturnType<NonNullable<MathAgentSession['stopForFreeze']>>> | undefined;
      try { stopped = await session.stopForFreeze?.(); }
      catch { stopped = { status: 'unconfirmed', reason: 'shutdown-failed' }; }
      if (stopped?.status !== 'stopped') {
        const reason = stopped?.reason ?? 'writer-stop-confirmation-unavailable';
        // Persist quarantine before ordinary close: that close can itself fail or stall.
        research.writerStopUnconfirmed = { at: Date.now(), reason };
        cooperation.proofReadyFailedFreeze(worker, assignment, reason);
        cooperation.interrupted(worker, assignment);
        emit('proof_ready_freeze_deferred', { receiptId: ready.id, reason });
        save();
        try { await close(); } catch { /* Quarantine, not ordinary close, controls reuse. */ }
        throw new Error('math_writer_stop_unconfirmed:' + worker.id + ':' + reason);
      }
      await close();
      // The assignment and environment may have changed while the writer was stopping.
      if (!cooperation.pendingProofReady(worker, assignment)) return true;
      const sourceError = solverSourceFeedback(state.problem, worker.worktree);
      if (sourceError) {
        research.check = undefined;
        cooperation.proofReadyFailedFreeze(worker, assignment, sourceError);
        cooperation.rejected(assignment, sourceError);
        save(); emit('source_rejected');
        return true;
      }
      const commit = commitSolverSources(state.problem, worker.worktree);
      if (!cooperation.proofReadyFrozen(worker, assignment, commit)) return true;
    } else await close();
    await this.checkSnapshot(assignment, ready);
    return true;
  }

  private async checkSnapshot(assignment: TaskAction, ready: ProofReadyRecord): Promise<void> {
    const { state, research, worker, cooperation, save, emit, checked } = this.input;
    if (!ready.snapshotCommit) throw new Error('math_proof_ready_snapshot_missing');
    state.phase = research.phase = 'checking'; save();
    const delivery = await cooperation.deliver(worker, assignment, ready.snapshotCommit);
    research.check = delivery.check;
    cooperation.proofReadyCompleted(worker, assignment, delivery.check);
    emit('proof_ready_checked', { receiptId: ready.id, commit: ready.snapshotCommit,
      passed: delivery.check?.passed === true, conditional: ready.evidence === 'conditional' });
    checked(); save();
  }
}
