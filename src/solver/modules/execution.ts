import crypto from 'node:crypto';
import type { MathAgentSession } from '../../runtime/codexSession';
import type { SolverProblem } from '../problem';
import type { ContextBundle } from './context';
import type { ResearchOperation } from './value';
import type { ResearchWorker } from './organization';

export type ResearchCandidate = Readonly<{
  status: string;
  worktree: string;
  problemReceiptDigest: string;
  operation: ResearchOperation;
  provenance: Readonly<{ workerId: string; threadId: string }>;
}>;

/** A closed transport is a failed turn; aborts and other errors keep their original meaning. */
export async function runResearchTurn(session: MathAgentSession, message: string, worktree: string,
  signal: AbortSignal, onStarted: (turnId: string) => void): Promise<string> {
  let status: string;
  try {
    status = await session.run(message, crypto.randomUUID(), worktree, onStarted);
  } catch (error) {
    if (!(error instanceof Error) || !/^math_codex_(?:transport_closed|rpc_timeout:)/u.test(error.message)) throw error;
    status = 'failed';
  }
  signal.throwIfAborted();
  return status;
}

/** M1 writes a candidate; M2 subsequently freezes and fingerprints its actual source. */
export async function executeResearch(task: SolverProblem, context: ContextBundle, operation: ResearchOperation,
  worker: ResearchWorker, session: MathAgentSession, signal: AbortSignal,
  onStarted: (turnId: string) => void): Promise<ResearchCandidate> {
  const status = await runResearchTurn(session, context.message, worker.worktree, signal, onStarted);
  return { status, worktree: worker.worktree, problemReceiptDigest: task.receiptDigest, operation,
    provenance: { workerId: worker.id, threadId: session.threadId } };
}
