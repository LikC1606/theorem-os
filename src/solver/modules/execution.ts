import crypto from 'node:crypto';
import type { MathAgentSession } from '../../runtime/codexSession';
import type { SolverProblem } from '../problem';
import type { ContextBundle } from './context';
import type { ResearchOperation } from './value';
import type { ResearchWorker } from './organization';
import { readLemmaPlan, type LemmaPlan } from '../lemma';

export type ResearchCandidate = Readonly<{
  status: string;
  version: string;
  worktree: string;
  problemReceiptDigest: string;
  operation: ResearchOperation;
  provenance: Readonly<{ workerId: string; threadId: string }>;
  remainingObligations: SolverProblem['targets'];
  lemmaPlan?: LemmaPlan;
  lemmaPlanError?: string;
}>;

/** M1 writes a candidate; M2 subsequently freezes and fingerprints its actual source. */
export async function executeResearch(task: SolverProblem, context: ContextBundle, operation: ResearchOperation,
  worker: ResearchWorker, session: MathAgentSession, signal: AbortSignal,
  onStarted: (turnId: string) => void): Promise<ResearchCandidate> {
  const version = crypto.randomUUID();
  let status: string;
  try {
    status = await session.run(context.message, version, worker.worktree, onStarted);
  } catch (error) {
    if (!(error instanceof Error) || error.message !== 'math_codex_transport_closed') throw error;
    status = 'failed';
  }
  signal.throwIfAborted();
  let lemmaPlan: LemmaPlan | undefined;
  let lemmaPlanError: string | undefined;
  if (operation !== 'direct') {
    try { lemmaPlan = readLemmaPlan(task, worker.worktree); }
    catch (error) { lemmaPlanError = error instanceof Error ? error.message : 'math_lemma_plan_invalid'; }
  }
  return { status, version, worktree: worker.worktree, problemReceiptDigest: task.receiptDigest, operation,
    provenance: { workerId: worker.id, threadId: session.threadId }, remainingObligations: task.targets,
    ...(operation !== 'direct' ? { lemmaPlan, lemmaPlanError } : {}) };
}
