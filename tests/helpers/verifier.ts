import type { MathematicsVerifierBatchRequest, MathematicsVerifierBatchResult } from '../../src/math/verifier';

type Results = MathematicsVerifierBatchResult['results'];

function envelope(request: MathematicsVerifierBatchRequest, sessionId: string, results: Results): MathematicsVerifierBatchResult {
  return { schema: 'deepscientist.mathematics.verification-batch/v1', status: 'kernel_verified',
    targetCommit: request.targetCommit!, sessionId, events: [], startedAt: 1, checkedAt: 2, durationMs: 1, results };
}

/**
 * Kernel-verified batch that echoes each request item. With `checks`, every result also carries
 * the check id, session id and check time the runtime uses to bind receipts to requested items.
 */
export function verifiedBatch(request: MathematicsVerifierBatchRequest,
  { sessionId, receipt = 'fixture', checks = false }: { sessionId: string; receipt?: string; checks?: boolean }): MathematicsVerifierBatchResult {
  return envelope(request, sessionId, request.items.map((item, index) => ({ ...item,
    sourceDeclarationHash: item.expectedSourceDeclarationHash,
    ...(checks ? { checkId: item.id?.trim() || `check-${index + 1}`, sessionId, checkedAt: 2 } : {}),
    receiptId: `${receipt}-${request.targetCommit}-${item.theoremName}`, targetCommit: request.targetCommit,
    status: 'kernel_verified', claim: 'statement' })) as Results);
}

/** Kernel-verified batch with complete receipts, for code that reads hashes, toolchain and counts. */
export function receiptBatch(request: MathematicsVerifierBatchRequest,
  { sessionId, receiptId }: { sessionId: string; receiptId: (index: number, theoremName?: string) => string }): MathematicsVerifierBatchResult {
  return envelope(request, sessionId, request.items.map((item, index) => ({
    status: 'kernel_verified', targetCommit: request.targetCommit!, proofPath: item.proofPath, theoremName: item.theoremName,
    statementHash: item.statementHash, leanStatementHash: item.leanStatementHash, claim: item.claim ?? 'statement',
    sourceDeclarationHash: item.expectedSourceDeclarationHash, proofHash: 'fixture-proof',
    statementBinding: 'caller-bound-to-committed-declaration', toolchain: { lean: 'fixture-lean' }, verifier: 'lean-kernel',
    goalsRemaining: 0, sorryCount: 0, admitCount: 0, axioms: [], checkedAt: 2,
    checkId: item.id?.trim() || `check-${index + 1}`, receiptId: receiptId(index, item.theoremName), sessionId,
    declarationReferences: { statement: [], proof: [] },
  })));
}

/** Marks the selected results (default: all) and the batch as failed Lean checks. */
export function failedBatch(batch: MathematicsVerifierBatchResult,
  { stdoutPreview, goalsRemaining, selected = () => true }: {
    stdoutPreview: (proofPath: string) => string; goalsRemaining?: number;
    selected?: (result: Results[number], index: number) => boolean;
  }): MathematicsVerifierBatchResult {
  return { ...batch, status: 'failed', results: batch.results.map((result, index) => selected(result, index)
    ? { ...result, status: 'failed', ...(goalsRemaining === undefined ? {} : { goalsRemaining }),
      error: 'Lean exited with status 1.', stdoutPreview: stdoutPreview(result.proofPath) } : result) };
}
