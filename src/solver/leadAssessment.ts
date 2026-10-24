import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';

export type LeadAssessmentKind = 'capacity' | 'stagnation';
export type LeadAssessmentReceipt = {
  inputDigest: string; requestedAt: number; status: 'requested' | 'assessed';
  /** Optional for old saved runs; supplied at their next dispatch. */
  requestId?: string; evidenceDigest?: string; dispatchNonce?: string;
  coveredInputDigest?: string; assessedAt?: number;
  outcome?: 'plan-published' | 'no-independent-work'; decisionReason?: string;
  /** Host-verified executable work, absent from the old publication-only acknowledgement. */
  fulfilledTaskIds?: string[];
};
export type LeadAssessmentRequest = Readonly<{ requestId?: string; inputDigest: string }>;

/** Mathematical input identifies the request; redispatch only replaces its durable admission token. */
export function prepareLeadAssessment<T extends LeadAssessmentReceipt>(kind: LeadAssessmentKind,
  previous: T | undefined, next: T, dispatchNonce: string): { receipt: T; created: boolean } {
  const resumed = previous?.status === 'requested' && previous.inputDigest === next.inputDigest;
  const receipt = { ...(resumed ? previous : next),
    requestId: resumed && previous.requestId ? previous.requestId :
      mathDigest(canonicalMathJson({ schema: 'theorem-os.lead-assessment.v1', kind, inputDigest: next.inputDigest })),
    evidenceDigest: resumed ? previous.evidenceDigest ?? next.evidenceDigest : next.evidenceDigest,
    dispatchNonce };
  return { receipt, created: !resumed };
}

export function leadAssessmentCovered(receipt: LeadAssessmentReceipt | undefined, inputDigest: string): boolean {
  return receipt?.status === 'assessed' &&
    (receipt.inputDigest === inputDigest || receipt.coveredInputDigest === inputDigest);
}

/** Old publications acknowledged unrelated plans. Reconsider that receipt once on restore. */
export function reopenLegacyLeadAssessment(receipt: LeadAssessmentReceipt | undefined): boolean {
  if (receipt?.status !== 'assessed' || receipt.outcome !== 'plan-published' || receipt.fulfilledTaskIds?.length) return false;
  receipt.status = 'requested';
  delete receipt.outcome; delete receipt.assessedAt; delete receipt.coveredInputDigest; delete receipt.decisionReason;
  return true;
}

/** A late completion acknowledges only the exact admitted dispatch, never its replacement. */
export function finishLeadAssessment(receipt: LeadAssessmentReceipt | undefined, request: LeadAssessmentRequest | undefined,
  dispatchNonce: string | undefined, completion: { at: number; outcome: 'plan-published' | 'no-independent-work';
    reason?: string; fulfilledTaskIds?: readonly string[]; currentInput?: { inputDigest: string; evidenceDigest: string } }): boolean {
  if (!receipt || !request?.requestId || !dispatchNonce || receipt.requestId !== request.requestId ||
      receipt.inputDigest !== request.inputDigest || receipt.dispatchNonce !== dispatchNonce || receipt.status === 'assessed') return false;
  receipt.status = 'assessed'; receipt.assessedAt = completion.at; receipt.outcome = completion.outcome;
  if (completion.reason !== undefined) receipt.decisionReason = completion.reason;
  if (completion.fulfilledTaskIds) receipt.fulfilledTaskIds = [...completion.fulfilledTaskIds];
  // Cover the Lead's own graph revision, but preserve its original frozen request basis.
  if (completion.currentInput && receipt.evidenceDigest === completion.currentInput.evidenceDigest)
    receipt.coveredInputDigest = completion.currentInput.inputDigest;
  return true;
}
