import crypto from 'node:crypto';
import {
  normalizeMathCandidateReview,
  normalizeMathOfficialGateReceipt,
  normalizeMathRouteProbeReceipt,
  type MathCandidateReview,
  type MathCandidateReviewSource,
  type MathOfficialGateReceipt,
  type MathReceiptAttestation,
  type MathRouteProbeReceipt,
  type MathSolverReadyReceipt,
} from "../common/types/team/mathematicsTeam";
import { readFinanceReceiptSecret } from "../shared/services/finance/receiptAttestation";

type UnsignedOfficialReceipt = Omit<MathOfficialGateReceipt, 'attestation'>;
type UnsignedCandidateReview = Omit<MathCandidateReview, 'source' | 'attestation'>;
type UnsignedRouteProbeReceipt = Omit<MathRouteProbeReceipt, 'receiptId' | 'attestation'> &
  Partial<Pick<MathRouteProbeReceipt, 'receiptId'>>;
type UnsignedSolverReadyReceipt = Omit<MathSolverReadyReceipt, 'schema' | 'receiptId' | 'attestation'> &
  Partial<Pick<MathSolverReadyReceipt, 'receiptId'>>;

const stableValue = (value: unknown): unknown => {
  if (Array.isArray(value)) return value.map(stableValue);
  if (!value || typeof value !== 'object') return value;
  const input = value as Record<string, unknown>;
  const keys = Object.keys(input).toSorted((left, right) => left.localeCompare(right));
  const stable: Record<string, unknown> = {};
  for (const key of keys) stable[key] = stableValue(input[key]);
  return stable;
};

const canonical = (domain: string, value: unknown): string => `${domain}\u0000${JSON.stringify(stableValue(value))}`;

export const deriveMathematicsReceiptSecret = (masterSecret: string): string =>
  crypto.createHmac('sha256', masterSecret).update('deepscientist.mathematics.receipt-key.v1').digest('hex');

export const readMathematicsReceiptSecret = (): string | undefined => {
  const master = readFinanceReceiptSecret();
  return master ? deriveMathematicsReceiptSecret(master) : undefined;
};

const keyIdForSecret = (secret: string): string =>
  crypto.createHash('sha256').update(secret).digest('hex').slice(0, 16);

const signatureValue = (domain: string, value: unknown, secret: string): string =>
  crypto.createHmac('sha256', secret).update(canonical(domain, value)).digest('hex');

const sign = (domain: string, value: unknown, secret: string): MathReceiptAttestation => ({
  algorithm: 'hmac-sha256',
  keyId: keyIdForSecret(secret),
  value: signatureValue(domain, value, secret),
});

const verifies = (domain: string, value: unknown, attestation: MathReceiptAttestation, secret: string): boolean => {
  if (attestation.algorithm !== 'hmac-sha256' || attestation.keyId !== keyIdForSecret(secret)) return false;
  const actualValue = Buffer.from(attestation.value, 'hex');
  const expectedValue = Buffer.from(signatureValue(domain, value, secret), 'hex');
  return actualValue.length === expectedValue.length && crypto.timingSafeEqual(actualValue, expectedValue);
};

export const signMathOfficialGateReceipt = (
  receipt: UnsignedOfficialReceipt,
  secret: string
): MathOfficialGateReceipt => {
  // Normalize before signing so the signer and verifier canonicalize hashes,
  // whitespace, and optional fields identically.
  const normalized = normalizeMathOfficialGateReceipt({
    ...receipt,
    attestation: {
      algorithm: 'hmac-sha256',
      keyId: keyIdForSecret(secret),
      value: '0'.repeat(64),
    },
  });
  const { attestation: _placeholder, ...unsigned } = normalized;
  return normalizeMathOfficialGateReceipt({
    ...unsigned,
    attestation: sign('deepscientist.mathematics.official-gate.v1', unsigned, secret),
  });
};

export const verifyMathOfficialGateReceipt = (value: unknown, secret: string): MathOfficialGateReceipt | undefined => {
  try {
    const receipt = normalizeMathOfficialGateReceipt(value as MathOfficialGateReceipt);
    const { attestation, ...unsigned } = receipt;
    return verifies('deepscientist.mathematics.official-gate.v1', unsigned, attestation, secret) ? receipt : undefined;
  } catch {
    return undefined;
  }
};

export const signMathCandidateReview = (
  review: UnsignedCandidateReview,
  source: MathCandidateReviewSource,
  secret: string
): MathCandidateReview => {
  const normalized = normalizeMathCandidateReview(review as MathCandidateReview);
  // Legacy direct callers did not carry a lane; runtime-produced signatures
  // always do.  The default keeps old local fixtures readable while the
  // verifier below rejects any signed source that is not an independent
  // reviewer lane.
  const signedSource = { ...source, laneId: source.laneId || 'independent-review' };
  const signedPayload = { ...normalized, source: signedSource };
  return normalizeMathCandidateReview({
    ...signedPayload,
    attestation: sign('deepscientist.mathematics.candidate-review.v1', signedPayload, secret),
  });
};

export const verifyMathCandidateReview = (value: unknown, secret: string): MathCandidateReview | undefined => {
  try {
    const review = normalizeMathCandidateReview(value as MathCandidateReview);
    if (!review.source || !review.attestation) return undefined;
    const { attestation, ...signedPayload } = review;
    if (!verifies('deepscientist.mathematics.candidate-review.v1', signedPayload, attestation, secret)) {
      return undefined;
    }
    if (
      review.reviewerSessionId !== `${review.source.teamId}:${review.source.slotId}:${review.source.assignmentId}` ||
      review.source.deliveryId !== `${review.source.teamId}:${review.source.slotId}:${review.source.assignmentId}` ||
      review.source.laneId !== 'independent-review'
    ) {
      return undefined;
    }
    return review;
  } catch {
    return undefined;
  }
};

export const signMathSolverReadyReceipt = (
  input: UnsignedSolverReadyReceipt,
  secret: string
): MathSolverReadyReceipt => {
  const normalized = {
    schema: 'deepscientist.mathematics.solver-ready.v1' as const,
    receiptId:
      input.receiptId ||
      `solver-ready-${crypto
        .createHash('sha256')
        .update(canonical('deepscientist.mathematics.solver-ready.v1', input))
        .digest('hex')
        .slice(0, 24)}`,
    teamId: input.teamId.trim(),
    slotId: input.slotId.trim(),
    assignmentId: input.assignmentId.trim(),
    deliveryId: input.deliveryId.trim(),
    targetCommit: input.targetCommit.trim().toLowerCase(),
    statementHash: input.statementHash.trim().toLowerCase(),
    routeFingerprint: input.routeFingerprint.trim(),
    checkedAt: input.checkedAt,
  };
  if (
    !normalized.teamId ||
    !normalized.slotId ||
    !normalized.assignmentId ||
    !normalized.deliveryId ||
    !/^(?:[0-9a-f]{40}|[0-9a-f]{64})$/u.test(normalized.targetCommit) ||
    !/^[0-9a-f]{64}$/u.test(normalized.statementHash) ||
    !normalized.routeFingerprint ||
    !Number.isSafeInteger(normalized.checkedAt) ||
    normalized.checkedAt <= 0
  ) {
    throw new TypeError('Mathematics solver-ready receipt identity is invalid');
  }
  return Object.freeze({
    ...normalized,
    attestation: sign('deepscientist.mathematics.solver-ready.v1', normalized, secret),
  });
};

export const verifyMathSolverReadyReceipt = (
  value: unknown,
  secret: string
): MathSolverReadyReceipt | undefined => {
  try {
    if (!value || typeof value !== 'object' || Array.isArray(value)) return undefined;
    const receipt = value as MathSolverReadyReceipt;
    if (receipt.schema !== 'deepscientist.mathematics.solver-ready.v1' || !receipt.attestation) return undefined;
    const { attestation, ...unsigned } = receipt;
    if (!verifies('deepscientist.mathematics.solver-ready.v1', unsigned, attestation, secret)) return undefined;
    return signMathSolverReadyReceipt(unsigned, secret);
  } catch {
    return undefined;
  }
};

export const signMathRouteProbeReceipt = (input: UnsignedRouteProbeReceipt, secret: string): MathRouteProbeReceipt => {
  const receiptId =
    input.receiptId ||
    `route-probe-${crypto.createHash('sha256').update(canonical('deepscientist.mathematics.route-probe.v1', input)).digest('hex').slice(0, 24)}`;
  const normalized = normalizeMathRouteProbeReceipt({ ...input, receiptId });
  const { attestation: _attestation, ...unsigned } = normalized;
  return normalizeMathRouteProbeReceipt({
    ...normalized,
    attestation: sign('deepscientist.mathematics.route-probe.v1', unsigned, secret),
  });
};

export const verifyMathRouteProbeReceipt = (value: unknown, secret: string): MathRouteProbeReceipt | undefined => {
  try {
    const receipt = normalizeMathRouteProbeReceipt(value as MathRouteProbeReceipt);
    if (!receipt.attestation) return undefined;
    const { attestation, ...unsigned } = receipt;
    return verifies('deepscientist.mathematics.route-probe.v1', unsigned, attestation, secret) ? receipt : undefined;
  } catch {
    return undefined;
  }
};
