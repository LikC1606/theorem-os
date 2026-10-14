import crypto from 'node:crypto';
import { normalizeMathOfficialGateReceipt, type MathOfficialGateReceipt, type MathReceiptAttestation } from "./contracts";
import { readMathReceiptMasterSecret } from "./receiptKey";
import { canonicalMathJson } from './mathRuntimeIo';

type UnsignedOfficialReceipt = Omit<MathOfficialGateReceipt, 'attestation'>;

// Keep the historical receipt ordering while sharing the canonical JSON implementation.
const canonical = (domain: string, value: unknown): string =>
  `${domain}\u0000${canonicalMathJson(value, (a, b) => a.localeCompare(b))}`;

export const deriveMathematicsReceiptSecret = (masterSecret: string): string =>
  crypto.createHmac('sha256', masterSecret).update('deepscientist.mathematics.receipt-key.v1').digest('hex');

export const readMathematicsReceiptSecret = (): string | undefined => {
  const master = readMathReceiptMasterSecret();
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
