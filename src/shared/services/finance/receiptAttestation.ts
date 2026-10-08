import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { financeToolReceiptSchema, type FinanceToolReceipt } from "../../../common/chat/finance/index";
import {
  BUILTIN_FINANCE_RECEIPT_KEY_PATH_ENV,
  BUILTIN_FINANCE_RECEIPT_SECRET_ENV,
  resolveBuiltinFinanceReceiptKeyPath,
} from "../../../mcp/constants";

type UnsignedFinanceToolReceipt = Omit<FinanceToolReceipt, 'attestation'>;

const stableValue = (value: unknown): unknown => {
  if (Array.isArray(value)) return value.map(stableValue);
  if (!value || typeof value !== 'object') return value;
  return Object.fromEntries(
    Object.entries(value as Record<string, unknown>)
      .toSorted(([left], [right]) => left.localeCompare(right))
      .map(([key, item]) => [key, stableValue(item)])
  );
};

const canonicalReceipt = (receipt: UnsignedFinanceToolReceipt): string => JSON.stringify(stableValue(receipt));

const readFinanceReceiptMasterSecret = (): string | undefined => {
  const configured = process.env[BUILTIN_FINANCE_RECEIPT_SECRET_ENV]?.trim();
  if (configured) return configured;
  const keyPath = resolveBuiltinFinanceReceiptKeyPath(process.env[BUILTIN_FINANCE_RECEIPT_KEY_PATH_ENV]);
  try {
    const existing = fs.readFileSync(keyPath, 'utf8').trim();
    if (existing) return existing;
  } catch {
    // Create the local key below. The exclusive create handles concurrent MCP startup.
  }
  // Inside a mathematics isolation sandbox the host mounts its key. A locally
  // minted key would sign receipts the host can never verify (run 23 attempt
  // 16), so fail closed instead of generating one.
  if (process.env.DEEPSCIENTIST_MATH_ISOLATION_WORKSPACE) return undefined;
  const generated = crypto.randomBytes(32).toString('hex');
  try {
    fs.mkdirSync(path.dirname(keyPath), { recursive: true });
    const fd = fs.openSync(keyPath, 'wx', 0o600);
    try {
      fs.writeFileSync(fd, `${generated}\n`, 'utf8');
    } finally {
      fs.closeSync(fd);
    }
    return generated;
  } catch {
    try {
      const existing = fs.readFileSync(keyPath, 'utf8').trim();
      return existing || undefined;
    } catch {
      return undefined;
    }
  }
};

export const deriveFinanceReceiptSecret = (masterSecret: string, runId?: string): string =>
  runId?.trim()
    ? crypto
        .createHmac('sha256', masterSecret)
        .update(`deepscientist.finance.receipt.v1\u0000${runId.trim()}`)
        .digest('hex')
    : masterSecret;

export const readFinanceReceiptSecret = (runId?: string): string | undefined => {
  const master = readFinanceReceiptMasterSecret();
  return master ? deriveFinanceReceiptSecret(master, runId) : undefined;
};

export const signFinanceToolReceipt = (receipt: UnsignedFinanceToolReceipt, secret: string): FinanceToolReceipt => {
  const keyId = crypto.createHash('sha256').update(secret).digest('hex').slice(0, 16);
  const value = crypto.createHmac('sha256', secret).update(canonicalReceipt(receipt)).digest('hex');
  return {
    ...receipt,
    attestation: { algorithm: 'hmac-sha256', keyId, value },
  };
};

export const verifyFinanceToolReceipt = (value: unknown, secret: string): FinanceToolReceipt | undefined => {
  const parsed = financeToolReceiptSchema.safeParse(value);
  if (!parsed.success) return undefined;
  const receipt = parsed.data as FinanceToolReceipt;
  const { attestation, ...unsigned } = receipt;
  const candidates = [secret, deriveFinanceReceiptSecret(secret, receipt.runId)];
  for (const candidate of candidates) {
    const expectedKeyId = crypto.createHash('sha256').update(candidate).digest('hex').slice(0, 16);
    const expectedValue = crypto.createHmac('sha256', candidate).update(canonicalReceipt(unsigned)).digest('hex');
    if (attestation.keyId !== expectedKeyId) continue;
    const actual = Buffer.from(attestation.value, 'hex');
    const expected = Buffer.from(expectedValue, 'hex');
    if (actual.length === expected.length && crypto.timingSafeEqual(actual, expected)) return receipt;
  }
  return undefined;
};

export const verifiedFinanceReceiptIds = (
  receipts: readonly FinanceToolReceipt[],
  secret: string | undefined
): Set<string> => {
  if (!secret) return new Set();
  return new Set(
    receipts
      .map((receipt) => verifyFinanceToolReceipt(receipt, secret)?.receiptId)
      .filter((receiptId): receiptId is string => Boolean(receiptId))
  );
};
