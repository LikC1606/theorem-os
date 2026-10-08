/**
 * Shared identity rules for Research Team transport keys.
 * Local assignment and delivery ids may remain readable and long; Core HTTP
 * idempotency keys must stay within its 128-character contract.
 */
import crypto from 'node:crypto';

const CORE_IDEMPOTENCY_KEY_MAX_LENGTH = 128;
const VALID_OPAQUE_ID = /^[A-Za-z0-9][A-Za-z0-9._:-]*$/u;

export const canonicalResearchTeamIdempotencyKey = (value: unknown, field = 'idempotency_key'): string => {
  const normalized = normalizeResearchTeamOpaqueId(value, field);
  if (normalized.length <= CORE_IDEMPOTENCY_KEY_MAX_LENGTH) return normalized;
  return `ds-idempotency-v1-${crypto.createHash('sha256').update(normalized, 'utf8').digest('hex').slice(0, 64)}`;
};

export const normalizeResearchTeamOpaqueId = (value: unknown, field = 'id'): string => {
  const normalized = String(value ?? '').trim();
  if (!normalized || !VALID_OPAQUE_ID.test(normalized)) throw new Error(`Research Team ${field} is invalid`);
  return normalized;
};

export const createResearchTeamTransportKey = (identity: string): string =>
  `ds-delivery-v1-${crypto.createHash('sha256').update(identity, 'utf8').digest('hex').slice(0, 64)}`;
