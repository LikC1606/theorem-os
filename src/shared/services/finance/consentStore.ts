import crypto from 'node:crypto';
import {
  FINANCE_CONSENT_GRANT_SCHEMA,
  financeConsentDisclosureCanonicalJson,
  type FinanceConsentGrant,
  type FinanceConsentRequest,
  type FinanceConsentScope,
} from "../../../common/chat/finance/index";

export type FinanceConsentConsumeInput = {
  consentId: string;
  decisionToken: string;
  runId: string;
  consentScope: FinanceConsentScope;
  action: string;
  resourceId?: string;
  disclosureHash?: string;
  confirmationHash: string;
};

export type FinanceConsentConsumeResult =
  | { ok: true; grant: Omit<FinanceConsentGrant, 'decisionToken'>; consumedAt: string }
  | {
      ok: false;
      error: 'invalid_request' | 'permission_denied';
      reason: 'unknown' | 'expired' | 'already_consumed' | 'scope_mismatch';
    };

type StoredGrant = {
  grant: FinanceConsentGrant;
  consumedAt?: string;
};

const DEFAULT_CONSENT_TTL_MS = 5 * 60_000;
const RETENTION_MS = 15 * 60_000;

const confirmationHash = (grant: Omit<FinanceConsentGrant, 'confirmationHash' | 'decisionToken'>): string =>
  crypto.createHash('sha256').update(JSON.stringify(grant)).digest('hex');

const sameOptionalString = (left: string | undefined, right: string | undefined): boolean =>
  (left || undefined) === (right || undefined);

export const hashFinanceConsentDisclosure = (disclosure: NonNullable<FinanceConsentRequest['disclosure']>): string =>
  crypto.createHash('sha256').update(financeConsentDisclosureCanonicalJson(disclosure)).digest('hex');

export class FinanceConsentStore {
  private readonly grants = new Map<string, StoredGrant>();

  issue(request: FinanceConsentRequest, confirmedAtMs = Date.now()): FinanceConsentGrant {
    this.cleanup(confirmedAtMs);
    const consentId = `finance_consent_${crypto.randomUUID()}`;
    const decisionToken = `${crypto.randomUUID()}${crypto.randomUUID().replaceAll('-', '')}`;
    const confirmedAt = new Date(confirmedAtMs).toISOString();
    const expiresAt = new Date(confirmedAtMs + (request.expiresInMs || DEFAULT_CONSENT_TTL_MS)).toISOString();
    const disclosureHash = request.disclosure ? hashFinanceConsentDisclosure(request.disclosure) : undefined;
    if (disclosureHash !== request.disclosureHash) {
      throw new Error('Finance consent disclosure hash is missing or invalid.');
    }
    const unsigned = {
      schema: FINANCE_CONSENT_GRANT_SCHEMA,
      consentId,
      runId: request.runId,
      consentScope: request.consentScope,
      action: request.action,
      ...(request.resourceId ? { resourceId: request.resourceId } : {}),
      ...(disclosureHash ? { disclosureHash } : {}),
      confirmedAt,
      expiresAt,
    } as const;
    const grant: FinanceConsentGrant = {
      ...unsigned,
      decisionToken,
      confirmationHash: confirmationHash(unsigned),
    };
    this.grants.set(decisionToken, { grant });
    return grant;
  }

  consume(input: FinanceConsentConsumeInput, consumedAtMs = Date.now()): FinanceConsentConsumeResult {
    this.cleanup(consumedAtMs);
    const stored = this.grants.get(input.decisionToken);
    if (!stored) return { ok: false, error: 'permission_denied', reason: 'unknown' };
    if (stored.consumedAt) return { ok: false, error: 'permission_denied', reason: 'already_consumed' };
    if (Date.parse(stored.grant.expiresAt) <= consumedAtMs) {
      return { ok: false, error: 'permission_denied', reason: 'expired' };
    }
    const matches =
      stored.grant.consentId === input.consentId &&
      stored.grant.runId === input.runId &&
      stored.grant.consentScope === input.consentScope &&
      stored.grant.action === input.action &&
      sameOptionalString(stored.grant.resourceId, input.resourceId) &&
      sameOptionalString(stored.grant.disclosureHash, input.disclosureHash) &&
      stored.grant.confirmationHash === input.confirmationHash;
    if (!matches) return { ok: false, error: 'permission_denied', reason: 'scope_mismatch' };

    const consumedAt = new Date(consumedAtMs).toISOString();
    stored.consumedAt = consumedAt;
    const { decisionToken: _decisionToken, ...grant } = stored.grant;
    return { ok: true, grant, consumedAt };
  }

  private cleanup(nowMs: number): void {
    for (const [token, stored] of this.grants) {
      const expiry = Date.parse(stored.grant.expiresAt);
      const consumed = stored.consumedAt ? Date.parse(stored.consumedAt) : undefined;
      if (expiry + RETENTION_MS <= nowMs || (consumed != null && consumed + RETENTION_MS <= nowMs)) {
        this.grants.delete(token);
      }
    }
  }
}
