import { z } from 'zod';

export const FINANCE_CONSENT_REQUEST_SCHEMA = 'deepscientist.finance.consent_request.v1' as const;
export const FINANCE_CONSENT_GRANT_SCHEMA = 'deepscientist.finance.consent_grant.v1' as const;

export const FINANCE_CONSENT_SCOPES = [
  'finance_research_write',
  'finance_monitor_schedule',
  'finance_cloud_image',
  'finance_external_code',
] as const;

export type FinanceConsentScope = (typeof FINANCE_CONSENT_SCOPES)[number];

export type FinanceConsentDisclosure = {
  kind: 'external_code_execution';
  endpoint: string;
  model: string;
  estimatedCalls: number;
  selectedFiles: Array<{
    path: string;
    sha256: string;
    bytes: number;
  }>;
  selectedFileBytes: number;
  warnings: string[];
};

export type FinanceConsentRequest = {
  schema: typeof FINANCE_CONSENT_REQUEST_SCHEMA;
  runId: string;
  consentScope: FinanceConsentScope;
  action: string;
  resourceId?: string;
  disclosure?: FinanceConsentDisclosure;
  disclosureHash?: string;
  expiresInMs?: number;
};

export type FinanceConsentGrant = {
  schema: typeof FINANCE_CONSENT_GRANT_SCHEMA;
  consentId: string;
  decisionToken: string;
  runId: string;
  consentScope: FinanceConsentScope;
  action: string;
  resourceId?: string;
  disclosureHash?: string;
  confirmedAt: string;
  expiresAt: string;
  confirmationHash: string;
};

export const financeConsentDisclosureCanonicalJson = (value: FinanceConsentDisclosure): string =>
  JSON.stringify({
    kind: value.kind,
    endpoint: value.endpoint,
    model: value.model,
    estimatedCalls: value.estimatedCalls,
    selectedFiles: value.selectedFiles.map((file) => ({
      path: file.path,
      sha256: file.sha256,
      bytes: file.bytes,
    })),
    selectedFileBytes: value.selectedFileBytes,
    warnings: value.warnings,
  });

const boundedString = (max: number) => z.string().trim().min(1).max(max);
const isoTimestamp = z.string().datetime({ offset: true });
const sha256 = z.string().regex(/^[a-f0-9]{64}$/iu);
const financeConsentDisclosureSchema = z
  .object({
    kind: z.literal('external_code_execution'),
    endpoint: boundedString(500),
    model: boundedString(200),
    estimatedCalls: z.number().int().min(0).max(100_000),
    selectedFiles: z
      .array(
        z
          .object({
            path: boundedString(500),
            sha256,
            bytes: z
              .number()
              .int()
              .min(1)
              .max(1024 * 1024),
          })
          .strict()
      )
      .max(16),
    selectedFileBytes: z
      .number()
      .int()
      .min(0)
      .max(16 * 1024 * 1024),
    warnings: z.array(boundedString(500)).min(1).max(8),
  })
  .strict();

export const financeConsentRequestSchema = z
  .object({
    schema: z.literal(FINANCE_CONSENT_REQUEST_SCHEMA),
    runId: boundedString(160),
    consentScope: z.enum(FINANCE_CONSENT_SCOPES),
    action: boundedString(160),
    resourceId: boundedString(240).optional(),
    disclosure: financeConsentDisclosureSchema.optional(),
    disclosureHash: sha256.optional(),
    expiresInMs: z
      .number()
      .int()
      .min(60_000)
      .max(15 * 60_000)
      .optional(),
  })
  .strict();

export const financeConsentGrantSchema = z
  .object({
    schema: z.literal(FINANCE_CONSENT_GRANT_SCHEMA),
    consentId: boundedString(160),
    decisionToken: boundedString(240),
    runId: boundedString(160),
    consentScope: z.enum(FINANCE_CONSENT_SCOPES),
    action: boundedString(160),
    resourceId: boundedString(240).optional(),
    disclosureHash: sha256.optional(),
    confirmedAt: isoTimestamp,
    expiresAt: isoTimestamp,
    confirmationHash: sha256,
  })
  .strict();

export const normalizeFinanceConsentRequest = (value: unknown): FinanceConsentRequest | undefined => {
  const parsed = financeConsentRequestSchema.safeParse(value);
  return parsed.success ? (parsed.data as FinanceConsentRequest) : undefined;
};

export const normalizeFinanceConsentGrant = (value: unknown): FinanceConsentGrant | undefined => {
  const parsed = financeConsentGrantSchema.safeParse(value);
  return parsed.success ? (parsed.data as FinanceConsentGrant) : undefined;
};
