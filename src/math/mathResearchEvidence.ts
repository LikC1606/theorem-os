import crypto from 'node:crypto';
import { z } from 'zod';
import type { MathResearchFinding } from "../common/types/team/mathematicsTeam";
import { canonicalMathJson } from "./mathRuntimeIo";
import { readMathematicsReceiptSecret } from "./receiptAttestation";
import { readMathRunHistoryIdentity } from "./mathRunHistory";

const prefix = 'math-observation:';
const digest = z.string().regex(/^[a-f0-9]{64}$/u);
export const mathObservationProvenanceSchema = z
  .object({
    inputDigest: digest,
    casesDigest: digest,
    sourceDigest: digest.optional(),
    expression: z.string().max(1000),
    precondition: z.string().max(500).optional(),
    mode: z.string().max(80),
    outcome: z.string().max(80),
    casesChecked: z.number().int().nonnegative(),
    casesRequested: z.number().int().nonnegative(),
    designDigest: digest.optional(),
    witnessDigest: digest.optional(),
  })
  .strict();
export type MathObservationProvenance = z.infer<typeof mathObservationProvenanceSchema>;
const observation = z
  .object({
    schema: z.literal('deepscientist.math.observation.v1'),
    runIdentity: z.string(),
    teamId: z.string(),
    assignmentId: z.string(),
    grade: z.literal('runtime_checked'),
    scope: z.literal('bounded_observation'),
    statement: z.string().min(1).max(1500),
    fingerprint: z.string().regex(/^[a-f0-9]{64}$/u),
    provenance: mathObservationProvenanceSchema.optional(),
  })
  .strict();

/** Only the executing tool signs observations; the scope never establishes the parent theorem. */
export function signMathResearchObservation(
  input: {
    teamId: string;
    assignmentId: string;
    statement: string;
    fingerprint: string;
    provenance?: MathObservationProvenance;
  },
  secret = readMathematicsReceiptSecret(),
  runIdentity = readMathRunHistoryIdentity()
) {
  if (!secret || !runIdentity) return undefined;
  const payload = observation.parse({
    schema: 'deepscientist.math.observation.v1',
    ...input,
    runIdentity,
    grade: 'runtime_checked',
    scope: 'bounded_observation',
  });
  const encoded = Buffer.from(canonicalMathJson(payload)).toString('base64url');
  const signature = crypto
    .createHmac('sha256', secret)
    .update(prefix + encoded)
    .digest('hex');
  return { ...payload, reference: `${prefix}${encoded}.${signature}` };
}

export function readTrustedMathResearchEvidence(
  finding: Pick<MathResearchFinding, 'evidenceRefs'>,
  binding: { teamId: string; assignmentId: string },
  secret = readMathematicsReceiptSecret(),
  runIdentity = readMathRunHistoryIdentity()
) {
  if (!secret || !runIdentity) return [];
  return finding.evidenceRefs.flatMap((reference) => {
    if (!reference.startsWith(prefix) || reference.length > 32_000) return [];
    try {
      const [encoded, signature, extra] = reference.slice(prefix.length).split('.');
      if (extra || !/^[a-f0-9]{64}$/u.test(signature ?? '')) return [];
      const expected = crypto
        .createHmac('sha256', secret)
        .update(prefix + encoded)
        .digest();
      if (!crypto.timingSafeEqual(expected, Buffer.from(signature, 'hex'))) return [];
      const result = observation.parse(JSON.parse(Buffer.from(encoded, 'base64url').toString('utf8')));
      if (
        result.runIdentity !== runIdentity ||
        result.teamId !== binding.teamId ||
        result.assignmentId !== binding.assignmentId
      )
        return [];
      return [
        {
          grade: result.grade,
          scope: result.scope,
          statement: result.statement,
          fingerprint: result.provenance
            ? crypto
                .createHash('sha256')
                .update(canonicalMathJson({ fingerprint: result.fingerprint, provenance: result.provenance }))
                .digest('hex')
            : result.fingerprint,
          proofStateFingerprint: result.fingerprint,
          ...(result.provenance ? { provenance: result.provenance } : {}),
          reference,
        },
      ];
    } catch {
      return [];
    }
  });
}
