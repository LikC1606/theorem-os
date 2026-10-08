import { z } from 'zod';
import type {
  MathArtifactReadRequest,
  MathAssignmentRequest,
  MathIntegrationRequest,
  MathWorkerDelivery,
} from "../common/types/team/mathRuntimeContracts";
import type { ProtocolIssue } from "../common/types/team/mathematicsTeam";

const ID = /^[A-Za-z0-9_-]{1,128}$/u;
const COMMIT = /^(?:[a-f0-9]{40}|[a-f0-9]{64})$/u;
const bytes = (value: string): number => Buffer.byteLength(value, 'utf8');
const text = (limit: number) =>
  z
    .string()
    .trim()
    .min(1)
    .refine((value) => bytes(value) <= limit);
const identity = z.string().regex(ID);
const deliveryIdentity = z.string().regex(/^[A-Za-z0-9_:-]{1,512}$/u);

export function isMathRelativePath(value: string): boolean {
  return (
    Boolean(value) &&
    bytes(value) <= 512 &&
    ![...value].some(
      (character) => character.charCodeAt(0) < 32 || character.charCodeAt(0) === 127 || character === '\\'
    ) &&
    !value.startsWith('/') &&
    !/^[A-Za-z]:/u.test(value) &&
    value.split('/').every((part) => part !== '' && part !== '.' && part !== '..')
  );
}

const relativePath = z.string().refine(isMathRelativePath);
const digest = z.string().regex(/^[a-f0-9]{64}$/u);
const waitQuestionIds = z
  .array(z.string().regex(/^question_[a-f0-9]{64}$/u))
  .max(16)
  .refine((ids) => new Set(ids).size === ids.length, 'duplicate');
const waitProducerAssignmentIds = z
  .array(identity)
  .max(16)
  .refine((ids) => new Set(ids).size === ids.length, 'duplicate');
const waitEvidenceIds = z
  .array(digest)
  .max(256)
  .refine((ids) => new Set(ids).size === ids.length, 'duplicate');

export const mathResearchQuestionSchema = z
  .object({
    statement: text(1024),
    assumptions: z.array(text(256)).max(8),
    targetConnection: text(512),
  })
  .strict();

const verificationTarget = z
  .object({
    targetId: identity,
    pathRelative: relativePath,
    theoremName: text(512),
    statementHash: digest,
    leanStatementHash: digest.optional(),
    expectedSourceDeclarationHash: digest,
    claim: z.enum(['statement', 'negation']).optional(),
  })
  .strict();

export type MathArtifactReference =
  | Readonly<{ scheme: 'math-artifact'; runId: string; artifactId: string }>
  | Readonly<{ scheme: 'git-blob'; commit: string; path: string }>;

export function parseMathArtifactReference(value: string): MathArtifactReference | undefined {
  try {
    const url = new URL(value);
    if (url.username || url.password || url.port || url.search || url.hash) return undefined;
    if (url.protocol === 'math-artifact:' && bytes(value) <= 273) {
      const artifactId = url.pathname.slice(1);
      if (!ID.test(url.hostname) || !ID.test(artifactId) || value !== `math-artifact://${url.hostname}/${artifactId}`)
        return undefined;
      return { scheme: 'math-artifact', runId: url.hostname, artifactId };
    }
    if (url.protocol === 'git-blob:' && COMMIT.test(url.hostname) && bytes(value) <= 1612) {
      const decoded = decodeURIComponent(url.pathname.slice(1));
      if (!isMathRelativePath(decoded)) return undefined;
      // Compare the raw input as well: URL normalization must not hide traversal.
      const raw = value.slice(`git-blob://${url.hostname}/`.length);
      if (decodeURIComponent(raw) !== decoded || raw.includes('?') || raw.includes('#')) return undefined;
      return { scheme: 'git-blob', commit: url.hostname, path: decoded };
    }
  } catch {
    /* Invalid URL or UTF-8 percent encoding. */
  }
  return undefined;
}

const artifactRef = z.string().refine((value) => parseMathArtifactReference(value)?.scheme === 'math-artifact');
const evidenceRef = z.string().refine((value) => Boolean(parseMathArtifactReference(value)));

export const mathAssignmentShape = {
  idempotencyKey: identity,
  targetSlotId: identity,
  predecessorAssignmentId: identity.optional(),
  consumerAssignmentIds: z.array(identity).min(1).max(16).optional(),
  researchQuestion: mathResearchQuestionSchema.optional(),
  kind: z.enum(['research', 'formalize']),
  objective: text(2048),
  sharedWritePaths: z.array(relativePath).max(16).optional(),
  inputs: z
    .array(
      z.union([
        z.object({ path: relativePath, purpose: text(512) }).strict(),
        z.object({ artifactRef, purpose: text(512) }).strict(),
      ])
    )
    .max(16)
    .optional(),
  acceptance: z.array(text(512)).min(1).max(16),
  verificationTargets: z.array(verificationTarget).min(1).max(16).optional(),
} satisfies z.ZodRawShape;

export const mathDeliveryShape = {
  status: z.enum(['completed', 'blocked']),
  summary: text(2048),
  evidence: z
    .array(z.object({ kind: z.enum(['source', 'kernel', 'analysis', 'blocker']), ref: evidenceRef }).strict())
    .max(16),
  blockers: z.array(text(256)).max(16).optional(),
} satisfies z.ZodRawShape;

export const mathLiteProgressIntentSchema = z
  .object({
    summary: text(2048),
    files: z.array(relativePath).max(16).optional(),
    wait_for_question_ids: waitQuestionIds.optional(),
  })
  .strict()
  .superRefine((value, context) => {
    if (value.files && new Set(value.files).size !== value.files.length) {
      context.addIssue({ code: z.ZodIssueCode.custom, path: ['files'], message: 'duplicate' });
    }
  });

export const mathLiteProgressSnapshotSchema = z
  .object({
    schema: z.literal('deepscientist.math.progress-share.v1'),
    runId: identity,
    assignmentId: identity,
    targetSlotId: identity,
    bindingDigest: digest,
    shareId: digest,
    // Host-resolved destination, frozen with the share; never a mutable slot subscription.
    recipient: z.object({ assignmentId: identity, slotId: identity }).strict().optional(),
    wait_for_question_ids: waitQuestionIds.optional(),
    // Host-owned baseline fixes which producers and evidence were seen when waiting began.
    wait_producer_assignment_ids: waitProducerAssignmentIds.optional(),
    wait_evidence_ids: waitEvidenceIds.optional(),
    summary: text(2048),
    files: z.array(z.object({ pathRelative: relativePath, ref: artifactRef, sha256: digest }).strict()).max(16),
  })
  .strict();

export const mathLiteDeliveryIntentSchema = z
  .object({
    status: z.enum(['completed', 'blocked']),
    summary: text(2048),
    files: z.array(relativePath).max(16).optional(),
    blockers: z.array(text(256)).max(16).optional(),
  })
  .strict()
  .superRefine((value, context) => {
    if (value.status === 'blocked' && !value.blockers?.length) {
      context.addIssue({ code: z.ZodIssueCode.custom, path: ['blockers'], message: 'required' });
    }
    if (value.status === 'completed' && value.blockers?.length) {
      context.addIssue({ code: z.ZodIssueCode.custom, path: ['blockers'], message: 'forbidden' });
    }
    if (value.files && new Set(value.files).size !== value.files.length) {
      context.addIssue({ code: z.ZodIssueCode.custom, path: ['files'], message: 'duplicate' });
    }
  });

export type MathLiteDeliveryIntent = Readonly<{
  status: 'completed' | 'blocked';
  summary: string;
  files?: readonly string[];
  blockers?: readonly string[];
}>;

export function normalizeMathLiteDeliveryIntent(value: unknown): MathLiteDeliveryIntent {
  const parsed = mathLiteDeliveryIntentSchema.safeParse(value);
  if (!parsed.success || bytes(JSON.stringify(parsed.data)) >= 4096) {
    throw new Error('math_lite_delivery_invalid');
  }
  return Object.freeze({
    status: parsed.data.status!,
    summary: parsed.data.summary!,
    ...(parsed.data.files ? { files: Object.freeze([...parsed.data.files]) } : {}),
    ...(parsed.data.blockers ? { blockers: Object.freeze([...parsed.data.blockers]) } : {}),
  });
}

export const mathSourceArtifactSchema = z
  .object({
    schema: z.literal('deepscientist.math.source-artifact.v1'),
    assignmentId: identity,
    deliveryId: deliveryIdentity,
    baseCommit: z.string().regex(COMMIT),
    pathRelative: relativePath,
    mode: z.enum(['patch', 'file']),
    content: z.string().refine((value) => bytes(value) <= 5 * 1024 * 1024),
    contentSha256: digest,
    resultContentSha256: digest.optional(),
    verificationTargetId: identity,
    theoremName: text(512),
    statementHash: digest,
    leanStatementHash: digest.optional(),
    expectedSourceDeclarationHash: digest,
    claim: z.enum(['statement', 'negation']).optional(),
  })
  .strict()
  .superRefine((value, context) => {
    if (value.mode === 'patch' && !value.resultContentSha256) {
      context.addIssue({ code: z.ZodIssueCode.custom, path: ['resultContentSha256'], message: 'required' });
    }
    if (value.mode === 'file' && value.resultContentSha256 !== undefined) {
      context.addIssue({ code: z.ZodIssueCode.custom, path: ['resultContentSha256'], message: 'forbidden' });
    }
  });

export const mathIntegrationShape = {
  idempotencyKey: identity,
  deliveryIds: z.array(deliveryIdentity).max(8).default([]),
  sourceArtifacts: z.array(mathSourceArtifactSchema).max(8).optional(),
  declareSolverReady: z.boolean().optional(),
  supersedeAssignmentIds: z.array(identity).max(8).optional(),
} satisfies z.ZodRawShape;

export const mathArtifactReadShape = {
  ref: evidenceRef,
  offsetBytes: z.number().int().nonnegative().max(Number.MAX_SAFE_INTEGER).optional(),
  maxBytes: z.number().int().min(1).max(2048).optional(),
} satisfies z.ZodRawShape;

const OWNED_FIELDS = new Set([
  'assignmentId',
  'scopeId',
  'teamId',
  'runId',
  'baseCommit',
  'worktree',
  'branch',
  'taskHash',
  'workspace',
  'resultContract',
  'binding',
  'git',
  'headCommit',
  'changedFiles',
  'fastCheck',
  'alignmentCheck',
]);

export class MathWireValidationError extends Error {
  constructor(readonly issues: readonly ProtocolIssue[]) {
    super('Invalid mathematics request. Correct all reported fields.');
    this.name = 'MathWireValidationError';
  }
}

/** One issue per public field; never reflect values, arbitrary keys, or Zod diagnostics. */
function collectFields<T>(
  value: unknown,
  shape: z.ZodRawShape,
  limit: number,
  validate: (parsed: Record<string, unknown>, add: (path: string, code: ProtocolIssue['code']) => void) => void
): T {
  const issues = new Map<string, ProtocolIssue>();
  const add = (path: string, code: ProtocolIssue['code']): void => {
    const old = issues.get(path);
    if (!old || code === 'unauthorized' || (old.code !== 'unauthorized' && code < old.code)) {
      issues.set(path, {
        path,
        code,
        message:
          code === 'runtime_owned_field'
            ? 'Remove runtime-owned fields.'
            : 'Correct this field using the declared schema.',
      });
    }
  };
  if (!value || typeof value !== 'object' || Array.isArray(value)) {
    throw new MathWireValidationError([{ path: '$', code: 'invalid', message: 'Expected a request object.' }]);
  }
  const input = value as Record<string, unknown>;
  const parsed: Record<string, unknown> = {};
  for (const [key, schema] of Object.entries(shape)) {
    const result = schema.safeParse(input[key]);
    if (result.success) {
      if (result.data !== undefined) parsed[key] = result.data;
    } else add(key, input[key] === undefined ? 'required' : 'invalid');
  }
  const unknown = Object.keys(input).filter((key) => !Object.hasOwn(shape, key));
  if (unknown.length) add('$', unknown.some((key) => OWNED_FIELDS.has(key)) ? 'runtime_owned_field' : 'invalid');
  validate(parsed, add);
  // Valid individual fields can still exceed the total wire budget.
  if (bytes(JSON.stringify(parsed)) >= limit) add('$', 'payload_too_large');
  if (issues.size)
    throw new MathWireValidationError(
      [...issues.values()].toSorted((a, b) => (a.path < b.path ? -1 : a.path > b.path ? 1 : 0))
    );
  return parsed as T;
}

export function normalizeMathAssignment(value: unknown, workerIds?: ReadonlySet<string>): MathAssignmentRequest {
  return collectFields(value, mathAssignmentShape, 8192, (parsed, add) => {
    if (typeof parsed.targetSlotId === 'string' && workerIds && !workerIds.has(parsed.targetSlotId))
      add('targetSlotId', 'unauthorized');
    if (Array.isArray(parsed.consumerAssignmentIds)) {
      if (parsed.kind !== 'research') add('consumerAssignmentIds', 'invalid');
      if (new Set(parsed.consumerAssignmentIds).size !== parsed.consumerAssignmentIds.length)
        add('consumerAssignmentIds', 'conflict');
    }
    if (parsed.researchQuestion !== undefined && parsed.kind !== 'research') add('researchQuestion', 'invalid');
    if (
      Array.isArray(parsed.sharedWritePaths) &&
      new Set(parsed.sharedWritePaths).size !== parsed.sharedWritePaths.length
    )
      add('sharedWritePaths', 'conflict');
    if (Array.isArray(parsed.verificationTargets)) {
      const targets = parsed.verificationTargets as Array<{
        targetId: string;
        pathRelative: string;
        theoremName: string;
        statementHash: string;
        expectedSourceDeclarationHash: string;
        leanStatementHash?: string;
        claim?: string;
      }>;
      if (
        new Set(targets.map((target) => target.targetId)).size !== targets.length ||
        new Set(targets.map((target) => `${target.pathRelative}\u0000${target.theoremName}`)).size !== targets.length
      )
        add('verificationTargets', 'conflict');
      const byDeclaration = new Map<string, (typeof targets)[number]>();
      for (const target of targets) {
        const key = `${target.pathRelative}\u0000${target.theoremName}`;
        const previous = byDeclaration.get(key);
        if (
          previous &&
          (previous.statementHash !== target.statementHash ||
            previous.leanStatementHash !== target.leanStatementHash ||
            previous.expectedSourceDeclarationHash !== target.expectedSourceDeclarationHash ||
            (previous.claim ?? 'statement') !== (target.claim ?? 'statement'))
        ) {
          add('verificationTargets', 'conflict');
        }
        byDeclaration.set(key, target);
      }
      if (parsed.kind !== 'formalize') add('verificationTargets', 'invalid');
    }
  });
}

export function normalizeMathDelivery(value: unknown): MathWorkerDelivery {
  return collectFields(value, mathDeliveryShape, 4096, (parsed, add) => {
    if (parsed.status === 'blocked' && (!Array.isArray(parsed.blockers) || !parsed.blockers.length))
      add('blockers', 'required');
    if (parsed.status === 'completed' && Array.isArray(parsed.blockers) && parsed.blockers.length)
      add('blockers', 'invalid');
  });
}

export function normalizeMathIntegration(value: unknown): MathIntegrationRequest {
  const hasSources = Boolean(value && typeof value === 'object' && 'sourceArtifacts' in value);
  return collectFields(
    value,
    mathIntegrationShape,
    hasSources ? 8 * 6 * 5 * 1024 * 1024 + 65536 : 4096,
    (parsed, add) => {
      const sourceArtifacts = Array.isArray(parsed.sourceArtifacts)
        ? (parsed.sourceArtifacts as Array<{ deliveryId: string; pathRelative: string; verificationTargetId: string }>)
        : undefined;
      if (
        sourceArtifacts &&
        (!Array.isArray(parsed.deliveryIds) ||
          !parsed.deliveryIds.length ||
          sourceArtifacts.some((artifact) => !(parsed.deliveryIds as string[]).includes(artifact.deliveryId)) ||
          (parsed.deliveryIds as string[]).some(
            (deliveryId) => !sourceArtifacts.some((artifact) => artifact.deliveryId === deliveryId)
          ) ||
          new Set(
            sourceArtifacts.map(
              (artifact) => `${artifact.deliveryId}\u0000${artifact.pathRelative}\u0000${artifact.verificationTargetId}`
            )
          ).size !== sourceArtifacts.length)
      )
        add('sourceArtifacts', 'conflict');
      for (const field of ['deliveryIds', 'supersedeAssignmentIds']) {
        const ids = parsed[field];
        if (Array.isArray(ids) && new Set(ids).size !== ids.length) add(field, 'conflict');
      }
      if (
        !(Array.isArray(parsed.deliveryIds) && parsed.deliveryIds.length) &&
        !(Array.isArray(parsed.supersedeAssignmentIds) && parsed.supersedeAssignmentIds.length) &&
        parsed.declareSolverReady !== true
      )
        add('$', 'invalid');
    }
  );
}

export function normalizeMathArtifactRead(value: unknown): MathArtifactReadRequest {
  return collectFields(value, mathArtifactReadShape, 4096, () => {});
}

export const normalizedMathObjective = (objective: string): string =>
  objective.normalize('NFKC').trim().replace(/\s+/gu, ' ');

export function mathPathsOverlap(left: string, right: string): boolean {
  return left === right || left.startsWith(`${right}/`) || right.startsWith(`${left}/`);
}

/**
 * Progress summaries are advisory evidence. Normalize presentation-only
 * differences before deriving the idempotency identity so a Worker cannot
 * create a new Lead wake by rewrapping the same finding. Source bytes and
 * artifact hashes remain part of the identity and are never normalized.
 */
export function normalizeMathProgressSummary(summary: string): string {
  return summary
    .replace(/\r\n?/gu, '\n')
    .split('\n')
    .map((line) => line.trim().replace(/[ \t]+/gu, ' '))
    .join('\n')
    .trim();
}
