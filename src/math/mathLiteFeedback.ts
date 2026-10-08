import fs from 'node:fs';
import path from 'node:path';
import { z } from 'zod';
import { readMathRunBinding, resolveMathRunProjectPaths, assertMathCanonicalPath } from "./mathRunBinding";
import {
  canonicalMathJson,
  mathDigest,
  readMathJson,
  writeMathJsonDurable,
  withMathRuntimeLease,
} from "./mathRuntimeIo";
import {
  verifyMathRunInputsEnvironment,
  verifyMathRunInputs,
  MATH_RUN_INPUTS_ENV,
  type MathRunInputs,
} from "./mathRunInputs";
import { projectRuntimeMathAssignmentToExecutionView } from "./mathAssignmentExecutionAdapter";
import { normalizeRuntimeMathAssignment } from "./mathAssignmentJournal";
import { mathAssignmentResearchQuestionId, mathAssignmentResearchEvidenceVersion } from "./mathAssignmentResearchGraph";
import { mathLiteProgressSnapshotSchema, normalizeMathProgressSummary } from "./mathPublicWire";
import { selectMathV2IntegrationDelivery } from "./mathIntegrationSelector";
import { readMathLiteSealedSet } from "./mathWorkerDeliveryAdapter";
import { MathArtifactStore, MathArtifactError, type MathArtifactAccess } from "./mathArtifactStore";
import { parseMathArtifactReference } from "./mathPublicWire";
import { listProjectGitResearchTeamAssignments } from "../project-git/index";
import { recordMathProofImpact } from "./mathProofImpact";
import { readMathLiteBlockerLineage, readVerifiedMathBlockerReference } from "./mathLiteBlockerContext";

const feedbackUseSchema = z.object({
  ref: z.string(),
  sourceHash: z.string().regex(/^[a-f0-9]{64}$/u),
  sourceAssignmentId: z.string(),
  sourceReceiptHash: z.string(),
  recipientReceiptHash: z.string(),
  status: z.enum(['read', 'checked', 'check_failed', 'check_incomplete']),
  environmentId: z.string().min(1).optional(),
  diagnostic: z.string().max(2048).optional(),
});

export function mathLiteFeedbackCursor(binding: ReturnType<typeof readMathRunBinding>, assignmentId: string) {
  const directory = path.join(path.dirname(binding.artifactStoreRoot), 'lite-feedback');
  assertMathCanonicalPath(directory);
  fs.mkdirSync(directory, { recursive: true, mode: 0o700 });
  const file = path.join(directory, `${mathDigest(assignmentId)}.json`);
  assertMathCanonicalPath(file);
  const schema = z.object({
    seen: z.array(z.string().regex(/^[a-f0-9]{64}$/u)),
    last: z.array(z.string()),
    uses: z.array(feedbackUseSchema).max(256).default([]),
    usageSeen: z.array(z.string()).default([]),
    usageLast: z.array(z.string()).default([]),
    waitShareId: z
      .string()
      .regex(/^[a-f0-9]{64}$/u)
      .optional(),
    appliedWaitShares: z.array(z.string().regex(/^[a-f0-9]{64}$/u)).default([]),
    releasedWait: z
      .object({
        shareId: z.string().regex(/^[a-f0-9]{64}$/u),
        state: z.enum(['source_changed', 'evidence_available', 'producer_ended']),
      })
      .strict()
      .optional(),
    blockedEvidenceRevision: z
      .string()
      .regex(/^[a-f0-9]{64}$/u)
      .optional(),
  });
  return { file, read: () => schema.parse(fs.existsSync(file) ? readMathJson(file) : { seen: [], last: [] }) };
}

/** Acknowledged explicit clears always release a wait; an old wait retry never re-arms it. */
export async function acknowledgeMathLiteResearchWait(
  binding: ReturnType<typeof readMathRunBinding>,
  share: ReturnType<typeof mathLiteProgressSnapshotSchema.parse>,
  signal: AbortSignal
): Promise<void> {
  if (share.wait_for_question_ids === undefined) return;
  const cursor = mathLiteFeedbackCursor(binding, share.assignmentId);
  await withMathRuntimeLease(
    { lockPath: `${cursor.file}.lock`, flockExecutable: '/usr/bin/flock', signal },
    async (lease) => {
      const previous = cursor.read();
      if (previous.appliedWaitShares.includes(share.shareId) && share.wait_for_question_ids!.length > 0) return;
      lease.assertHeld();
      writeMathJsonDurable(cursor.file, {
        ...previous,
        waitShareId: share.shareId,
        appliedWaitShares: [...new Set([...previous.appliedWaitShares, share.shareId])],
      });
    }
  );
}

export function mathLiteProofContextArtifactId(
  binding: ReturnType<typeof readMathRunBinding>,
  assignmentId: string
): string {
  return `proof_context_${mathDigest(canonicalMathJson({ binding, assignmentId }))}`;
}

/** Shared original-target input for proof and research assignments accepted in the first batch. */
export function mathLiteInitialProofContextArtifactId(binding: ReturnType<typeof readMathRunBinding>): string {
  return `initial_proof_context_${mathDigest(canonicalMathJson(binding))}`;
}

export function readLatestMathLiteProgress(
  binding: ReturnType<typeof readMathRunBinding>,
  receipt: ReturnType<typeof listProjectGitResearchTeamAssignments>[number],
  selectedFile?: string,
  requireFiles = false
): ReturnType<typeof mathLiteProgressSnapshotSchema.parse> | undefined {
  projectRuntimeMathAssignmentToExecutionView(receipt.assignment, {
    expectedRunId: binding.runId,
    expectedBindingDigest: mathDigest(canonicalMathJson(binding)),
    expectedTargetSlotId: receipt.slotId,
    ...(receipt.preparedGit?.baseCommit ? { expectedBaseCommit: receipt.preparedGit.baseCommit } : {}),
  });
  const directory = path.join(path.dirname(binding.artifactStoreRoot), 'lite-shares', receipt.assignmentId);
  if (!fs.existsSync(directory)) return undefined;
  assertMathCanonicalPath(directory);
  // A wait's cursor update is its atomic acknowledgment after Core accepts the
  // share. A crash may leave the compatibility .ack file unwritten.
  const cursor = mathLiteFeedbackCursor(binding, receipt.assignmentId).read();
  const cursorAcknowledgedFile =
    cursor.waitShareId && cursor.appliedWaitShares.includes(cursor.waitShareId)
      ? `${cursor.waitShareId}.json`
      : undefined;
  const files = (selectedFile ? [selectedFile] : fs.readdirSync(directory))
    .filter(
      (file) =>
        /^[a-f0-9]{64}\.json$/u.test(file) &&
        fs.existsSync(path.join(directory, file)) &&
        (fs.existsSync(path.join(directory, `${file}.ack`)) || file === cursorAcknowledgedFile)
    )
    .toSorted(
      (left, right) =>
        fs.statSync(path.join(directory, right)).mtimeMs - fs.statSync(path.join(directory, left)).mtimeMs
    );
  if (!files.length) return undefined;
  if (requireFiles) {
    for (const candidate of files) {
      const snapshot = readLatestMathLiteProgress(binding, receipt, candidate);
      if (snapshot?.files.length) return snapshot;
    }
    return undefined;
  }
  if (selectedFile && !files.includes(selectedFile)) return undefined;
  const file = path.join(directory, selectedFile ?? files[0]!);
  assertMathCanonicalPath(file);
  assertMathCanonicalPath(`${file}.ack`);
  const raw = readMathJson(file);
  const expectedIdentity = {
    shareId: path.basename(file, '.json'),
    runId: binding.runId,
    assignmentId: receipt.assignmentId,
    targetSlotId: receipt.slotId,
    bindingDigest: mathDigest(canonicalMathJson(binding)),
  };
  // A malformed optional field must not mask an already identifiable foreign report.
  if (raw && typeof raw === 'object' && !Array.isArray(raw)) {
    const identity = raw as Record<string, unknown>;
    if (
      Object.entries(expectedIdentity).some(
        ([key, expected]) => identity[key] !== undefined && identity[key] !== expected
      )
    )
      throw new Error('math_share_snapshot_integrity');
  }
  const parsed = mathLiteProgressSnapshotSchema.parse(raw);
  let acknowledgement: unknown;
  const hasAcknowledgementFile = fs.existsSync(`${file}.ack`);
  if (hasAcknowledgementFile) {
    try {
      acknowledgement = readMathJson(`${file}.ack`);
    } catch (error) {
      if (error instanceof SyntaxError) throw new Error('math_share_snapshot_integrity', { cause: error });
      throw error;
    }
  }
  const cursorAcknowledgedWait =
    !hasAcknowledgementFile &&
    path.basename(file) === cursorAcknowledgedFile &&
    parsed.wait_for_question_ids !== undefined;
  const { shareId, ...snapshot } = parsed;
  if (
    shareId !== path.basename(file, '.json') ||
    (!cursorAcknowledgedWait &&
      (!acknowledgement ||
        typeof acknowledgement !== 'object' ||
        (acknowledgement as Record<string, unknown>).shareId !== shareId)) ||
    mathDigest(canonicalMathJson({ ...snapshot, summary: normalizeMathProgressSummary(snapshot.summary) })) !==
      shareId ||
    snapshot.runId !== binding.runId ||
    snapshot.assignmentId !== receipt.assignmentId ||
    snapshot.targetSlotId !== receipt.slotId ||
    snapshot.bindingDigest !== mathDigest(canonicalMathJson(binding))
  )
    throw new Error('math_share_snapshot_integrity');
  return parsed;
}

function readRecentMathLiteProgress(
  binding: ReturnType<typeof readMathRunBinding>,
  receipt: ReturnType<typeof listProjectGitResearchTeamAssignments>[number],
  limit?: number
): NonNullable<ReturnType<typeof readLatestMathLiteProgress>>[] {
  const directory = path.join(path.dirname(binding.artifactStoreRoot), 'lite-shares', receipt.assignmentId);
  if (!fs.existsSync(directory)) return [];
  assertMathCanonicalPath(directory);
  const files = fs
    .readdirSync(directory)
    .filter((file) => /^[a-f0-9]{64}\.json$/u.test(file) && fs.existsSync(path.join(directory, `${file}.ack`)))
    .toSorted(
      (left, right) =>
        fs.statSync(path.join(directory, right)).mtimeMs - fs.statSync(path.join(directory, left)).mtimeMs ||
        right.localeCompare(left)
    )
    .slice(0, limit)
    .toReversed();
  return files.map((file) => readLatestMathLiteProgress(binding, receipt, file)!);
}

type MathLiteFeedbackCapability = { teamId: string; slotId: string; roleKind: string; projectRoot: string };
const operationContexts = new WeakMap<
  object,
  { capability: string; signal: AbortSignal; inputs?: MathRunInputs; environment?: string }
>();

export function readMathLiteProofLineage(
  resolvedCapability: MathLiteFeedbackCapability,
  signal: AbortSignal,
  runInputs?: MathRunInputs,
  allowResearch = false
) {
  if (!runInputs) verifyMathRunInputsEnvironment(process.env);
  signal.throwIfAborted();
  const binding = readMathRunBinding(verifyMathRunInputs(runInputs ?? JSON.parse(process.env[MATH_RUN_INPUTS_ENV]!)));
  const readAssignments = () =>
    listProjectGitResearchTeamAssignments({
      workspace: binding.workspace,
      teamId: resolvedCapability.teamId,
      strict: true,
    });
  const receipts = readAssignments();
  if (
    receipts.some(
      (receipt) =>
        receipt.slotId === resolvedCapability.slotId &&
        receipt.state === 'accepted' &&
        (receipt.supersessionPending || receipt.budgetCancellation)
    )
  )
    throw new Error('math_feedback_assignment_changed');
  const active = receipts.filter(
    (receipt) =>
      receipt.schema === 'deepscientist.research_team_assignment.v2' &&
      receipt.slotId === resolvedCapability.slotId &&
      receipt.state === 'accepted' &&
      !receipt.delivery &&
      !receipt.integration &&
      !receipt.supersessionPending &&
      !receipt.budgetCancellation
  );
  if (resolvedCapability.roleKind !== 'worker' || active.length !== 1)
    throw new Error('math_feedback_assignment_unavailable');
  const target = active[0]!;
  const validate = (receipt: typeof target) =>
    projectRuntimeMathAssignmentToExecutionView(receipt.assignment, {
      expectedRunId: binding.runId,
      expectedBindingDigest: mathDigest(canonicalMathJson(binding)),
      expectedTargetSlotId: receipt.slotId,
      ...(receipt.preparedGit?.baseCommit ? { expectedBaseCommit: receipt.preparedGit.baseCommit } : {}),
    });
  const targetKind = validate(target).kind;
  if (targetKind !== 'formalize' && !(allowResearch && targetKind === 'research'))
    throw new Error('math_feedback_formalizer_required');
  // A Researcher's frozen input references bind its findings to this proof task.
  const ownRefs = new Set<string>();
  const lineage: Array<typeof target> = [];
  let ancestor: typeof target | undefined = target;
  while (ancestor) {
    if (lineage.some((entry) => entry.assignmentId === ancestor!.assignmentId))
      throw new Error('math_feedback_predecessor_cycle');
    const view = validate(ancestor);
    if (
      ancestor.teamId !== target.teamId ||
      ancestor.slotId !== target.slotId ||
      view.kind !== targetKind ||
      normalizeRuntimeMathAssignment(ancestor.assignment).scopeId !==
        normalizeRuntimeMathAssignment(target.assignment).scopeId
    )
      throw new Error('math_feedback_predecessor_identity');
    lineage.push(ancestor);
    ownRefs.add(`math-artifact://${binding.runId}/${mathLiteProofContextArtifactId(binding, ancestor.assignmentId)}`);
    const initialContextId = mathLiteInitialProofContextArtifactId(binding);
    const initialContextRef = `math-artifact://${binding.runId}/${initialContextId}`;
    const ancestorAssignment = normalizeRuntimeMathAssignment(ancestor.assignment);
    if (
      view.kind === 'formalize' &&
      ancestorAssignment.artifactGrants.includes(initialContextId) &&
      ancestorAssignment.request.inputs?.some(
        (input) => 'artifactRef' in input && input.artifactRef === initialContextRef
      )
    )
      ownRefs.add(initialContextRef);
    const directory = path.join(path.dirname(binding.artifactStoreRoot), 'lite-shares', ancestor.assignmentId);
    if (fs.existsSync(directory)) {
      assertMathCanonicalPath(directory);
      for (const file of fs.readdirSync(directory)) {
        if (!/^[a-f0-9]{64}\.json$/u.test(file)) continue;
        for (const entry of readLatestMathLiteProgress(binding, ancestor, file)?.files ?? []) ownRefs.add(entry.ref);
      }
    }
    if (ancestor.delivery) {
      const selection = selectMathV2IntegrationDelivery(ancestor, ancestor.delivery.deliveryId, {
        expectedRunId: binding.runId,
        expectedBindingDigest: mathDigest(canonicalMathJson(binding)),
      });
      for (const evidence of selection.delivery.delivery.evidence) ownRefs.add(evidence.ref);
    }
    const parentId = normalizeRuntimeMathAssignment(ancestor.assignment).request.predecessorAssignmentId;
    ancestor = parentId ? receipts.find((entry) => entry.assignmentId === parentId) : undefined;
    if (parentId && (!ancestor || ancestor.state !== 'superseded'))
      throw new Error('math_feedback_predecessor_unavailable');
  }
  resolveMathRunProjectPaths(binding, resolvedCapability.projectRoot);
  const context = { binding, readAssignments, receipts, target, lineage, ownRefs, validate };
  operationContexts.set(context, {
    capability: canonicalMathJson(resolvedCapability),
    signal,
    inputs: runInputs,
    environment: runInputs ? undefined : process.env[MATH_RUN_INPUTS_ENV],
  });
  return context;
}

export type MathLiteOperationContext = ReturnType<typeof readMathLiteProofLineage>;

/** Host-only reuse within one tool request. Async consumers still recheck live WAL before returning. */
export function resolveMathLiteOperationContext(
  capability: MathLiteFeedbackCapability,
  signal: AbortSignal,
  runInputs?: MathRunInputs,
  context?: MathLiteOperationContext,
  allowResearch = false
): MathLiteOperationContext {
  signal.throwIfAborted();
  if (!context) return readMathLiteProofLineage(capability, signal, runInputs, allowResearch);
  const owner = operationContexts.get(context);
  if (
    !owner ||
    owner.signal !== signal ||
    owner.capability !== canonicalMathJson(capability) ||
    owner.inputs !== runInputs ||
    owner.environment !== (runInputs ? undefined : process.env[MATH_RUN_INPUTS_ENV])
  )
    throw new Error('math_feedback_operation_identity');
  if (!allowResearch && context.validate(context.target).kind !== 'formalize')
    throw new Error('math_feedback_formalizer_required');
  return context;
}

// Run-scoped immutable readers verify stat/identity on every read. Keep only a
// small number of stores; no provider/config data or model text enters the key.
const feedbackStores = new Map<string, Promise<MathArtifactStore>>();
async function feedbackStore(binding: ReturnType<typeof readMathRunBinding>) {
  const key = `${binding.artifactStoreRoot}\0${binding.runId}`;
  let opening = feedbackStores.get(key);
  if (!opening) {
    opening = (async () => {
      const store = new MathArtifactStore({
        runRoot: path.dirname(binding.artifactStoreRoot),
        runId: binding.runId,
        flockExecutable: '/usr/bin/flock',
      });
      await store.initialize();
      return store;
    })();
    feedbackStores.set(key, opening);
    opening.catch(() => {
      if (feedbackStores.get(key) === opening) feedbackStores.delete(key);
    });
    if (feedbackStores.size > 8) {
      const oldest = feedbackStores.keys().next().value!;
      const retired = feedbackStores.get(oldest)!;
      feedbackStores.delete(oldest);
      void retired.then((store) => store.closeReaders()).catch((): void => undefined);
    }
  }
  return opening;
}

export async function readMathLiteFeedback({
  resolvedCapability,
  signal,
  consume = false,
  automatic = false,
  historyLimit,
  historyQuery,
  artifactRefOnly,
  runInputs,
  operationContext,
  onEvidenceRevision,
}: {
  resolvedCapability: MathLiteFeedbackCapability;
  signal: AbortSignal;
  consume?: boolean;
  automatic?: boolean;
  historyLimit?: number;
  historyQuery?: string;
  /** Host-only authorization lookup: never consumes notifications or scans attachment bodies. */
  artifactRefOnly?: string;
  runInputs?: MathRunInputs;
  operationContext?: MathLiteOperationContext;
  /** Host-only change observation, independent of whether a notification was already consumed. */
  onEvidenceRevision?: (revision: string) => void;
}) {
  if (
    historyLimit !== undefined &&
    (consume || automatic || !Number.isSafeInteger(historyLimit) || historyLimit < 1 || historyLimit > 6)
  )
    throw new Error('math_feedback_history_limit_invalid');
  const { binding, readAssignments, receipts, target, lineage, ownRefs, validate } = resolveMathLiteOperationContext(
    resolvedCapability,
    signal,
    runInputs,
    operationContext,
    true
  );
  const researchRecipient = validate(target).kind === 'research';
  const initiallySeen = new Set(automatic ? mathLiteFeedbackCursor(binding, target.assignmentId).read().seen : []);
  const materialized = new Set<string>();
  const store = await feedbackStore(binding);
  const findings: Array<{
    shareId: string;
    summary: string;
    sourceAssignmentId: string;
    fullRefs: string[];
    notes: Array<{ path: string; text: string; truncated: boolean; ref: string; sha256: string }>;
    deliveryId?: string;
    source?: 'final_report';
    provisional?: true;
  }> = [];
  const deferredNotes = new Map<string, readonly Readonly<{ pathRelative: string; ref: string; sha256: string }>[]>();
  const sources: Array<typeof target> = [];
  const outstandingResearchAssignmentIds: string[] = [];
  const readNotes = async (
    shareId: string,
    files: readonly Readonly<{ pathRelative: string; ref: string; sha256: string }>[]
  ) => {
    if (automatic && (initiallySeen.has(shareId) || materialized.size >= 4)) return [];
    materialized.add(shareId);
    const notes: Array<{ path: string; text: string; truncated: boolean; ref: string; sha256: string }> = [];
    for (const file of files
      .filter((entry) => entry.pathRelative.endsWith('.md'))
      .slice(0, automatic || historyLimit !== undefined ? 1 : undefined)) {
      let text = '';
      let offsetBytes = 0;
      const limit = automatic ? 1024 : historyLimit ? 512 : 4096;
      for (;;) {
        signal.throwIfAborted();
        // Store.read verifies the complete object's content hash, including bytes
        // beyond this excerpt. Do not reread a whole attachment to display 512 chars.
        const chunk = await store.read(
          { ref: file.ref, offsetBytes, maxBytes: Math.min(2048, limit) },
          { role: 'lead' }
        );
        if (chunk.sha256 !== file.sha256) throw new Error('math_share_note_integrity');
        text += chunk.text;
        if (chunk.nextOffsetBytes === undefined || Buffer.byteLength(text, 'utf8') >= limit) {
          const characters = Array.from(text);
          notes.push({
            path: file.pathRelative,
            text: characters.slice(0, limit).join(''),
            ref: file.ref,
            sha256: file.sha256,
            truncated: chunk.nextOffsetBytes !== undefined || characters.length > limit,
          });
          break;
        }
        offsetBytes = chunk.nextOffsetBytes;
      }
    }
    return notes;
  };
  const notesFor = async (
    shareId: string,
    files: readonly Readonly<{ pathRelative: string; ref: string; sha256: string }>[]
  ): Promise<(typeof findings)[number]['notes']> => {
    deferredNotes.set(shareId, files);
    return [];
  };
  for (const receipt of receipts) {
    if (
      receipt.schema !== 'deepscientist.research_team_assignment.v2' ||
      (receipt.state !== 'accepted' && receipt.state !== 'integrated') ||
      receipt.supersessionPending ||
      receipt.budgetCancellation
    )
      continue;
    const raw = normalizeRuntimeMathAssignment(receipt.assignment);
    if (raw.runId !== binding.runId || raw.request.kind !== 'research') continue;
    validate(receipt);
    if (receipt.assignmentId === target.assignmentId) continue;
    // Explicit consumers narrow the existing artifact-grant boundary. A legal
    // proof successor inherits its predecessor's findings through verified lineage.
    if (
      raw.request.consumerAssignmentIds &&
      !researchRecipient &&
      !lineage.some((owner) => raw.request.consumerAssignmentIds!.includes(owner.assignmentId))
    )
      continue;
    // A proof owner receives findings bound to its supplied evidence. A research
    // peer receives only shares explicitly addressed to this exact assignment.
    const addressed = researchRecipient
      ? readRecentMathLiteProgress(binding, receipt).filter(
          (share) => share.recipient?.assignmentId === target.assignmentId && share.recipient.slotId === target.slotId
        )
      : undefined;
    if (
      researchRecipient
        ? !addressed?.length
        : !raw.request.inputs?.some(
            (input) =>
              'artifactRef' in input &&
              ownRefs.has(input.artifactRef) &&
              raw.artifactGrants.includes(input.artifactRef.split('/').at(-1) ?? '')
          )
    )
      continue;
    sources.push(receipt);
    if (receipt.state === 'accepted' && !receipt.delivery && !receipt.integration)
      outstandingResearchAssignmentIds.push(receipt.assignmentId);
    const sharedHistory =
      addressed ??
      (historyLimit === undefined && !artifactRefOnly
        ? [readLatestMathLiteProgress(binding, receipt)].filter(
            (shared): shared is NonNullable<typeof shared> => shared !== undefined
          )
        : readRecentMathLiteProgress(binding, receipt));
    for (const shared of sharedHistory) {
      findings.push({
        shareId: shared.shareId,
        sourceAssignmentId: receipt.assignmentId,
        fullRefs: shared.files.map((file) => file.ref),
        summary: shared.summary,
        // eslint-disable-next-line no-await-in-loop -- sequential reads enforce the automatic attachment budget.
        notes: await notesFor(
          shared.shareId,
          (shared.files ?? []).filter(
            (file): file is Readonly<{ pathRelative: string; ref: string; sha256: string }> =>
              typeof file.pathRelative === 'string' && typeof file.ref === 'string' && typeof file.sha256 === 'string'
          )
        ),
      });
    }
    if (receipt.delivery && !researchRecipient) {
      const selected = selectMathV2IntegrationDelivery(receipt, receipt.delivery.deliveryId, {
        expectedRunId: binding.runId,
        expectedBindingDigest: mathDigest(canonicalMathJson(binding)),
      });
      const sealed = readMathLiteSealedSet(path.dirname(binding.artifactStoreRoot), selected.delivery.deliveryId);
      if (
        sealed &&
        (sealed.runId !== binding.runId ||
          sealed.assignmentId !== receipt.assignmentId ||
          sealed.targetSlotId !== receipt.slotId ||
          canonicalMathJson(sealed.delivery) !== canonicalMathJson(selected.delivery.delivery))
      )
        throw new Error('math_feedback_delivery_identity');
      // A final report can correct the last progress share.
      // Keep both, with distinct stable identities, so a
      // Worker cannot silently miss that correction.
      const finalShareId = mathDigest(`final-report:${selected.delivery.deliveryId}:${selected.delivery.payloadHash}`);
      const deliveredAt = Date.parse(receipt.delivery.deliveredAt);
      recordMathProofImpact(
        { runRoot: path.dirname(binding.artifactStoreRoot), runId: binding.runId },
        {
          kind: 'shared',
          runId: binding.runId,
          assignmentId: receipt.assignmentId,
          shareId: finalShareId,
          observedAt: Number.isFinite(deliveredAt) ? deliveredAt : null,
        }
      );
      findings.push({
        shareId: finalShareId,
        sourceAssignmentId: receipt.assignmentId,
        fullRefs: (sealed?.files ?? []).map((file) => file.ref),
        deliveryId: selected.delivery.deliveryId,
        source: 'final_report',
        provisional: true,
        summary: selected.delivery.delivery.summary,
        // eslint-disable-next-line no-await-in-loop -- sequential reads enforce the automatic attachment budget.
        notes: await notesFor(finalShareId, sealed?.files ?? []),
      });
    }
  }
  // Select verified metadata before opening any attachment. Lexical overlap is
  // recall only: it never adjudicates a mathematical claim or prevents a check.
  const terms = new Set(
    (historyQuery ?? normalizeRuntimeMathAssignment(target.assignment).request.objective).match(
      /[\p{L}_][\p{L}\p{N}_'.]*/gu
    ) ?? []
  );
  const overlap = (finding: (typeof findings)[number]) => {
    const source = sources.find((entry) => entry.assignmentId === finding.sourceAssignmentId);
    const text = `${source ? normalizeRuntimeMathAssignment(source.assignment).request.objective : ''} ${finding.summary}`;
    const words = new Set(text.match(/[\p{L}_][\p{L}\p{N}_'.]*/gu) ?? []);
    return [...terms].filter((term) => words.has(term)).length;
  };
  const summaryRef = (finding: (typeof findings)[number]) =>
    `math-artifact://${binding.runId}/research-text-${mathDigest(
      canonicalMathJson({
        assignmentId: finding.sourceAssignmentId,
        evidenceId: finding.shareId,
        summary: finding.summary,
      })
    )}`;
  let historyFindings = findings;
  if (artifactRefOnly) {
    historyFindings = findings.filter(
      (finding) => finding.fullRefs.includes(artifactRefOnly) || summaryRef(finding) === artifactRefOnly
    );
  } else if (historyLimit !== undefined) {
    historyFindings = findings
      .map((finding, index) => ({ finding, index, overlap: overlap(finding) }))
      .sort((a, b) => b.overlap - a.overlap || b.index - a.index)
      .slice(0, historyLimit)
      .map(({ finding }) => finding);
  } else if (automatic) {
    historyFindings = findings.filter((finding) => !initiallySeen.has(finding.shareId)).slice(0, 4);
  }
  for (const finding of historyFindings) {
    signal.throwIfAborted();
    const ref = summaryRef(finding);
    // The full authenticated summary is itself an immutable artifact, including
    // summary-only shares and final corrections. Never turn a share ID into a URI.
    try {
      const existing = await store.read({ ref, maxBytes: 8 }, { role: 'lead' });
      if (existing.sha256 !== mathDigest(finding.summary)) throw new Error('math_share_note_integrity');
    } catch (error) {
      if (!(error instanceof MathArtifactError) || error.code !== 'not_found') throw error;
      await store.publishText({
        artifactId: ref.split('/').at(-1)!,
        assignmentId: finding.sourceAssignmentId,
        kind: 'evidence',
        sensitivity: 'solver-visible',
        mediaType: 'text/plain',
        text: finding.summary,
      });
    }
    finding.fullRefs = [ref, ...finding.fullRefs];
    if (!artifactRefOnly) finding.notes = await readNotes(finding.shareId, deferredNotes.get(finding.shareId) ?? []);
  }
  signal.throwIfAborted();
  const latest = readAssignments();
  for (const expected of [...lineage, ...sources]) {
    const current = latest.find((receipt) => receipt.assignmentId === expected.assignmentId);
    if (!current || canonicalMathJson(current) !== canonicalMathJson(expected))
      throw new Error('math_feedback_assignment_changed');
  }
  let batch = historyFindings;
  const newlyReceived = new Set<string>();
  // An empty automatic batch has nothing to consume or replay; avoid taking its write lease.
  if (consume && (historyFindings.length > 0 || !automatic)) {
    const cursor = mathLiteFeedbackCursor(binding, target.assignmentId);
    batch = await withMathRuntimeLease(
      { lockPath: `${cursor.file}.lock`, flockExecutable: '/usr/bin/flock', signal: signal },
      async (lease) => {
        const previous = cursor.read();
        const unseen = historyFindings
          .filter(
            (finding) => !previous.seen.includes(finding.shareId) && (!automatic || materialized.has(finding.shareId))
          )
          .slice(0, automatic ? 4 : undefined);
        // Replay the last batch after a lost MCP response, but do
        // not append previously consumed reports to a new batch.
        if (!unseen.length)
          return automatic ? [] : findings.filter((finding) => previous.last.includes(finding.shareId));
        lease.assertHeld();
        signal.throwIfAborted();
        writeMathJsonDurable(cursor.file, {
          ...previous,
          seen: [...new Set([...previous.seen, ...unseen.map((finding) => finding.shareId)])],
          last: unseen.map((finding) => finding.shareId),
        });
        unseen.forEach((finding) => newlyReceived.add(finding.shareId));
        return unseen;
      }
    );
    for (const finding of batch)
      recordMathProofImpact(
        { runRoot: path.dirname(binding.artifactStoreRoot), runId: binding.runId },
        {
          kind: 'received',
          runId: binding.runId,
          assignmentId: finding.sourceAssignmentId,
          consumerAssignmentId: target.assignmentId,
          shareId: finding.shareId,
          observedAt: newlyReceived.has(finding.shareId) ? Date.now() : null,
        }
      );
    for (const finding of batch)
      for (const note of finding.notes)
        recordMathProofImpact(
          { runRoot: path.dirname(binding.artifactStoreRoot), runId: binding.runId },
          {
            kind: 'artifact_read',
            runId: binding.runId,
            assignmentId: finding.sourceAssignmentId,
            consumerAssignmentId: target.assignmentId,
            shareId: finding.shareId,
            artifactId: note.ref.split('/').at(-1),
            observedAt: newlyReceived.has(finding.shareId) ? Date.now() : null,
          }
        );
  }
  // Host observations of this task's own frozen material, not proof acceptance.
  // Bind both WAL receipts: a revoked or replaced relationship cannot leak old diagnostics.
  const ownUsageRefs = new Set(ownRefs);
  for (const source of lineage) {
    for (const share of readRecentMathLiteProgress(binding, source)) {
      ownUsageRefs.add(
        summaryRef({
          sourceAssignmentId: source.assignmentId,
          shareId: share.shareId,
          summary: share.summary,
          fullRefs: [],
          notes: [],
        })
      );
    }
  }
  let usageFeedback = receipts
    .flatMap((recipient) => {
      if (
        recipient.teamId !== target.teamId ||
        recipient.state !== 'accepted' ||
        recipient.supersessionPending ||
        recipient.budgetCancellation
      )
        return [];
      const observations = mathLiteFeedbackCursor(binding, recipient.assignmentId).read().uses;
      return observations
        .filter((observation) => {
          const source = lineage.find((entry) => entry.assignmentId === observation.sourceAssignmentId);
          return (
            source &&
            observation.sourceReceiptHash === mathDigest(canonicalMathJson(source)) &&
            observation.recipientReceiptHash === mathDigest(canonicalMathJson(recipient)) &&
            ownUsageRefs.has(observation.ref)
          );
        })
        .map((observation) => ({
          ref: observation.ref,
          sourceHash: observation.sourceHash,
          recipientAssignmentId: recipient.assignmentId,
          status: observation.status,
          ...(observation.environmentId ? { environmentId: observation.environmentId } : {}),
          ...(observation.diagnostic ? { diagnostic: observation.diagnostic } : {}),
          provisional: true as const,
        }));
    })
    .slice(-32);

  if (consume && !artifactRefOnly && usageFeedback.length) {
    const cursor = mathLiteFeedbackCursor(binding, target.assignmentId);
    const identity = (observation: (typeof usageFeedback)[number]) => mathDigest(canonicalMathJson(observation));
    usageFeedback = await withMathRuntimeLease(
      { lockPath: `${cursor.file}.lock`, flockExecutable: '/usr/bin/flock', signal },
      async (lease) => {
        const previous = cursor.read();
        const unseen = usageFeedback.filter((entry) => !previous.usageSeen.includes(identity(entry)));
        if (!unseen.length)
          return automatic ? [] : usageFeedback.filter((entry) => previous.usageLast.includes(identity(entry)));
        lease.assertHeld();
        signal.throwIfAborted();
        writeMathJsonDurable(cursor.file, {
          ...previous,
          usageSeen: [...new Set([...previous.usageSeen, ...unseen.map(identity)])].slice(-256),
          usageLast: unseen.map(identity),
        });
        return unseen;
      }
    );
  }
  signal.throwIfAborted();
  // Research evidence is identified by immutable authorized assignments and
  // content-addressed findings. Advisory integration and receipt timestamps do
  // not create new mathematical evidence or justify repeating the same blocker.
  // Revoked/superseded relationships still change this revision because the
  // validated sources/findings above no longer include them.
  onEvidenceRevision?.(
    mathDigest(
      canonicalMathJson([
        sources
          .map((source) => [source.assignmentId, normalizeRuntimeMathAssignment(source.assignment).payloadHash])
          .toSorted((left, right) => left[0].localeCompare(right[0])),
        findings
          .map((finding) => [finding.sourceAssignmentId, finding.shareId])
          .toSorted((left, right) => left[0].localeCompare(right[0]) || left[1].localeCompare(right[1])),
      ])
    )
  );
  const researchQuestions = sources.flatMap((source) => {
    const assignment = normalizeRuntimeMathAssignment(source.assignment);
    const question = assignment.request.researchQuestion;
    const latestQuestionShare = question ? readLatestMathLiteProgress(binding, source) : undefined;
    return question
      ? [
          {
            question_id: mathAssignmentResearchQuestionId(binding, question),
            evidence_version: mathAssignmentResearchEvidenceVersion(assignment.request, assignment.baseCommit),
            producer_assignment_id: source.assignmentId,
            pending: outstandingResearchAssignmentIds.includes(source.assignmentId),
            finding_ids: [
              ...new Set([
                ...(latestQuestionShare ? [latestQuestionShare.shareId] : []),
                ...findings
                  .filter(
                    (finding) => finding.sourceAssignmentId === source.assignmentId && finding.source === 'final_report'
                  )
                  .map((finding) => finding.shareId),
              ]),
            ],
            ...question,
          },
        ]
      : [];
  });
  const waitCursor = mathLiteFeedbackCursor(binding, target.assignmentId);
  const waitCursorState = waitCursor.read();
  const waitShareId = waitCursorState.waitShareId;
  const wait = readLatestMathLiteProgress(binding, target, waitShareId ? `${waitShareId}.json` : undefined);
  if (waitShareId && !wait) throw new Error('math_share_snapshot_integrity');
  let waitState: 'none' | 'waiting' | 'evidence_available' | 'producer_ended' | 'source_changed' = 'none';
  let waitingOnResearch: string[] = [];
  if (wait && waitCursorState.releasedWait?.shareId === wait.shareId) {
    waitState = waitCursorState.releasedWait.state;
  } else if (!researchRecipient && wait?.wait_for_question_ids?.length) {
    if (!wait.wait_producer_assignment_ids?.length || !wait.wait_evidence_ids)
      throw new Error('math_share_snapshot_integrity');
    const assignment = normalizeRuntimeMathAssignment(target.assignment);
    const required = assignment.request.verificationTargets?.map((entry) => entry.pathRelative) ?? [];
    const root = target.preparedGit?.solverProjectRoot;
    // The wait belongs to this exact proof snapshot. Ordinary source progress
    // revokes it instead of suspending independent work on a newer proof state.
    const currentSource =
      root &&
      required.length > 0 &&
      required.every((file) => {
        const frozen = wait.files.find((entry) => entry.pathRelative === file);
        if (!frozen) return false;
        const source = path.resolve(root, assignment.sourceRootRelative, file);
        try {
          assertMathCanonicalPath(source);
          const stat = fs.statSync(source);
          return stat.isFile() && stat.size <= 5 * 1024 * 1024 && mathDigest(fs.readFileSync(source)) === frozen.sha256;
        } catch {
          return false;
        }
      });
    if (!currentSource) waitState = 'source_changed';
    else {
      const producers = researchQuestions.filter(
        (question) =>
          wait.wait_for_question_ids!.includes(question.question_id) &&
          wait.wait_producer_assignment_ids!.includes(question.producer_assignment_id)
      );
      const newEvidence = producers.some((question) =>
        question.finding_ids.some((id) => !wait.wait_evidence_ids!.includes(id))
      );
      const active = producers
        .filter((question) => question.pending)
        .map((question) => question.producer_assignment_id);
      // A report permits a consumer to inspect evidence, not to mark a theorem
      // solved. Cancellation, lost authority or completion also release a wait.
      if (newEvidence) waitState = 'evidence_available';
      else if (active.length !== wait.wait_producer_assignment_ids.length) waitState = 'producer_ended';
      else {
        waitState = 'waiting';
        waitingOnResearch = active;
      }
    }
    if (waitState === 'source_changed' || waitState === 'evidence_available' || waitState === 'producer_ended') {
      const releasedState = waitState;
      await withMathRuntimeLease(
        { lockPath: `${waitCursor.file}.lock`, flockExecutable: '/usr/bin/flock', signal },
        async (lease) => {
          const previous = waitCursor.read();
          // A newer explicit wait wins over this observation of an older one.
          if (previous.waitShareId !== wait.shareId || previous.releasedWait?.shareId === wait.shareId) return;
          lease.assertHeld();
          signal.throwIfAborted();
          writeMathJsonDurable(waitCursor.file, {
            ...previous,
            releasedWait: { shareId: wait.shareId, state: releasedState },
          });
        }
      );
    }
  }
  return {
    status: 'feedback',
    provisional: true,
    findings: automatic
      ? batch.map((finding) => ({
          ...finding,
          summary: Array.from(finding.summary).slice(0, 512).join(''),
          summaryTruncated: Array.from(finding.summary).length > 512,
        }))
      : batch,
    outstanding_research_assignment_ids: outstandingResearchAssignmentIds,
    research_questions: researchQuestions,
    waiting_on_research_assignment_ids: waitingOnResearch,
    research_wait: { state: waitState, question_ids: wait?.wait_for_question_ids ?? [] },
    usageFeedback,
    instruction:
      'These are provisional findings for your current task, not theorem acceptance. Compare their exact hypotheses and source version with your current question before applying them. Use attached feedback first. Read cited immutable full text when assumptions were omitted; request feedback for missing material, a new approach to this blocker, or lost responses. Host usage feedback records byte access or a source check, never adoption or original-target acceptance. check_incomplete requires retry, not a changed mathematical claim. Do not poll unchanged checkpoints.',
  };
}

/** Called only after an actual artifact read or kernel check. Authorization alone is not consumption.
 * These durable host diagnostics never certify adoption or the original theorem. */
export async function recordMathLiteFeedbackUse(input: {
  resolvedCapability: MathLiteFeedbackCapability;
  signal: AbortSignal;
  runInputs?: MathRunInputs;
  ref: string;
  sourceHash: string;
  status: 'read' | 'checked' | 'check_failed' | 'check_incomplete';
  environmentId?: string;
  diagnostic?: string;
}): Promise<'recorded' | 'unchanged' | 'persistence_unconfirmed'> {
  if (input.status !== 'read' && !input.environmentId) throw new Error('math_feedback_usage_environment_required');
  const context = readMathLiteProofLineage(input.resolvedCapability, input.signal, input.runInputs, true);
  const feedback = await readMathLiteFeedback({
    resolvedCapability: input.resolvedCapability,
    signal: input.signal,
    runInputs: input.runInputs,
    artifactRefOnly: input.ref,
  });
  const finding = feedback.findings.find((entry) => entry.fullRefs.includes(input.ref));
  const source = context.receipts.find((entry) => entry.assignmentId === finding?.sourceAssignmentId);
  const parsed = parseMathArtifactReference(input.ref);
  if (!source || parsed?.scheme !== 'math-artifact' || parsed.runId !== context.binding.runId)
    throw new MathArtifactError('unauthorized');
  const store = await feedbackStore(context.binding);
  const artifact = await store.read(
    { ref: input.ref, maxBytes: 1 },
    {
      role: 'worker',
      assignmentId: context.target.assignmentId,
      grants: new Set([parsed.artifactId]),
    }
  );
  if (artifact.sha256 !== input.sourceHash) throw new Error('math_feedback_usage_source_changed');
  const observation = feedbackUseSchema.parse({
    ref: input.ref,
    sourceHash: input.sourceHash,
    sourceAssignmentId: source.assignmentId,
    sourceReceiptHash: mathDigest(canonicalMathJson(source)),
    recipientReceiptHash: mathDigest(canonicalMathJson(context.target)),
    status: input.status,
    ...(input.environmentId ? { environmentId: input.environmentId } : {}),
    ...(input.diagnostic ? { diagnostic: input.diagnostic.slice(0, 2048) } : {}),
  });
  const cursor = mathLiteFeedbackCursor(context.binding, context.target.assignmentId);
  return withMathRuntimeLease(
    { lockPath: `${cursor.file}.lock`, flockExecutable: '/usr/bin/flock', signal: input.signal },
    async (lease) => {
      const latest = context.readAssignments();
      for (const expected of [source, context.target]) {
        const current = latest.find((entry) => entry.assignmentId === expected.assignmentId);
        if (!current || canonicalMathJson(current) !== canonicalMathJson(expected))
          throw new Error('math_feedback_assignment_changed');
      }
      const previous = cursor.read();
      const existing = previous.uses.find(
        (entry) =>
          entry.ref === input.ref &&
          entry.sourceHash === input.sourceHash &&
          entry.sourceReceiptHash === observation.sourceReceiptHash &&
          entry.recipientReceiptHash === observation.recipientReceiptHash
      );
      // A later read must not erase an actual check or its diagnosis; identical retries do not append.
      if (
        (input.status === 'read' && existing) ||
        canonicalMathJson(existing ?? null) === canonicalMathJson(observation)
      )
        return 'unchanged';
      const uses = previous.uses.filter((entry) => entry.ref !== input.ref);
      uses.push(observation);
      lease.assertHeld();
      input.signal.throwIfAborted();
      try {
        writeMathJsonDurable(cursor.file, { ...previous, uses: uses.slice(-256) });
      } catch (error) {
        const code = (error as NodeJS.ErrnoException).code;
        // This is an advisory diagnostic after authenticated bytes/checks succeeded.
        // A full disk must not convert that success to a mathematical rejection.
        if (!code || !['ENOSPC', 'EDQUOT', 'EIO', 'EROFS'].includes(code)) throw error;
        console.warn(`[math_feedback] use receipt persistence unconfirmed: ${code}`);
        return 'persistence_unconfirmed';
      }
      return 'recorded';
    }
  );
}

/** Narrow, revocable access derived from the current proof's authenticated feedback relation. */
export async function readMathLiteFeedbackArtifact(
  capability: MathLiteFeedbackCapability,
  signal: AbortSignal,
  ref: string,
  access: MathArtifactAccess,
  observedRead = false
): Promise<MathArtifactAccess> {
  const context = readMathLiteProofLineage(capability, signal, undefined, true);
  if (access.role !== 'worker' || access.assignmentId !== context.target.assignmentId)
    throw new MathArtifactError('unauthorized');
  const parsed = parseMathArtifactReference(ref);
  if (parsed?.scheme !== 'math-artifact' || parsed.runId !== context.binding.runId)
    throw new MathArtifactError('unauthorized');
  const feedback = await readMathLiteFeedback({ resolvedCapability: capability, signal, artifactRefOnly: ref });
  if (!feedback.findings.some((finding) => finding.fullRefs.includes(ref))) throw new MathArtifactError('unauthorized');
  signal.throwIfAborted();
  if (observedRead)
    for (const finding of feedback.findings.filter((entry) => entry.fullRefs.includes(ref)))
      recordMathProofImpact(
        { runRoot: path.dirname(context.binding.artifactStoreRoot), runId: context.binding.runId },
        {
          kind: 'artifact_read',
          runId: context.binding.runId,
          assignmentId: finding.sourceAssignmentId,
          consumerAssignmentId: context.target.assignmentId,
          shareId: finding.shareId,
          artifactId: parsed.artifactId,
          observedAt: Date.now(),
        }
      );
  return { ...access, grants: new Set([...(access.grants ?? []), parsed.artifactId]) };
}

/** Advisory evidence identity at a blocked boundary, independent of notification consumption. */
export async function readMathLiteBlockedEvidenceRevision(input: {
  resolvedCapability: MathLiteFeedbackCapability;
  signal: AbortSignal;
  runInputs?: MathRunInputs;
}): Promise<string> {
  const context = readMathLiteProofLineage(input.resolvedCapability, input.signal, input.runInputs);
  let researchRevision = '';
  await readMathLiteFeedback({
    ...input,
    operationContext: context,
    onEvidenceRevision: (revision) => {
      researchRevision = revision;
    },
  });
  const grants = new Set(normalizeRuntimeMathAssignment(context.target.assignment).artifactGrants);
  const diagnostics: string[] = [];
  for (const reference of readMathLiteBlockerLineage(context.binding, context.target, context.receipts)) {
    if (reference.assignmentId !== context.target.assignmentId && !grants.has(reference.artifactId)) continue;
    // An owner boundary report states why the owner stopped; it is not a host
    // observation. Counting it here made a notes-only retry look like a new
    // evidence boundary and turned a nonterminal share into a terminal delivery.
    // Validate immutable content and its authorization; a filename/mtime is never evidence.
    // eslint-disable-next-line no-await-in-loop
    const verified = await readVerifiedMathBlockerReference(
      context.binding,
      context.target,
      reference.artifactId,
      input.signal
    );
    if ((verified?.provenance ?? reference.provenance) === 'owner_boundary') continue;
    // Oversized diagnostic contents remain a changed observation, never silently absent.
    diagnostics.push(verified?.observationDigest ?? reference.artifactId);
  }
  input.signal.throwIfAborted();
  const current = context.readAssignments().find((entry) => entry.assignmentId === context.target.assignmentId);
  if (!current || canonicalMathJson(current) !== canonicalMathJson(context.target))
    throw new Error('math_feedback_assignment_changed');
  return mathDigest(canonicalMathJson({ researchRevision, diagnostics: [...new Set(diagnostics)].toSorted() }));
}

/** Store the pre-seal observation only after the complete delivery has been sealed. */
export async function recordMathLiteBlockedEvidence(input: {
  resolvedCapability: MathLiteFeedbackCapability;
  signal: AbortSignal;
  revision: string;
  runInputs?: MathRunInputs;
}): Promise<void> {
  if (!/^[a-f0-9]{64}$/u.test(input.revision)) throw new Error('math_feedback_blocked_revision_invalid');
  const context = readMathLiteProofLineage(input.resolvedCapability, input.signal, input.runInputs);
  const cursor = mathLiteFeedbackCursor(context.binding, context.target.assignmentId);
  await withMathRuntimeLease(
    { lockPath: `${cursor.file}.lock`, flockExecutable: '/usr/bin/flock', signal: input.signal },
    async (lease) => {
      const current = context.readAssignments().find((entry) => entry.assignmentId === context.target.assignmentId);
      if (!current || canonicalMathJson(current) !== canonicalMathJson(context.target))
        throw new Error('math_feedback_assignment_changed');
      const previous = cursor.read();
      // Recovery may confirm the first snapshot but must never move its boundary forward.
      if (previous.blockedEvidenceRevision !== undefined) {
        if (previous.blockedEvidenceRevision !== input.revision)
          throw new Error('math_feedback_blocked_revision_conflict');
        return;
      }
      lease.assertHeld();
      input.signal.throwIfAborted();
      writeMathJsonDurable(cursor.file, { ...previous, blockedEvidenceRevision: input.revision });
    }
  );
}
