import type { MathRunBinding } from "../common/types/team/mathRuntimeContracts";
import type { listProjectGitResearchTeamAssignments } from "../project-git/index";
import {
  cachedMathBlockerReference,
  mathBlockerPlanningStore,
  readVerifiedMathBlockerReference,
  readMathLiteBlockerLineage,
} from "./mathLiteBlockerContext";
import {
  readMathLiteFeedback,
  resolveMathLiteOperationContext,
  type MathLiteOperationContext,
} from "./mathLiteFeedback";
import { normalizeRuntimeMathAssignment } from "./mathAssignmentJournal";
import type { MathRunInputs } from "./mathRunInputs";
import { canonicalMathJson, mathDigest } from "./mathRuntimeIo";
import { MathRunInputsIntegrityError } from "./mathRunInputs";
import { MathRunBindingError } from "./mathRunBinding";
import { MathArtifactError } from "./mathArtifactStore";
import { MathAssignmentAdapterError } from "./mathAssignmentExecutionAdapter";

// Only availability failures in advisory history may be downgraded. Identity,
// permissions, source contracts and cancellation retain their original failure.
export function isMathPlanningSafetyError(error: unknown): boolean {
  const code = error instanceof Error ? error.message : String(error);
  return (
    (error instanceof Error && error.name === 'AbortError') ||
    error instanceof MathRunInputsIntegrityError ||
    error instanceof MathRunBindingError ||
    error instanceof MathAssignmentAdapterError ||
    (error instanceof MathArtifactError && ['unauthorized', 'integrity'].includes(error.code)) ||
    /^math_(?:runtime_(?:integrity|lease_lost|aborted)|assignment_wal_(?:integrity|schema_unsupported)|lite_delivery_(?:integrity|identity|file_identity)|delivery_(?:identity_mismatch|invalid)|feedback_(?:predecessor_.*|assignment_changed|delivery_identity|operation_identity)|planning_assignment_changed|blocker_(?:context_integrity|predecessor_.*|formalizer_required)|share_(?:snapshot|note)_integrity)/u.test(
      code
    )
  );
}

type Receipt = ReturnType<typeof listProjectGitResearchTeamAssignments>[number];
type Capability = { teamId: string; slotId: string; roleKind: string; projectRoot: string };

export type MathPlanningContext = Readonly<{
  text: string;
  evidenceRefs: readonly string[];
  contextDigest: string;
  historyCoverage: 'partial' | 'unavailable';
}>;

const excerpt = (value: string | undefined, limit: number): string => {
  if (!value) return '';
  return Array.from(value).length > limit
    ? `${Array.from(value).slice(0, limit).join('')} [excerpt; read the artifact for the complete text]`
    : value;
};

function finishContext(
  lines: readonly string[],
  evidenceRefs: readonly string[],
  hasHistory: boolean,
  identity: string,
  maxBytes = 8000
): MathPlanningContext {
  const kept: string[] = [];
  let size = 0;
  let omitted = false;
  for (const line of lines) {
    const next = Buffer.byteLength(line, 'utf8') + 1;
    if (size + next > maxBytes - 100) {
      omitted = true;
      continue;
    }
    kept.push(line);
    size += next;
  }
  if (omitted) kept.push('More material was omitted from this bounded view; read the cited artifacts.');
  const text = kept.join('\n');
  const displayedRefs = evidenceRefs.filter((ref) => text.includes(ref));
  return {
    text,
    evidenceRefs: displayedRefs,
    contextDigest: mathDigest(canonicalMathJson({ identity, text, evidenceRefs: displayedRefs })),
    historyCoverage: hasHistory ? 'partial' : 'unavailable',
  };
}

export type MathPlanningHistoryHint = Readonly<{
  artifactId: string;
  text: string;
  explicitlyReferenced?: boolean;
  sameDeclaration?: boolean;
  timestamp?: string;
}>;

// Lexical overlap is recall only. This ranking never declares equivalence,
// refutation, applicability or permission to skip the current Lean check.
export function rankMathPlanningHistory<T extends MathPlanningHistoryHint>(items: readonly T[], query: string): T[] {
  const terms = new Set(query.match(/[\p{L}\p{N}_'.]+/gu) ?? []);
  const overlap = (text: string): number =>
    new Set((text.match(/[\p{L}\p{N}_'.]+/gu) ?? []).filter((word) => terms.has(word))).size;
  return items
    .map((item, index) => ({ item, index, overlap: overlap(item.text) }))
    .sort(
      (left, right) =>
        Number(Boolean(right.item.explicitlyReferenced)) - Number(Boolean(left.item.explicitlyReferenced)) ||
        Number(Boolean(right.item.sameDeclaration)) - Number(Boolean(left.item.sameDeclaration)) ||
        right.overlap - left.overlap ||
        (right.item.timestamp ?? '').localeCompare(left.item.timestamp ?? '') ||
        left.index - right.index
    )
    .map(({ item }) => item);
}

const supplementCursors = new Map<string, number>();

export async function readMathPlanningBlockerContext({
  binding,
  target,
  receipts,
  signal,
  currentArtifactId,
}: {
  binding: MathRunBinding;
  target: Receipt;
  receipts: readonly Receipt[];
  signal: AbortSignal;
  currentArtifactId?: string;
}): Promise<MathPlanningContext & { currentLines: string[]; historyLines: string[] }> {
  signal.throwIfAborted();
  const assignment = normalizeRuntimeMathAssignment(target.assignment);
  const grants = new Set(assignment.artifactGrants);
  const refs = readMathLiteBlockerLineage(binding, target, receipts).filter(
    (item) => item.assignmentId === target.assignmentId || grants.has(item.artifactId)
  );
  const store = mathBlockerPlanningStore(binding);
  let metadata: Awaited<ReturnType<typeof store.listMetadata>> = [];
  try {
    metadata = (await store.listMetadata({ role: 'worker', assignmentId: target.assignmentId, grants })).filter(
      (entry) => entry.kind === 'diagnostic' && /^blocker-[a-f0-9]{64}$/u.test(entry.artifactId)
    );
  } catch (error) {
    if (isMathPlanningSafetyError(error)) throw error;
  }
  // The manifest is scoped and authoritative. Recent pointers remain the fast
  // path; older objects are hydrated incrementally rather than reread each turn.
  const pool = new Map(refs.map((item) => [item.artifactId, item]));
  for (const entry of metadata) {
    const cached = cachedMathBlockerReference(binding, entry.artifactId);
    if (cached) pool.set(entry.artifactId, cached);
  }
  const older = metadata.filter((entry) => !pool.has(entry.artifactId) && entry.artifactId !== currentArtifactId);
  const cursorKey = `${binding.artifactStoreRoot}:${target.assignmentId}`;
  const start = (supplementCursors.get(cursorKey) ?? 0) % Math.max(1, older.length);
  const read = async (id: string) => {
    try {
      return await readVerifiedMathBlockerReference(binding, target, id, signal);
    } catch (error) {
      if (isMathPlanningSafetyError(error)) throw error;
      return undefined;
    }
  };
  for (let index = 0; index < Math.min(4, older.length); index++) {
    const item = await read(older[(start + index) % older.length]!.artifactId);
    if (item) pool.set(item.artifactId, item);
  }
  supplementCursors.set(cursorKey, start + Math.min(4, older.length));
  if (supplementCursors.size > 128) supplementCursors.delete(supplementCursors.keys().next().value!);
  const current = currentArtifactId ? await read(currentArtifactId) : undefined;
  if (current && current.assignmentId !== target.assignmentId) throw new Error('math_blocker_context_integrity');
  const query = [current?.goalsExcerpt, assignment.request.objective].filter(Boolean).join('\n');
  const ranked = rankMathPlanningHistory(
    [...pool.values()]
      .filter((item) => item.artifactId !== currentArtifactId)
      .map((item) => ({
        ...item,
        text: [item.goalsExcerpt, item.diagnosticsExcerpt, item.attemptsExcerpt].filter(Boolean).join('\n'),
        explicitlyReferenced: grants.has(item.artifactId),
        timestamp: metadata.find((entry) => entry.artifactId === item.artifactId)?.createdAt,
      })),
    query
  );
  const history: NonNullable<Awaited<ReturnType<typeof read>>>[] = [];
  for (const hint of ranked.slice(0, 6)) {
    const checked = await read(hint.artifactId);
    if (checked) history.push(checked);
  }
  const evidenceRefs = [
    ...new Set(
      [...(current ? [current.artifactId] : []), ...history.map((item) => item.artifactId)].map(
        (id) => `math-artifact://${binding.runId}/${id}`
      )
    ),
  ];
  const currentLines = [
    'Current Lean result, if present, remains the tool result. Earlier observations below are historical, not proof receipts.',
    `Current assignment objective: ${excerpt(assignment.request.objective, 768)}`,
    `Bound original targets: ${canonicalMathJson((assignment.request.verificationTargets ?? []).map(({ targetId, theoremName, pathRelative }) => ({ targetId, theoremName, pathRelative })))}`,
  ];
  if (current) currentLines.push(`Current diagnostic artifact: math-artifact://${binding.runId}/${current.artifactId}`);
  if (current?.goalsExcerpt) currentLines.push(`Current goal excerpt: ${excerpt(current.goalsExcerpt, 512)}`);
  const historyLines = history.map((item) =>
    [
      `${item.provenance === 'owner_boundary' ? 'Owner-reported boundary (unverified)' : 'Historical observation'} from assignment ${item.assignmentId}, source ${item.sourceHash}: math-artifact://${binding.runId}/${item.artifactId}`,
      item.goalsExcerpt ? `Goal excerpt: ${excerpt(item.goalsExcerpt, 512)}` : '',
      item.diagnosticsExcerpt
        ? `${item.provenance === 'owner_boundary' ? 'Owner summary' : 'Diagnostic excerpt'}: ${excerpt(item.diagnosticsExcerpt, 512)}`
        : '',
      item.attemptsExcerpt ? `Attempt excerpt: ${excerpt(item.attemptsExcerpt, 512)}` : '',
    ]
      .filter(Boolean)
      .join('\n')
  );
  signal.throwIfAborted();
  return {
    ...finishContext(
      [
        ...currentLines,
        ...historyLines,
        'History coverage is partial: bounded related records are shown; omitted or unavailable history is not evidence that no earlier counterexample exists.',
      ],
      evidenceRefs,
      Boolean(current || history.length),
      `${binding.runId}:${target.assignmentId}`,
      5000
    ),
    currentLines,
    historyLines,
  };
}

export async function readMathPlanningContext({
  resolvedCapability,
  signal,
  currentArtifactId,
  runInputs,
  operationContext,
  includeAssignmentReminder = true,
}: {
  resolvedCapability: Capability;
  signal: AbortSignal;
  currentArtifactId?: string;
  runInputs?: MathRunInputs;
  operationContext?: MathLiteOperationContext;
  includeAssignmentReminder?: boolean;
}): Promise<MathPlanningContext> {
  const context = resolveMathLiteOperationContext(resolvedCapability, signal, runInputs, operationContext);
  const { binding, receipts, target, lineage, readAssignments } = context;
  const blockers = await readMathPlanningBlockerContext({ binding, target, receipts, signal, currentArtifactId });
  const feedback = await readMathLiteFeedback({
    resolvedCapability,
    signal,
    consume: false,
    historyLimit: 6,
    historyQuery: [
      normalizeRuntimeMathAssignment(target.assignment).request.objective,
      binding.problem?.formalStatement,
      blockers.text.split('\n').find((line) => line.startsWith('Current goal excerpt:')),
    ]
      .filter(Boolean)
      .join('\n'),
    runInputs,
    operationContext: context,
  });
  signal.throwIfAborted();
  const latest = readAssignments();
  for (const expected of lineage) {
    const live = latest.find((entry) => entry.assignmentId === expected.assignmentId);
    if (!live || canonicalMathJson(live) !== canonicalMathJson(expected))
      throw new Error('math_planning_assignment_changed');
  }
  const lines = blockers.currentLines.filter(
    (line) =>
      includeAssignmentReminder ||
      (!line.startsWith('Current assignment objective:') && !line.startsWith('Bound original targets:'))
  );
  for (const question of (feedback.research_questions ?? []).slice(0, 8)) {
    lines.push(
      `Research dependency ${question.question_id} (evidence ${question.evidence_version}, producer ${question.producer_assignment_id}, ${question.pending ? 'active' : 'reported'}): ${excerpt(question.statement, 512)}. Connection: ${excerpt(question.targetConnection, 256)}. Mathematical validity remains unverified.`
    );
  }
  if (feedback.waiting_on_research_assignment_ids?.length)
    lines.push(
      `Explicit wait at the frozen proof snapshot: ${feedback.waiting_on_research_assignment_ids.join(', ')}. Unrelated proof work is not suspended.`
    );
  const findings = feedback.findings.slice(0, 6);
  for (const finding of findings) {
    const notes = finding.notes.slice(0, 1);
    const refs = [
      ...new Set([finding.fullRefs[0], ...notes.map((note) => note.ref)].filter((ref): ref is string => Boolean(ref))),
    ];
    const entry = [
      `Provisional research from assignment ${finding.sourceAssignmentId} ${finding.source === 'final_report' ? 'final report' : 'share'} ${finding.shareId}` +
        `${finding.deliveryId ? ` (delivery ${finding.deliveryId})` : ''}: ${excerpt(finding.summary, 512)}`,
      refs.length ? `Frozen full research: ${refs.join(' ')}` : '',
      finding.fullRefs.length > refs.length
        ? 'Additional frozen attachments are available via research_team read_feedback.'
        : '',
      ...notes.map(
        (note) =>
          `Frozen note ${note.path} excerpt: ${excerpt(note.text, 512)}${note.truncated ? ' [truncated; read the frozen artifact for complete assumptions]' : ''}`
      ),
    ]
      .filter(Boolean)
      .join('\n');
    lines.push(entry);
  }
  lines.push(...blockers.historyLines.slice(0, 6 - findings.length));
  lines.push(
    'History coverage is partial. Earlier linked reports remain available through research_team read_feedback; absence here is not mathematical refutation.'
  );
  return finishContext(
    lines,
    [...new Set([...blockers.evidenceRefs, ...findings.flatMap((finding) => finding.fullRefs)])],
    blockers.historyCoverage === 'partial' || findings.length > 0,
    `${binding.runId}:${target.assignmentId}`
  );
}
