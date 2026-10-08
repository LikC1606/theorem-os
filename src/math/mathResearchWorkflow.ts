import fs from 'node:fs';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { z } from 'zod';
import { readMathResearchPolicy } from "./mathResearchPolicy";
import { readMathRunHistoryIdentity, resolveMathRunHistory } from "./mathRunHistory";
import {
  canonicalMathJson,
  mathDigest,
  readMathJson,
  withMathRuntimeLease,
  writeMathJsonDurable,
  syncMathDirectory,
} from "./mathRuntimeIo";
import {
  advanceMathSearchState,
  createMathSearchState,
  computeMathRouteFingerprint,
  DEFAULT_MATH_ROUTE_PIVOT_THRESHOLD,
  mathEvidencePacketSchema,
  mathRouteSpecSchema,
  mathSearchStateSchema,
  type MathEvidencePacket,
} from "./mathSearchState";

const text = z.string().trim().min(1).max(4000);
const id = z.string().trim().min(1).max(160);
const hash = z.string().regex(/^[a-f0-9]{64}$/u);
const revision = z.number().int().nonnegative();
export const mathResearchArtifactBinding = z
  .object({
    kind: z.enum(['lean_declaration', 'verification_receipt']),
    path: text,
    sha256: hash,
    declarationName: text.optional(),
  })
  .strict()
  .superRefine((value, context) => {
    if (value.kind === 'lean_declaration' && !value.declarationName)
      context.addIssue({ code: 'custom', message: 'Lean binding requires declarationName' });
  });
const noteKind = z.enum(['dependency', 'failed_route', 'finding', 'next_step', 'conjecture', 'experiment', 'decision']);
const experimentSchema = z
  .object({
    question: text,
    expectedObservation: text,
    procedure: text.optional(),
    observation: text.optional(),
    outcome: z.enum(['supports', 'refutes', 'inconclusive']).optional(),
    candidateRef: text.optional(),
  })
  .strict();
export const mathResearchAssignmentBinding = z
  .object({
    teamId: id,
    slotId: id,
    workerId: id,
    statementHash: hash,
    assignmentDigest: hash,
    initialRouteFingerprint: id,
    routeRevisionsSupported: z.boolean(),
  })
  .strict();
export type MathResearchAssignmentBinding = z.infer<typeof mathResearchAssignmentBinding>;
const route = z.object({ fingerprint: id, revision, objective: text, spec: mathRouteSpecSchema.optional() }).strict();
const proposal = z
  .object({
    id,
    baseRouteRevision: revision,
    workerId: id,
    fingerprint: id,
    objective: text,
    evidenceRefs: z.array(text).min(1).max(16),
    routeSpec: mathRouteSpecSchema.optional(),
  })
  .strict();
const entry = z
  .object({
    id,
    kind: z.enum(['retrieval', 'exploration']),
    bottleneck: hash,
    routeRevision: revision,
    rounds: revision,
    status: z.enum(['active', 'returned']),
    productive: z.boolean().optional(),
  })
  .strict();
const stateSchema = z
  .object({
    schema: z.literal('deepscientist.mathematics.research-workflow.v1'),
    runIdentity: hash,
    problemId: id,
    assignmentId: id,
    workerId: id,
    policy: id,
    revision,
    binding: mathResearchAssignmentBinding,
    route,
    pending: proposal.optional(),
    entries: z.array(entry),
    notebook: z
      .array(
        z
          .object({
            key: id,
            author: id,
            routeRevision: revision,
            observedProofStateFingerprint: id.optional(),
            staleContext: z.boolean().optional(),
            kind: noteKind,
            summary: text,
            evidenceRefs: z.array(text).max(16),
            relatedKeys: z.array(id).optional(),
            targetConnection: text.optional(),
            assessment: z.enum(['unverified', 'supported', 'refuted', 'inconclusive']).optional(),
            statement: text.optional(),
            dependsOn: z.array(id).optional(),
            artifactBindings: z.array(mathResearchArtifactBinding).optional(),
            supersedes: id.optional(),
            experiment: experimentSchema.optional(),
          })
          .strict()
      )
      .default([]),
    decisions: z.array(
      z
        .object({ proposalId: id, decision: z.enum(['accept', 'reject']), routeRevision: revision, fingerprint: id })
        .strict()
    ),
    operations: z.array(z.object({ key: id, digest: hash }).strict()),
    notifications: z
      .array(
        z
          .object({
            key: id,
            target: z.enum(['lead', 'worker']),
            message: z.string().min(1).max(8000),
            delivered: z.boolean(),
            // A Worker note is durable context. Intermediate notes do not need
            // to start a Lead turn before the Worker has a valid delivery.
            wake: z.boolean().optional(),
          })
          .strict()
      )
      .default([]),
    /** Optional for journals created before the proof-search projection. */
    search: mathSearchStateSchema.optional(),
  })
  .strict();
export type MathResearchWorkflowState = z.infer<typeof stateSchema>;

const mathCommonRootCache = new Map<string, string>();

/** Git metadata is stable for a project path during a run; avoid one sync process per assignment. */
export function resolveMathResearchCommonRoot(projectRoot: string): string {
  let cacheKey = projectRoot;
  try {
    cacheKey = fs.realpathSync(projectRoot);
  } catch {
    /* Let git produce the authoritative error below when the path is invalid. */
  }
  const cached = mathCommonRootCache.get(cacheKey);
  if (cached) return cached;
  const commonRoot = execFileSync(
    'git',
    ['-C', projectRoot, 'rev-parse', '--path-format=absolute', '--git-common-dir'],
    { encoding: 'utf8', timeout: 10_000 }
  ).trim();
  if (mathCommonRootCache.size >= 64) mathCommonRootCache.delete(mathCommonRootCache.keys().next().value!);
  mathCommonRootCache.set(cacheKey, commonRoot);
  return commonRoot;
}

export function mathResearchOutboxIndexRoot(
  commonRoot: string,
  env: NodeJS.ProcessEnv = process.env
): string | undefined {
  if (!readMathRunHistoryIdentity(env)) return undefined;
  return resolveMathRunHistory(commonRoot, 'research-outbox-index', env).root;
}

/** The index is a recoverable scheduling hint; delivery still checks the assignment and workflow. */
export function syncMathResearchOutboxIndex(
  commonRoot: string,
  state: MathResearchWorkflowState,
  env: NodeJS.ProcessEnv = process.env
): void {
  const root = mathResearchOutboxIndexRoot(commonRoot, env);
  if (!root) return;
  const file = path.join(
    root,
    `pending-${mathDigest(canonicalMathJson([state.binding.teamId, state.assignmentId]))}.json`
  );
  const roles = [
    ...new Set(
      state.notifications.filter((item) => !item.delivered).map((item) => (item.target === 'lead' ? 'worker' : 'lead'))
    ),
  ];
  if (roles.length)
    writeMathJsonDurable(file, {
      teamId: state.binding.teamId,
      assignmentId: state.assignmentId,
      slotId: state.binding.slotId,
      roles,
    });
  else {
    try {
      fs.unlinkSync(file);
      syncMathDirectory(root);
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code !== 'ENOENT') throw error;
    }
  }
}

const journalArrayFields = ['entries', 'notebook', 'decisions', 'operations', 'notifications'] as const;
const checkpointSchema = z.object({ sequence: revision, headHash: hash }).strict();
const journalDeltaSchema = z
  .object({
    scalars: z
      .object({
        revision: revision.optional(),
        route: route.optional(),
        pending: proposal.nullable().optional(),
        search: mathSearchStateSchema.nullable().optional(),
      })
      .strict(),
    arrays: z.array(
      z
        .object({
          field: z.enum(journalArrayFields),
          previousLength: revision,
          append: z.array(z.unknown()),
          replace: z.array(z.object({ index: revision, value: z.unknown() }).strict()),
        })
        .strict()
    ),
  })
  .strict();
const journalRecordSchema = z
  .object({
    schema: z.literal('deepscientist.mathematics.research-journal.v1'),
    sequence: revision,
    previousHash: hash,
    delta: journalDeltaSchema,
    digest: hash,
  })
  .strict();
const snapshotSchema = z
  .object({
    schema: z.literal('deepscientist.mathematics.research-snapshot.v1'),
    checkpoint: checkpointSchema,
    state: stateSchema,
    stateDigest: hash,
  })
  .strict();
type PersistedResearch = { state: MathResearchWorkflowState; sequence: number; headHash: string };
type CachedResearch = { persisted: PersistedResearch; snapshotStamp: string; records: Map<string, string> };
const researchReadCache = new Map<string, CachedResearch>();
/**
 * Idempotency history is intentionally durable and unbounded. Keep its lookup
 * separate from the journal representation so long-running research does not
 * rescan every prior operation for each command.
 */
type ResearchOperationIndex = {
  parent?: ResearchOperationIndex;
  entries: Map<string, string>;
};
const researchOperationIndexes = new WeakMap<MathResearchWorkflowState, ResearchOperationIndex>();

function researchOperationIndex(state: MathResearchWorkflowState): ResearchOperationIndex {
  const cached = researchOperationIndexes.get(state);
  if (cached) return cached;
  const index = {
    entries: new Map(state.operations.map((operation) => [operation.key, operation.digest])),
  };
  researchOperationIndexes.set(state, index);
  return index;
}

function findResearchOperation(state: MathResearchWorkflowState, key: string): string | undefined {
  let index: ResearchOperationIndex | undefined = researchOperationIndex(state);
  while (index) {
    const digest = index.entries.get(key);
    if (digest !== undefined) return digest;
    index = index.parent;
  }
  return undefined;
}

function appendResearchOperation(
  state: MathResearchWorkflowState,
  operation: MathResearchWorkflowState['operations'][number]
): void {
  mutableResearchArray(state, 'operations').push(operation);
  const index = researchOperationIndexes.get(state);
  if (index) index.entries.set(operation.key, operation.digest);
  else researchOperationIndexes.set(state, { entries: new Map([[operation.key, operation.digest]]) });
}

const fileStamp = (file: string): string => {
  try {
    const stat = fs.lstatSync(file, { bigint: true });
    if (!stat.isFile() || fs.realpathSync(file) !== file) throw new Error('math_research_journal_integrity');
    return [stat.dev, stat.ino, stat.size, stat.mtimeNs, stat.ctimeNs].join(':');
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code === 'ENOENT') return 'missing';
    throw error;
  }
};
function freezeResearchValue<T>(value: T): T {
  if (value && typeof value === 'object' && !Object.isFrozen(value)) {
    for (const child of Object.values(value)) freezeResearchValue(child);
    Object.freeze(value);
  }
  return value;
}
function copyResearchStateForUpdate(state: MathResearchWorkflowState): MathResearchWorkflowState {
  const copy = { ...state };
  researchArrayChanges.set(copy, new Map());
  researchOperationIndexes.set(copy, { parent: researchOperationIndex(state), entries: new Map() });
  return copy;
}
type ResearchArrayField = (typeof journalArrayFields)[number];
const researchArrayChanges = new WeakMap<MathResearchWorkflowState, Map<ResearchArrayField, Set<number>>>();
function mutableResearchArray<F extends ResearchArrayField>(
  state: MathResearchWorkflowState,
  field: F
): MathResearchWorkflowState[F] {
  const changes = researchArrayChanges.get(state);
  if (changes && !changes.has(field)) {
    Object.assign(state, { [field]: state[field].slice() });
    changes.set(field, new Set());
  }
  return state[field];
}
function replaceResearchArrayItem<F extends ResearchArrayField>(
  state: MathResearchWorkflowState,
  field: F,
  index: number,
  value: MathResearchWorkflowState[F][number]
): void {
  const items = mutableResearchArray(state, field) as unknown[];
  items[index] = value;
  researchArrayChanges.get(state)?.get(field)?.add(index);
}
const journalFile = (directory: string, sequence: number) =>
  path.join(directory, `${String(sequence).padStart(16, '0')}.json`);

/** Remove journal deltas covered by a durable snapshot after the snapshot is
 * written.  This bounds restart work without weakening the hash-chain check
 * for the retained suffix. */
function compactResearchJournal(directory: string, sequence: number): void {
  for (const journalEntry of fs.readdirSync(directory)) {
    const match = /^(\d{16})\.json$/u.exec(journalEntry);
    if (!match || Number(match[1]) > sequence) continue;
    try {
      fs.rmSync(path.join(directory, journalEntry), { force: true });
    } catch {
      // Compaction is an optimization. A later read can still replay the
      // retained records if another process keeps an old file open.
    }
  }
}

function readOptionalMathJson(file: string): unknown | undefined {
  try {
    return readMathJson(file);
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code === 'ENOENT') return undefined;
    throw error;
  }
}

function assertJournalDirectory(directory: string): void {
  if (fs.realpathSync(directory) !== directory || !fs.lstatSync(directory).isDirectory())
    throw new Error('math_research_journal_integrity');
}

function readPersistedResearch(file: string): PersistedResearch | undefined {
  const directory = `${file}.journal`;
  const snapshotPath = fileStamp(file) === 'missing' ? path.join(directory, 'genesis.json') : file;
  const snapshotStamp = `${snapshotPath}:${fileStamp(snapshotPath)}`;
  const cached = researchReadCache.get(file);
  const reusable =
    cached?.snapshotStamp === snapshotStamp &&
    [...cached.records].every(([record, stamp]) => fileStamp(record) === stamp)
      ? cached
      : undefined;
  const raw = reusable ? undefined : readOptionalMathJson(snapshotPath);
  if (reusable) assertJournalDirectory(directory);
  if (!reusable && raw === undefined) return undefined;
  const snapshot = reusable ? undefined : snapshotSchema.safeParse(raw);
  let state = reusable ? reusable.persisted.state : snapshot?.success ? snapshot.data.state : stateSchema.parse(raw);
  if (snapshot?.success && mathDigest(canonicalMathJson(state)) !== snapshot.data.stateDigest)
    throw new Error('math_research_snapshot_integrity');
  let sequence = reusable?.persisted.sequence ?? (snapshot?.success ? snapshot.data.checkpoint.sequence : 0);
  let headHash =
    reusable?.persisted.headHash ??
    (snapshot?.success ? snapshot.data.checkpoint.headHash : mathDigest(canonicalMathJson(state)));
  const records = new Map(reusable?.records);
  const remember = (): PersistedResearch => {
    if (`${snapshotPath}:${fileStamp(snapshotPath)}` !== snapshotStamp)
      throw new Error('math_research_snapshot_changed');
    const persisted = { state: freezeResearchValue(state), sequence, headHash };
    if (researchReadCache.size >= 64) researchReadCache.delete(researchReadCache.keys().next().value!);
    researchReadCache.set(file, { persisted, snapshotStamp, records });
    return persisted;
  };
  if (!fs.existsSync(directory)) {
    if (sequence) throw new Error('math_research_journal_missing');
    return { state: freezeResearchValue(state), sequence, headHash };
  }
  assertJournalDirectory(directory);
  const headValue = readOptionalMathJson(path.join(directory, 'head.json'));
  const head = headValue === undefined ? undefined : checkpointSchema.parse(headValue);
  if (!head && sequence === 0 && !fs.readdirSync(directory).some((name) => /^\d{16}\.json$/u.test(name)))
    return remember();
  let copied = false;
  while (true) {
    const recordPath = journalFile(directory, sequence + 1);
    const beforeRecord = fileStamp(recordPath);
    const value = readOptionalMathJson(recordPath);
    if (value === undefined) break;
    const record = journalRecordSchema.parse(value);
    const { digest, ...payload } = record;
    if (
      record.sequence !== sequence + 1 ||
      record.previousHash !== headHash ||
      mathDigest(canonicalMathJson(payload)) !== digest
    )
      throw new Error('math_research_journal_integrity');
    if (!copied) {
      state = copyResearchStateForUpdate(state);
      copied = true;
    }
    for (const patch of record.delta.arrays) {
      const items = mutableResearchArray(state, patch.field) as unknown[];
      if (items.length !== patch.previousLength) throw new Error('math_research_journal_integrity');
      for (const replacement of patch.replace) {
        if (replacement.index >= patch.previousLength || !['entries', 'notifications'].includes(patch.field))
          throw new Error('math_research_journal_integrity');
        items[replacement.index] = stateSchema.shape[patch.field].parse([replacement.value])[0];
      }
      const appended = stateSchema.shape[patch.field].parse(patch.append);
      items.push(...appended);
      if (patch.field === 'operations') {
        const index = researchOperationIndexes.get(state) ?? { entries: new Map<string, string>() };
        researchOperationIndexes.set(state, index);
        for (const operation of stateSchema.shape.operations.parse(patch.append))
          index.entries.set(operation.key, operation.digest);
      }
    }
    const { pending, search, ...scalars } = record.delta.scalars;
    Object.assign(state, scalars);
    if (pending === null) delete state.pending;
    else if (pending !== undefined) state.pending = pending;
    if (search === null) delete state.search;
    else if (search !== undefined) state.search = search;
    sequence = record.sequence;
    headHash = digest;
    const afterRecord = fileStamp(recordPath);
    if (beforeRecord !== afterRecord) throw new Error('math_research_journal_integrity');
    records.set(recordPath, afterRecord);
    if (head?.sequence === sequence && head.headHash !== headHash) throw new Error('math_research_journal_integrity');
  }
  if (!head || head.sequence > sequence || (head.sequence === sequence && head.headHash !== headHash))
    throw new Error('math_research_journal_integrity');
  return remember();
}

function persistResearch(
  file: string,
  previous: PersistedResearch | undefined,
  value: MathResearchWorkflowState
): void {
  // Inputs were parsed at the command boundary and existing state was validated on read.
  // Preserve unchanged object identities so append-only histories need no reserialization.
  const state = value;
  if (!previous) {
    const directory = `${file}.journal`;
    fs.mkdirSync(directory, { recursive: true, mode: 0o700 });
    assertJournalDirectory(directory);
    syncMathDirectory(path.dirname(directory));
    const initial = stateSchema.parse(state);
    const stateDigest = mathDigest(canonicalMathJson(initial));
    writeMathJsonDurable(path.join(directory, 'genesis.json'), {
      schema: 'deepscientist.mathematics.research-snapshot.v1',
      checkpoint: { sequence: 0, headHash: stateDigest },
      state: initial,
      stateDigest,
    });
    // Keep initial and legacy state files readable; the first compaction writes an internal envelope.
    writeMathJsonDurable(file, state);
    return;
  }
  const directory = `${file}.journal`;
  if (!fs.existsSync(directory)) {
    fs.mkdirSync(directory, { mode: 0o700 });
    syncMathDirectory(path.dirname(directory));
  }
  assertJournalDirectory(directory);
  if (!fs.existsSync(path.join(directory, 'head.json')))
    writeMathJsonDurable(path.join(directory, 'head.json'), {
      sequence: previous.sequence,
      headHash: previous.headHash,
    });
  const scalars: z.infer<typeof journalDeltaSchema>['scalars'] = {};
  if (state.revision !== previous.state.revision) scalars.revision = state.revision;
  if (canonicalMathJson(state.route) !== canonicalMathJson(previous.state.route)) scalars.route = state.route;
  if (canonicalMathJson(state.pending ?? null) !== canonicalMathJson(previous.state.pending ?? null))
    scalars.pending = state.pending ?? null;
  if (canonicalMathJson(state.search ?? null) !== canonicalMathJson(previous.state.search ?? null))
    scalars.search = state.search ?? null;
  const arrays: z.infer<typeof journalDeltaSchema>['arrays'] = [];
  for (const field of journalArrayFields) {
    const before = previous.state[field];
    const after = state[field];
    if (after.length < before.length) throw new Error('math_research_journal_integrity');
    const changed = researchArrayChanges.get(state)?.get(field);
    const replace = changed
      ? [...changed].filter((index) => index < before.length).map((index) => ({ index, value: after[index] }))
      : [];
    if (replace.length && field !== 'entries' && field !== 'notifications')
      throw new Error('math_research_journal_integrity');
    const append = after.slice(before.length);
    if (replace.length || append.length) arrays.push({ field, previousLength: before.length, append, replace });
  }
  const payload = {
    schema: 'deepscientist.mathematics.research-journal.v1' as const,
    sequence: previous.sequence + 1,
    previousHash: previous.headHash,
    delta: { scalars, arrays },
  };
  const digest = mathDigest(canonicalMathJson(payload));
  const recordPath = journalFile(directory, payload.sequence);
  if (fs.existsSync(recordPath)) throw new Error('math_research_journal_sequence_conflict');
  writeMathJsonDurable(recordPath, { ...payload, digest });
  const checkpoint = { sequence: payload.sequence, headHash: digest };
  writeMathJsonDurable(path.join(directory, 'head.json'), checkpoint);
  // This is a storage checkpoint frequency, never a limit on research activity.
  if (checkpoint.sequence % 128 === 0)
    (() => {
      const snapshot = {
        schema: 'deepscientist.mathematics.research-snapshot.v1',
        checkpoint,
        state,
        stateDigest: mathDigest(canonicalMathJson(state)),
      } as const;
      writeMathJsonDurable(file, snapshot);
      // Keep the recovery base aligned with the first retained journal record.
      // This lets a run recover when the published snapshot is lost after
      // compaction without requiring the deleted prefix.
      writeMathJsonDurable(path.join(directory, 'genesis.json'), snapshot);
      compactResearchJournal(directory, checkpoint.sequence);
    })();
}
export type MathResearchProjectionView = 'working' | 'full';

const MATH_RESEARCH_WORKING_VIEW_MAX_BYTES = 12 * 1024;
const MATH_RESEARCH_WORKING_VIEW_WINDOW = 8;
const mathResearchProjectionCache = new WeakMap<MathResearchWorkflowState, Map<string, unknown>>();

const boundedResearchText = (value: string | undefined, byteLimit: number): { value?: string; truncated: boolean } => {
  if (value === undefined || Buffer.byteLength(value, 'utf8') <= byteLimit) return { value, truncated: false };
  let bytes = 0;
  let result = '';
  for (const character of value) {
    const width = Buffer.byteLength(character, 'utf8');
    if (bytes + width > byteLimit) break;
    result += character;
    bytes += width;
  }
  return { value: `${result}\n[truncated; read the full view]`, truncated: true };
};

const mathResearchFullReadRef = (state: MathResearchWorkflowState) => ({
  tool: 'math_research' as const,
  problemId: state.problemId,
  assignmentId: state.assignmentId,
  command: { action: 'get' as const, view: 'full' as const, offset: 0, limit: 200 },
});

function buildMathResearchWorkingView(state: MathResearchWorkflowState) {
  let textTruncated = false;
  const compactReference = (value: string): string => {
    const compacted = boundedResearchText(value, 256);
    textTruncated ||= compacted.truncated;
    return compacted.value ?? '';
  };
  const superseded = new Set(state.notebook.flatMap((note) => (note.supersedes ? [note.supersedes] : [])));
  const currentNotes = state.notebook.filter(
    (note) => note.routeRevision === state.route.revision && !superseded.has(note.key)
  );
  const recentNotes = currentNotes.slice(-MATH_RESEARCH_WORKING_VIEW_WINDOW);
  const dependencyKeys = new Set(recentNotes.flatMap((note) => note.dependsOn ?? []));
  const directDependencies = currentNotes
    .filter((note) => dependencyKeys.has(note.key))
    .slice(-MATH_RESEARCH_WORKING_VIEW_WINDOW);
  const selectedKeys = new Set(directDependencies.map((note) => note.key));
  const remainingWindow = MATH_RESEARCH_WORKING_VIEW_WINDOW - directDependencies.length;
  const selected = [
    ...directDependencies,
    ...(remainingWindow > 0 ? recentNotes.filter((note) => !selectedKeys.has(note.key)).slice(-remainingWindow) : []),
  ].toSorted((left, right) => currentNotes.indexOf(left) - currentNotes.indexOf(right));

  const compactNote = (note: MathResearchWorkflowState['notebook'][number]) => {
    const summary = boundedResearchText(note.summary, 1_500);
    const statement = boundedResearchText(note.statement, 2_000);
    const targetConnection = boundedResearchText(note.targetConnection, 1_000);
    textTruncated ||=
      summary.truncated ||
      statement.truncated ||
      targetConnection.truncated ||
      note.evidenceRefs.length > 4 ||
      (note.dependsOn?.length ?? 0) > 8 ||
      (note.artifactBindings?.length ?? 0) > 2;
    return {
      key: note.key,
      kind: note.kind,
      routeRevision: note.routeRevision,
      summary: summary.value,
      evidenceRefs: note.evidenceRefs.slice(0, 4).map(compactReference),
      ...(note.assessment ? { assessment: note.assessment } : {}),
      ...(statement.value ? { statement: statement.value } : {}),
      ...(targetConnection.value ? { targetConnection: targetConnection.value } : {}),
      ...(note.dependsOn?.length ? { dependsOn: note.dependsOn.slice(0, 8) } : {}),
      ...(note.supersedes ? { supersedes: note.supersedes } : {}),
      ...(note.artifactBindings?.length
        ? {
            artifactBindings: note.artifactBindings.slice(0, 2).map((binding) =>
              binding.declarationName
                ? {
                    kind: binding.kind,
                    path: compactReference(binding.path),
                    sha256: binding.sha256,
                    declarationName: compactReference(binding.declarationName),
                  }
                : { kind: binding.kind, path: compactReference(binding.path), sha256: binding.sha256 }
            ),
          }
        : {}),
    };
  };
  const relevantWork = selected.map(compactNote);
  const lastDecisiveNote = currentNotes
    .toReversed()
    .find((note) => note.kind === 'failed_route' || note.assessment === 'refuted');
  const compilerDiagnostic = boundedResearchText(
    state.search?.evidencePacket.compiler.diagnostic ?? state.search?.evidencePacket.recentDelta.errorAfter,
    2_000
  );
  textTruncated ||= compilerDiagnostic.truncated;
  const hostVerified = Boolean(
    state.search?.evidencePacket.closedProof &&
    state.search.evidencePacket.independentEvaluator === 'passed' &&
    state.search.evidencePacket.verifierReceipt !== null &&
    state.search.diagnosis.proof_receipt === 'closed_and_verified'
  );
  const unverified = selected.map((note) => ({
    key: note.key,
    assessment: note.assessment ?? 'unverified',
    evidenceRefs: note.evidenceRefs.slice(0, 4).map(compactReference),
    reason:
      note.artifactBindings?.length || note.assessment === 'supported'
        ? 'The note or artifact binding has no host-validated receipt in this projection.'
        : 'Research notes do not confer proof authority.',
  }));
  const activeEntries = state.entries.filter(
    (item) => item.status === 'active' && item.routeRevision === state.route.revision
  );
  const routeObjective = boundedResearchText(state.route.objective, 1_000);
  const pendingObjective = boundedResearchText(state.pending?.objective, 1_000);
  const nextStep = boundedResearchText(
    currentNotes.toReversed().find((note) => note.kind === 'next_step')?.summary ??
      (state.pending
        ? 'Resolve the pending route proposal before changing the active route.'
        : state.search?.decision === 'complete'
          ? 'Send the frozen source to independent final verification.'
          : 'Continue the active assignment from the current proof state.'),
    1_000
  );
  textTruncated ||= routeObjective.truncated || pendingObjective.truncated || nextStep.truncated;
  const omittedNotes = Math.max(0, currentNotes.length - relevantWork.length);
  const readRef = mathResearchFullReadRef(state);
  let projection = {
    schema: 'deepscientist.mathematics.research-working-view.v1' as const,
    view: 'working' as const,
    identity: {
      runIdentity: state.runIdentity,
      problemId: state.problemId,
      assignmentId: state.assignmentId,
      workerId: state.workerId,
      statementHash: state.binding.statementHash,
      assignmentDigest: state.binding.assignmentDigest,
      route: {
        fingerprint: state.route.fingerprint,
        revision: state.route.revision,
        objective: routeObjective.value ?? '',
      },
      source: { status: 'not_recorded_by_research_workflow' as const },
      environment: { status: 'not_recorded_by_research_workflow' as const },
    },
    operation: {
      revision: state.revision,
      policy: state.policy,
      searchDecision: state.search?.decision ?? 'continue',
      suggestedNextStep: state.search?.nextStep ?? 'continue_local',
      compilerStatus: state.search?.evidencePacket.compiler.status ?? 'unavailable',
      pendingNotifications: state.notifications.filter((item) => !item.delivered).length,
    },
    selectedObligation: {
      proofStateFingerprint: state.search?.proofStateFingerprint ?? 'unknown',
      unresolvedGoals: state.search?.unresolvedGoals ?? [],
    },
    relevantWork,
    evidence: {
      verified: hostVerified
        ? [
            {
              kind: 'original_goal' as const,
              proofStateFingerprint: state.search!.proofStateFingerprint,
              evidenceRefs: state.search!.evidencePacket.evidenceRefs.slice(0, 8).map(compactReference),
            },
          ]
        : [],
      sourceCurrent: [] as unknown[],
      unverified,
    },
    decisiveEvidence: compilerDiagnostic.value
      ? { kind: 'compiler' as const, diagnostic: compilerDiagnostic.value }
      : lastDecisiveNote
        ? {
            kind: 'research_note' as const,
            key: lastDecisiveNote.key,
            evidenceRefs: lastDecisiveNote.evidenceRefs.slice(0, 4).map(compactReference),
          }
        : null,
    pendingResearch: {
      routeProposal: state.pending
        ? {
            id: state.pending.id,
            baseRouteRevision: state.pending.baseRouteRevision,
            workerId: state.pending.workerId,
            fingerprint: state.pending.fingerprint,
            objective: pendingObjective.value ?? '',
            evidenceRefs: state.pending.evidenceRefs.slice(0, 4).map(compactReference),
          }
        : null,
      entries: activeEntries,
    },
    nextStep: nextStep.value ?? '',
    truncated: omittedNotes > 0 || textTruncated,
    omitted: { notebook: omittedNotes },
    readRef,
    authority: 'organization' as const,
    solverReady: false as const,
  };

  while (
    Buffer.byteLength(canonicalMathJson(projection), 'utf8') > MATH_RESEARCH_WORKING_VIEW_MAX_BYTES &&
    projection.relevantWork.length > 0
  ) {
    projection.relevantWork.shift();
    projection.evidence.unverified.shift();
    projection.truncated = true;
    projection.omitted.notebook += 1;
  }
  if (Buffer.byteLength(canonicalMathJson(projection), 'utf8') > MATH_RESEARCH_WORKING_VIEW_MAX_BYTES) {
    const goals = projection.selectedObligation.unresolvedGoals;
    projection = {
      ...projection,
      selectedObligation: {
        ...projection.selectedObligation,
        unresolvedGoals: goals.slice(0, 1).map((goal) => boundedResearchText(goal, 2_000).value ?? ''),
      },
      decisiveEvidence: null,
      truncated: true,
    };
  }
  if (Buffer.byteLength(canonicalMathJson(projection), 'utf8') > MATH_RESEARCH_WORKING_VIEW_MAX_BYTES) {
    projection = {
      ...projection,
      selectedObligation: {
        proofStateFingerprint: projection.selectedObligation.proofStateFingerprint,
        unresolvedGoals: [],
      },
      relevantWork: [],
      evidence: { ...projection.evidence, unverified: [] },
      decisiveEvidence: null,
      pendingResearch: { routeProposal: null, entries: [] },
      nextStep: 'Read the full view from readRef; required working context exceeded the byte limit.',
      truncated: true,
      omitted: { notebook: currentNotes.length },
    };
  }
  return Object.freeze(projection);
}

/** Tool projection excludes internal retry history; paging never deletes durable notes. */
export function projectMathResearchState(
  state: MathResearchWorkflowState | undefined,
  offset?: number,
  limit = 40,
  view: MathResearchProjectionView = 'full'
) {
  if (!state) return undefined;
  if (view === 'working') {
    const cacheKey = `${view}:${state.revision}`;
    const cached = mathResearchProjectionCache.get(state)?.get(cacheKey);
    if (cached) return cached as ReturnType<typeof buildMathResearchWorkingView>;
    const projected = buildMathResearchWorkingView(state);
    const stateCache = mathResearchProjectionCache.get(state) ?? new Map<string, unknown>();
    stateCache.set(cacheKey, projected);
    mathResearchProjectionCache.set(state, stateCache);
    return projected;
  }
  const start = offset ?? Math.max(0, state.notebook.length - limit);
  const { operations: _operations, notifications, notebook, entries, decisions, ...current } = state;
  return {
    ...current,
    notebook: notebook.slice(start, start + limit),
    notebookPage: {
      offset: start,
      total: notebook.length,
      nextOffset: start + limit < notebook.length ? start + limit : null,
    },
    activeEntries: entries.filter((item) => item.status === 'active'),
    recentDecisions: decisions.slice(-20),
    pendingNotifications: notifications.filter((item) => !item.delivered).length,
    search: state.search,
    authority: 'organization',
    solverReady: false,
  };
}
export function readMathResearchWorkflowState(
  projectRoot: string,
  problemId: string,
  assignmentId: string,
  env: NodeJS.ProcessEnv = process.env
): MathResearchWorkflowState | undefined {
  const policy = readMathResearchPolicy(env);
  if (!readMathRunHistoryIdentity(env)) return undefined;
  const commonRoot = resolveMathResearchCommonRoot(projectRoot);
  const scope = resolveMathRunHistory(commonRoot, id.parse(problemId), env);
  const file = path.join(scope.root, `research-${mathDigest(id.parse(assignmentId))}.json`);
  const state = readPersistedResearch(file)?.state;
  if (!state) return undefined;
  if (
    state.runIdentity !== scope.runIdentity ||
    state.problemId !== problemId ||
    state.assignmentId !== assignmentId ||
    state.policy !== (policy?.id ?? 'full_system')
  )
    throw new Error('Research workflow provenance mismatch.');
  return state;
}
export const mathResearchWorkflowCommand = z.discriminatedUnion('action', [
  z.object({ action: z.literal('initialize'), key: id, workerId: id, fingerprint: id, objective: text }).strict(),
  z
    .object({
      action: z.literal('get'),
      offset: revision.optional(),
      limit: z.number().int().positive().max(200).optional(),
      view: z.enum(['working', 'full']).optional(),
    })
    .strict(),
  z
    .object({
      action: z.literal('record'),
      key: id,
      expectedRevision: revision,
      observedRouteRevision: revision.optional(),
      observedProofStateFingerprint: id.optional(),
      kind: noteKind,
      summary: text,
      evidenceRefs: z.array(text).max(16),
      relatedKeys: z.array(id).optional(),
      targetConnection: text.optional(),
      assessment: z.enum(['unverified', 'supported', 'refuted', 'inconclusive']).optional(),
      statement: text.optional(),
      dependsOn: z.array(id).optional(),
      artifactBindings: z.array(mathResearchArtifactBinding).optional(),
      supersedes: id.optional(),
      experiment: experimentSchema.optional(),
    })
    .strict(),
  z
    .object({
      action: z.literal('propose_route'),
      key: id,
      expectedRevision: revision,
      fingerprint: id,
      objective: text,
      evidenceRefs: z.array(text).min(1).max(16),
      routeSpec: mathRouteSpecSchema.optional(),
    })
    .strict(),
  z
    .object({
      action: z.literal('decide_route'),
      key: id,
      expectedRevision: revision,
      proposalId: id,
      decision: z.enum(['accept', 'reject']),
    })
    .strict(),
  z
    .object({
      action: z.literal('enter'),
      key: id,
      expectedRevision: revision,
      kind: z.enum(['retrieval', 'exploration']),
      bottleneck: hash,
    })
    .strict(),
  z.object({ action: z.literal('advance'), key: id, expectedRevision: revision, entryId: id }).strict(),
  z
    .object({ action: z.literal('return'), key: id, expectedRevision: revision, entryId: id, productive: z.boolean() })
    .strict(),
  z
    .object({
      action: z.literal('record_search'),
      key: id,
      expectedRevision: revision,
      packet: mathEvidencePacketSchema,
      routeSpec: mathRouteSpecSchema.optional(),
      routeNovelty: z.enum(['new', 'equivalent', 'repeated', 'unknown']).optional(),
      pivotThreshold: z.number().int().min(2).max(32).optional(),
    })
    .strict(),
]);
export type MathResearchWorkflowCommand = z.infer<typeof mathResearchWorkflowCommand>;

/** Production MCP adapter: only get may select a projection; mutations retain the legacy full response. */
export function projectMathResearchCommandState(
  state: MathResearchWorkflowState | undefined,
  command: MathResearchWorkflowCommand
) {
  return projectMathResearchState(
    state,
    command.action === 'get' ? command.offset : undefined,
    command.action === 'get' ? command.limit : undefined,
    command.action === 'get' ? command.view : undefined
  );
}

/**
 * Persist a proof-loop packet produced by the runtime itself. This boundary is
 * intentionally separate from the MCP command: model-authored `record_search`
 * calls cannot write completion, evaluator, or verifier fields, while the
 * runtime may persist the exact values returned by its Lean/evaluator hosts.
 */
export async function recordMathSearchEvidence(input: {
  projectRoot: string;
  problemId: string;
  assignmentId: string;
  packet: MathEvidencePacket;
  binding?: MathResearchAssignmentBinding;
  route?: { fingerprint: string; objective: string };
  env?: NodeJS.ProcessEnv;
}) {
  const env = input.env ?? process.env;
  let state = readMathResearchWorkflowState(input.projectRoot, input.problemId, input.assignmentId, env);
  if (!state && input.binding && input.route) {
    const binding = mathResearchAssignmentBinding.parse(input.binding);
    if (
      binding.statementHash !== input.packet.statementHash ||
      binding.initialRouteFingerprint !== input.route.fingerprint ||
      input.packet.routeFingerprint !== input.route.fingerprint
    )
      throw new Error('math_search_initial_binding_mismatch');
    const initialize = {
      action: 'initialize' as const,
      key: `host-search-init-${mathDigest(canonicalMathJson([input.assignmentId, binding.assignmentDigest]))}`,
      workerId: binding.workerId,
      fingerprint: input.route.fingerprint,
      objective: input.route.objective,
    };
    try {
      const initialized = await updateMathResearchWorkflow({
        projectRoot: input.projectRoot,
        problemId: input.problemId,
        assignmentId: input.assignmentId,
        actor: { roleId: binding.workerId, roleKind: 'worker' },
        command: initialize,
        binding,
        env,
        hostOwned: true,
      });
      state = initialized.state;
    } catch (error) {
      // A concurrent proof delivery may have initialized the same journal
      // after the initial read. Re-read only that expected race; preserve all
      // other integrity and provenance failures.
      if (!(error instanceof Error) || error.message !== 'Research workflow already exists.') throw error;
      state = readMathResearchWorkflowState(input.projectRoot, input.problemId, input.assignmentId, env);
    }
  }
  if (!state?.search) return { persisted: false as const, state };
  if (input.packet.routeFingerprint !== state.route.fingerprint)
    throw new Error('math_search_route_fingerprint_mismatch');
  const packet = mathEvidencePacketSchema.parse({
    ...input.packet,
    // The proof loop starts before it knows the durable route revision. Bind
    // the runtime packet to the current journal route at the host boundary.
    routeFingerprint: state.route.fingerprint,
    routeRevision: state.route.revision,
  });
  if (canonicalMathJson(state.search.evidencePacket) === canonicalMathJson(packet))
    return { persisted: true as const, state, replayed: true as const };
  const key = `host-search-${mathDigest(canonicalMathJson([input.assignmentId, state.route.revision, input.packet]))}`;
  const result = await updateMathResearchWorkflow({
    projectRoot: input.projectRoot,
    problemId: input.problemId,
    assignmentId: input.assignmentId,
    actor: { roleId: state.workerId, roleKind: 'worker' },
    binding: state.binding,
    command: {
      action: 'record_search',
      key,
      expectedRevision: state.revision,
      packet,
    },
    env,
    hostOwned: true,
  });
  return { persisted: true as const, state: result.state, replayed: result.replayed };
}

/** State changes express organization only; no transition confers proof or solver-ready authority. */
export async function updateMathResearchWorkflow(input: {
  projectRoot: string;
  problemId: string;
  assignmentId: string;
  actor: { roleId: string; roleKind: 'lead' | 'worker' };
  command: MathResearchWorkflowCommand;
  env?: NodeJS.ProcessEnv;
  binding: MathResearchAssignmentBinding;
  /** Internal runtime boundary; never exposed through the MCP command schema. */
  hostOwned?: boolean;
  notify?: (
    notification: { key: string; target: 'lead' | 'worker'; message: string; wake?: boolean },
    state: MathResearchWorkflowState
  ) => Promise<void>;
  /** Internal outbox pump may explicitly drain pending notifications on a read. */
  drainNotifications?: boolean;
}) {
  const env = input.env ?? process.env;
  const policy = readMathResearchPolicy(env);
  const routePivotThreshold = policy?.routePivotThreshold ?? DEFAULT_MATH_ROUTE_PIVOT_THRESHOLD;
  const problemId = id.parse(input.problemId);
  const assignmentId = id.parse(input.assignmentId);
  const command = mathResearchWorkflowCommand.parse(input.command);
  const binding = mathResearchAssignmentBinding.parse(input.binding);
  if (input.actor.roleKind === 'worker' && input.actor.roleId !== binding.workerId)
    throw new Error('Research work belongs to the assigned Worker.');
  const commonRoot = resolveMathResearchCommonRoot(input.projectRoot);
  const scope = resolveMathRunHistory(commonRoot, problemId, env);
  if (!scope.runIdentity) throw new Error('Research workflow requires managed run inputs.');
  const file = path.join(scope.root, `research-${mathDigest(assignmentId)}.json`);
  const readPersistence = () => {
    const persisted = readPersistedResearch(file);
    if (!persisted) return undefined;
    const value = persisted.state;
    if (
      value.runIdentity !== scope.runIdentity ||
      value.problemId !== problemId ||
      value.assignmentId !== assignmentId ||
      value.policy !== (policy?.id ?? 'full_system')
    )
      throw new Error('Research workflow provenance mismatch.');
    if (canonicalMathJson(value.binding) !== canonicalMathJson(binding))
      throw new Error('Research workflow assignment binding changed.');
    return persisted;
  };
  const read = () => readPersistence()?.state;
  const response = (state: MathResearchWorkflowState | undefined, replayed = false) => ({
    state,
    initialization: state ? undefined : { workerId: binding.workerId, fingerprint: binding.initialRouteFingerprint },
    replayed,
    authority: 'organization' as const,
    solverReady: false as const,
  });
  const committed =
    command.action === 'get'
      ? response(read())
      : await withMathRuntimeLease({ lockPath: `${file}.lock`, flockExecutable: 'flock' }, async (lease) => {
          const persistedBefore = readPersistence();
          let state = persistedBefore ? copyResearchStateForUpdate(persistedBefore.state) : undefined;
          const digest = mathDigest(canonicalMathJson({ command, actor: input.actor }));
          const previousDigest = state ? findResearchOperation(state, command.key) : undefined;
          if (previousDigest) {
            if (previousDigest !== digest)
              throw new Error('Research idempotency key was reused with different content.');
            return response(state, true);
          }
          if (command.action === 'initialize') {
            if (input.actor.roleKind !== 'lead' && !input.hostOwned)
              throw new Error('Only the Lead initializes the active route.');
            if (state) throw new Error('Research workflow already exists.');
            if (command.workerId !== binding.workerId || command.fingerprint !== binding.initialRouteFingerprint)
              throw new Error('Research initialization must match the durable assignment.');
            state = {
              schema: 'deepscientist.mathematics.research-workflow.v1',
              runIdentity: scope.runIdentity!,
              problemId,
              assignmentId,
              binding,
              workerId: command.workerId,
              policy: policy?.id ?? 'full_system',
              revision: 0,
              route: { fingerprint: command.fingerprint, objective: command.objective, revision: 0 },
              search: createMathSearchState({
                problemId,
                statementHash: binding.statementHash,
                assignmentId,
                route: { fingerprint: command.fingerprint, objective: command.objective, revision: 0 },
              }),
              entries: [],
              decisions: [],
              operations: [],
              notifications: [],
              notebook: [],
            };
          } else {
            if (!state) throw new Error('Research workflow is not initialized.');
            if (state.revision !== command.expectedRevision) throw new Error('Research workflow revision is stale.');
            if (command.action === 'record') {
              if (input.actor.roleKind !== 'lead' && input.actor.roleId !== state.workerId)
                throw new Error('Research notes belong to the Lead and assigned Worker.');
              const observedRouteRevision = command.observedRouteRevision ?? state.route.revision;
              const staleContext =
                observedRouteRevision !== state.route.revision ||
                Boolean(
                  command.observedProofStateFingerprint &&
                  state.search?.proofStateFingerprint !== 'unknown' &&
                  command.observedProofStateFingerprint !== state.search?.proofStateFingerprint
                );
              mutableResearchArray(state, 'notebook').push({
                key: command.key,
                author: input.actor.roleId,
                routeRevision: observedRouteRevision,
                observedProofStateFingerprint: command.observedProofStateFingerprint,
                ...(staleContext ? { staleContext: true } : {}),
                kind: command.kind,
                summary: command.summary,
                evidenceRefs: command.evidenceRefs,
                relatedKeys: command.relatedKeys,
                targetConnection: command.targetConnection,
                assessment: command.assessment,
                statement: command.statement,
                dependsOn: command.dependsOn,
                artifactBindings: command.artifactBindings,
                supersedes: command.supersedes,
                experiment: command.experiment,
              });
              if (
                !staleContext &&
                (command.kind === 'finding' ||
                  command.kind === 'failed_route' ||
                  command.kind === 'dependency' ||
                  command.kind === 'experiment' ||
                  command.kind === 'decision' ||
                  (input.actor.roleKind === 'lead' && command.kind === 'next_step'))
              ) {
                mutableResearchArray(state, 'notifications').push({
                  key: `note-${mathDigest(canonicalMathJson([scope.runIdentity, assignmentId, input.actor.roleKind, command.key]))}`,
                  target: input.actor.roleKind === 'worker' ? 'lead' : 'worker',
                  delivered: false,
                  wake: input.actor.roleKind === 'lead',
                  message: `Research update for ${assignmentId}: ${command.kind}. ${command.summary}\nEvidence: ${command.evidenceRefs.join('; ')}\nRead math_research get for the current route and notebook. Relate this evidence to the original target, distinguish verified facts from conjectures, and choose the next mathematical step. This note is not a proof receipt.`,
                });
              }
            } else if (command.action === 'record_search') {
              if (input.actor.roleKind !== 'lead' && input.actor.roleId !== state.workerId)
                throw new Error('Search evidence belongs to the Lead and assigned Worker.');
              const currentSearch =
                state.search ??
                createMathSearchState({
                  problemId,
                  statementHash: binding.statementHash,
                  assignmentId,
                  route: state.route,
                });
              if (command.packet.statementHash !== binding.statementHash)
                throw new Error('math_search_statement_hash_mismatch');
              if (command.packet.routeFingerprint !== state.route.fingerprint)
                throw new Error('math_search_route_fingerprint_mismatch');
              if (command.packet.routeRevision !== state.route.revision)
                throw new Error('math_search_route_revision_mismatch');
              if (
                !input.hostOwned &&
                (command.packet.closedProof ||
                  command.packet.independentEvaluator === 'passed' ||
                  command.packet.verifierReceipt !== null)
              )
                throw new Error('math_search_runtime_owned_field');
              if (command.pivotThreshold !== undefined && command.pivotThreshold !== routePivotThreshold)
                throw new Error('math_search_pivot_threshold_is_fixed');
              if (
                command.routeSpec &&
                computeMathRouteFingerprint(command.routeSpec) !== command.packet.routeFingerprint
              )
                throw new Error('math_search_route_fingerprint_invalid');
              const sameProofState =
                currentSearch.proofStateFingerprint === command.packet.proofStateFingerprint &&
                currentSearch.evidencePacket.routeFingerprint === command.packet.routeFingerprint;
              const hostRouteNovelty =
                currentSearch.budget.observedAttempts === 0 ? 'new' : sameProofState ? 'repeated' : 'equivalent';
              state.search = advanceMathSearchState(currentSearch, command.packet, {
                route: {
                  ...state.route,
                  ...(command.routeSpec ? { spec: command.routeSpec } : {}),
                },
                routeNovelty: hostRouteNovelty,
                pivotThreshold: routePivotThreshold,
              });
            } else if (command.action === 'decide_route') {
              if (input.actor.roleKind !== 'lead') throw new Error('Only the Lead decides a main-route proposal.');
              if (
                !state.pending ||
                state.pending.id !== command.proposalId ||
                state.pending.baseRouteRevision !== state.route.revision
              )
                throw new Error('Route proposal is missing or stale.');
              if (command.decision === 'accept') {
                if (!binding.routeRevisionsSupported)
                  throw new Error('This assignment adapter does not support in-place main-route revisions.');
                state.route = {
                  fingerprint: state.pending.fingerprint,
                  objective: state.pending.objective,
                  revision: state.route.revision + 1,
                  ...(state.pending.routeSpec ? { spec: state.pending.routeSpec } : {}),
                };
                state.search = createMathSearchState({
                  problemId,
                  statementHash: binding.statementHash,
                  assignmentId,
                  route: state.route,
                });
                state.entries.forEach((item, index) => {
                  if (item.status === 'active')
                    replaceResearchArrayItem(state!, 'entries', index, { ...item, status: 'returned' });
                });
              }
              mutableResearchArray(state, 'decisions').push({
                proposalId: command.proposalId,
                decision: command.decision,
                routeRevision: state.route.revision,
                fingerprint: state.pending.fingerprint,
              });
              mutableResearchArray(state, 'notifications').push({
                key: `route-${mathDigest(canonicalMathJson([scope.runIdentity, assignmentId, input.actor.roleKind, command.key]))}`,
                target: 'worker',
                delivered: false,
                message: `Main-route proposal ${command.proposalId}: ${command.decision}. Continue assignment ${assignmentId} in the same Worker and worktree. Active route revision ${state.route.revision}: ${state.route.fingerprint}. ${state.route.objective}. This decision grants no proof or solver-ready credit.`,
              });
              delete state.pending;
            } else {
              if (input.actor.roleKind !== 'worker' || input.actor.roleId !== state.workerId)
                throw new Error('Research work belongs to the assigned Worker.');
              if (command.action === 'propose_route') {
                if (state.pending) throw new Error('A main-route decision is already pending.');
                if (command.routeSpec && computeMathRouteFingerprint(command.routeSpec) !== command.fingerprint)
                  throw new Error('math_search_route_fingerprint_invalid');
                if (
                  command.fingerprint === binding.initialRouteFingerprint ||
                  command.fingerprint === state.route.fingerprint ||
                  state.decisions.some(
                    (decision) => decision.decision === 'accept' && decision.fingerprint === command.fingerprint
                  )
                )
                  throw new Error(
                    'A route revision requires a fresh fingerprint; old route identities cannot be reused.'
                  );
                state.pending = {
                  id: command.key,
                  baseRouteRevision: state.route.revision,
                  workerId: state.workerId,
                  fingerprint: command.fingerprint,
                  objective: command.objective,
                  evidenceRefs: command.evidenceRefs,
                  routeSpec: command.routeSpec,
                };
                mutableResearchArray(state, 'notifications').push({
                  key: `route-${mathDigest(canonicalMathJson([scope.runIdentity, assignmentId, input.actor.roleKind, command.key]))}`,
                  target: 'lead',
                  delivered: false,
                  message: `Main-route proposal ${command.key} awaits your decision for assignment ${assignmentId}, problem ${problemId}. Read math_research get and decide_route at its current revision. The existing Worker and assignment remain active; this is not a completed delivery.`,
                });
              } else if (command.action === 'enter') {
                if (state.pending) throw new Error('The proposed main route is awaiting a Lead decision.');
                if (
                  (command.kind === 'retrieval' && policy && !policy.retrievalLoop) ||
                  (command.kind === 'exploration' && policy && !policy.explorationLoop)
                )
                  throw new Error(
                    'This specialized loop is disabled by the frozen policy; ordinary mathematics work remains available.'
                  );
                if (state.entries.some((item) => item.status === 'active'))
                  throw new Error('Return from the current research entry first.');
                const sameBottleneck = state.entries.filter(
                  (item) =>
                    item.bottleneck === command.bottleneck &&
                    item.routeRevision === state!.route.revision &&
                    item.kind === command.kind
                );
                const entryLimit = policy
                  ? command.kind === 'retrieval'
                    ? policy.retrievalRoundLimit
                    : policy.explorationVersionLimit
                  : undefined;
                const consumedRounds = sameBottleneck.reduce((total, item) => total + item.rounds, 0);
                if (entryLimit !== null && entryLimit !== undefined && consumedRounds >= entryLimit)
                  throw new Error('Research entry bottleneck was already entered to its advisory limit.');
                const unproductiveLimit = policy?.unproductiveExplorationLimit;
                if (
                  unproductiveLimit !== null &&
                  unproductiveLimit !== undefined &&
                  command.kind === 'exploration' &&
                  sameBottleneck.slice(-unproductiveLimit).length === unproductiveLimit &&
                  sameBottleneck.slice(-unproductiveLimit).every((item) => item.productive === false)
                )
                  throw new Error('Change research method after consecutive unproductive exploration entries.');
                mutableResearchArray(state, 'entries').push({
                  id: command.key,
                  kind: command.kind,
                  bottleneck: command.bottleneck,
                  routeRevision: state.route.revision,
                  rounds: 0,
                  status: 'active',
                });
              } else {
                const entryIndex = state.entries.findIndex((item) => item.id === command.entryId);
                const item = state.entries[entryIndex] ? { ...state.entries[entryIndex]! } : undefined;
                if (!item || item.status !== 'active' || item.routeRevision !== state.route.revision)
                  throw new Error('Research entry is missing, returned or stale.');
                replaceResearchArrayItem(state, 'entries', entryIndex, item);
                if (command.action === 'advance') {
                  const limit = policy
                    ? item.kind === 'retrieval'
                      ? policy.retrievalRoundLimit
                      : policy.explorationVersionLimit
                    : Infinity;
                  if (limit !== null && limit !== undefined && item.rounds >= limit)
                    throw new Error('Research entry limit reached; return evidence to the main proof.');
                  item.rounds += 1;
                } else {
                  item.status = 'returned';
                  item.productive = command.productive;
                }
              }
            }
            state.revision += 1;
          }
          appendResearchOperation(state, { key: command.key, digest });
          lease.assertHeld();
          persistResearch(file, persistedBefore, state);
          if (!persistedBefore || researchArrayChanges.get(state)?.has('notifications'))
            syncMathResearchOutboxIndex(commonRoot, state, env);
          return response(state);
        });
  if (!input.notify || (command.action === 'get' && input.drainNotifications !== true)) return committed;
  const eligible = (item: MathResearchWorkflowState['notifications'][number]) =>
    !item.delivered && (item.target === 'lead' ? 'worker' : 'lead') === input.actor.roleKind;
  if (!committed.state?.notifications.some(eligible)) return committed;
  // The durable notification list is an outbox. Network latency never holds the state mutation lease.
  // Delivery is at least once: an interrupted acknowledgement retries the same Core idempotency key.
  try {
    await withMathRuntimeLease(
      { lockPath: `${file}.outbox-${input.actor.roleKind}.lock`, flockExecutable: 'flock' },
      async (deliveryLease) => {
        const snapshot = read();
        for (const notification of snapshot?.notifications.filter(eligible) ?? []) {
          deliveryLease.assertHeld();
          // eslint-disable-next-line no-await-in-loop -- Preserve notification order and acknowledge each durable effect.
          await input.notify!(
            {
              key: notification.key,
              target: notification.target,
              message: notification.message,
              ...(notification.wake === false ? { wake: false } : {}),
            },
            snapshot!
          );
          // eslint-disable-next-line no-await-in-loop -- Merge each acknowledgement under a fresh short mutation lease.
          await withMathRuntimeLease({ lockPath: `${file}.lock`, flockExecutable: 'flock' }, async (lease) => {
            const persistedBefore = readPersistence();
            const current = persistedBefore ? copyResearchStateForUpdate(persistedBefore.state) : undefined;
            const pendingIndex = current?.notifications.findIndex((item) => item.key === notification.key) ?? -1;
            const pending = current?.notifications[pendingIndex];
            if (!current || !pending || !eligible(pending)) return;
            replaceResearchArrayItem(current, 'notifications', pendingIndex, { ...pending, delivered: true });
            deliveryLease.assertHeld();
            lease.assertHeld();
            persistResearch(file, persistedBefore, current);
            syncMathResearchOutboxIndex(commonRoot, current, env);
          });
        }
      }
    );
  } catch (error) {
    // Another delivery/mutation owns its lease. The committed outbox remains retryable.
    if (!(error instanceof Error) || error.message !== 'math_runtime_lease_busy') throw error;
  }
  return response(read(), committed.replayed);
}
