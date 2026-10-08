import fs from 'node:fs';
import path from 'node:path';
import type { MathRunBinding } from "../common/types/team/mathRuntimeContracts";
import { assertMathCanonicalPath, resolveMathRunProjectPaths } from "./mathRunBinding";
import { canonicalMathJson, mathDigest, withMathRuntimeLease, writeMathJsonDurable } from "./mathRuntimeIo";
import { projectRuntimeMathAssignmentToExecutionView } from "./mathAssignmentExecutionAdapter";
import { normalizeRuntimeMathAssignment } from "./mathAssignmentJournal";
import { MathArtifactStore } from "./mathArtifactStore";
import type { listProjectGitResearchTeamAssignments } from "../project-git/index";

type Receipt = ReturnType<typeof listProjectGitResearchTeamAssignments>[number];
const record = (value: unknown): Record<string, unknown> =>
  value && typeof value === 'object' && !Array.isArray(value) ? (value as Record<string, unknown>) : {};
const pointer = (binding: MathRunBinding, id: string) =>
  path.join(path.dirname(binding.artifactStoreRoot), 'lite-blockers', `${mathDigest(id)}.json`);
const MAX_RECENT_PROBES = 8;
const MAX_RECENT_BLOCKERS = MAX_RECENT_PROBES + 1;
// Eight probes and one owner report fit even when each excerpt is JSON-escaped.
const MAX_BLOCKER_INDEX_BYTES = 128 * 1024;
const MAX_BLOCKER_CONTEXT_BYTES = 64 * 1024;
export type BlockerReference = Readonly<{
  artifactId: string;
  sourceHash: string;
  diagnosticsExcerpt?: string;
  goalsExcerpt?: string;
  attemptsExcerpt?: string;
  /**
   * `probe` is a host observation bound to actual source bytes. `owner_boundary`
   * is the proof owner's own account of why it stopped, recorded at a blocked
   * handoff. Only a probe observation advances the evidence boundary: an owner
   * report must not turn a notes-only retry into a new terminal delivery.
   */
  provenance?: 'probe' | 'owner_boundary';
}>;
export class MathBlockerHistoryUnavailableError extends Error {
  constructor() {
    super('math_blocker_history_unavailable');
  }
}

function readBlockerPointer(binding: MathRunBinding, receipt: Receipt): BlockerReference[] {
  const file = pointer(binding, receipt.assignmentId);
  assertMathCanonicalPath(file);
  if (!fs.existsSync(file)) return [];
  let value: Record<string, unknown>;
  let opened = false;
  try {
    const descriptor = fs.openSync(file, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK);
    opened = true;
    try {
      const before = fs.fstatSync(descriptor, { bigint: true });
      if (!before.isFile() || before.nlink !== BigInt(1)) throw new Error('math_blocker_context_integrity');
      if (before.size > BigInt(MAX_BLOCKER_INDEX_BYTES)) throw new MathBlockerHistoryUnavailableError();
      const buffer = Buffer.alloc(MAX_BLOCKER_INDEX_BYTES + 1);
      let bytes = 0;
      while (bytes < buffer.length) {
        const read = fs.readSync(descriptor, buffer, bytes, buffer.length - bytes, null);
        if (!read) break;
        bytes += read;
      }
      const after = fs.fstatSync(descriptor, { bigint: true });
      const current = fs.lstatSync(file, { bigint: true });
      if (
        before.size !== after.size ||
        before.mtimeNs !== after.mtimeNs ||
        before.ctimeNs !== after.ctimeNs ||
        current.dev !== before.dev ||
        current.ino !== before.ino ||
        current.nlink !== BigInt(1)
      )
        throw new Error('math_blocker_context_integrity');
      if (bytes > MAX_BLOCKER_INDEX_BYTES) throw new MathBlockerHistoryUnavailableError();
      let text: string;
      try {
        text = new TextDecoder('utf-8', { fatal: true }).decode(buffer.subarray(0, bytes));
      } catch {
        throw new MathBlockerHistoryUnavailableError();
      }
      value = record(JSON.parse(text));
    } finally {
      fs.closeSync(descriptor);
    }
  } catch (error) {
    if (error instanceof SyntaxError) throw new MathBlockerHistoryUnavailableError();
    if ((error as NodeJS.ErrnoException).code === 'ENOENT') {
      if (opened) throw new Error('math_blocker_context_integrity', { cause: error });
      return [];
    }
    if ((error as NodeJS.ErrnoException).code === 'ELOOP')
      throw new Error('math_blocker_context_integrity', { cause: error });
    throw error;
  }
  const recent = value.recent;
  const valid = (entry: unknown): entry is BlockerReference => {
    const item = record(entry);
    return (
      typeof item.artifactId === 'string' &&
      /^blocker-[a-f0-9]{64}$/u.test(item.artifactId) &&
      typeof item.sourceHash === 'string' &&
      /^[a-f0-9]{64}$/u.test(item.sourceHash) &&
      ['diagnosticsExcerpt', 'goalsExcerpt', 'attemptsExcerpt'].every(
        (field) => item[field] === undefined || (typeof item[field] === 'string' && item[field].length <= 768)
      ) &&
      (item.provenance === undefined || item.provenance === 'probe' || item.provenance === 'owner_boundary')
    );
  };
  if (
    value.bindingDigest !== mathDigest(canonicalMathJson(binding)) ||
    value.assignmentId !== receipt.assignmentId ||
    !valid(value) ||
    (recent !== undefined &&
      (!Array.isArray(recent) ||
        recent.length > MAX_RECENT_BLOCKERS ||
        !recent.every(valid) ||
        recent[0]?.artifactId !== value.artifactId ||
        recent[0]?.sourceHash !== value.sourceHash ||
        new Set(recent.map((entry: BlockerReference) => entry.artifactId)).size !== recent.length))
  )
    throw new Error('math_blocker_context_integrity');
  return recent === undefined ? ([value] as BlockerReference[]) : (recent as BlockerReference[]);
}

type VerifiedBlocker = BlockerReference & Readonly<{ assignmentId: string; observationDigest: string }>;
const verifiedBlockers = new Map<string, VerifiedBlocker>();
const planningStores = new Map<string, MathArtifactStore>();

export function mathBlockerPlanningStore(binding: MathRunBinding): MathArtifactStore {
  const key = `${binding.artifactStoreRoot}:${binding.runId}`;
  let store = planningStores.get(key);
  if (!store) {
    store = new MathArtifactStore({
      runRoot: path.dirname(binding.artifactStoreRoot),
      runId: binding.runId,
      flockExecutable: '/usr/bin/flock',
    });
    planningStores.set(key, store);
    if (planningStores.size > 16) {
      const oldest = planningStores.keys().next().value!;
      void planningStores
        .get(oldest)!
        .closeReaders()
        .catch(() => {});
      planningStores.delete(oldest);
    }
  }
  return store;
}

export function cachedMathBlockerReference(binding: MathRunBinding, artifactId: string): VerifiedBlocker | undefined {
  return verifiedBlockers.get(`${binding.artifactStoreRoot}:${artifactId}`);
}

export async function readVerifiedMathBlockerReference(
  binding: MathRunBinding,
  target: Receipt,
  artifactId: string,
  signal: AbortSignal
): Promise<VerifiedBlocker | undefined> {
  signal.throwIfAborted();
  const store = mathBlockerPlanningStore(binding);
  const access = {
    role: 'worker' as const,
    assignmentId: target.assignmentId,
    grants: new Set(normalizeRuntimeMathAssignment(target.assignment).artifactGrants),
  };
  const ref = `math-artifact://${binding.runId}/${artifactId}`;
  const key = `${binding.artifactStoreRoot}:${artifactId}`;
  const cached = verifiedBlockers.get(key);
  // Reauthorize and validate the immutable object even on a metadata cache hit.
  const first = await store.read({ ref, maxBytes: cached ? 1 : 2048 }, access);
  if (artifactId !== `blocker-${first.sha256}`) throw new Error('math_blocker_context_integrity');
  signal.throwIfAborted();
  if (cached) {
    const metadata = (await store.listMetadata(access)).find((entry) => entry.artifactId === artifactId);
    if (metadata?.assignmentId !== cached.assignmentId) throw new Error('math_blocker_context_integrity');
    signal.throwIfAborted();
    return cached;
  }
  if (first.totalBytes > MAX_BLOCKER_CONTEXT_BYTES) return undefined;
  let text = first.text;
  let offset = first.nextOffsetBytes;
  while (offset !== undefined) {
    signal.throwIfAborted();
    const next = await store.read({ ref, offsetBytes: offset, maxBytes: 2048 }, access);
    text += next.text;
    offset = next.nextOffsetBytes;
  }
  let value: Record<string, unknown>;
  try {
    value = record(JSON.parse(text));
  } catch {
    throw new Error('math_blocker_context_integrity');
  }
  if (
    artifactId !== `blocker-${mathDigest(text)}` ||
    typeof value.assignmentId !== 'string' ||
    typeof value.sourceHash !== 'string' ||
    !/^[a-f0-9]{64}$/u.test(value.sourceHash)
  )
    throw new Error('math_blocker_context_integrity');
  const metadata = (await store.listMetadata(access)).find((entry) => entry.artifactId === artifactId);
  if (metadata?.assignmentId !== value.assignmentId) throw new Error('math_blocker_context_integrity');
  const compact = (v: unknown): string => (typeof v === 'string' ? v : canonicalMathJson(v ?? [])).slice(0, 768);
  const result: VerifiedBlocker = {
    artifactId,
    assignmentId: value.assignmentId,
    provenance: value.provenance === 'owner_boundary_report' ? 'owner_boundary' : 'probe',
    observationDigest: mathDigest(
      canonicalMathJson({
        sourceHash: value.sourceHash,
        diagnostics: value.diagnostics,
        goals: value.goals,
        attempts: value.attempts,
      })
    ),
    sourceHash: value.sourceHash,
    goalsExcerpt: compact(value.goals),
    diagnosticsExcerpt: compact(value.provenance === 'owner_boundary_report' ? value.summary : value.diagnostics),
    attemptsExcerpt: compact(value.attempts),
  };
  verifiedBlockers.set(key, result);
  if (verifiedBlockers.size > 256) verifiedBlockers.delete(verifiedBlockers.keys().next().value!);
  return result;
}

// Host-generated diagnostic memory, not a proof receipt or a model-side protocol.
export function mathLiteBlockerObservation(payload: Record<string, unknown>) {
  const result = record(payload.result ?? payload.probe);
  const current = record(result.current ?? result.state);
  const sourceHash = result.sourceHash ?? current.sourceHash;
  if (typeof sourceHash !== 'string') return;
  const diagnostics = String(current.diagnostics ?? result.diagnostics ?? '');
  const goals = current.goals ?? result.remainingGoals ?? result.after ?? current.openGoals ?? [];
  if (!diagnostics && !(Array.isArray(goals) && goals.length)) return;
  return { sourceHash, diagnostics, goals, attempts: result.attempts ?? [] };
}

export async function publishMathLiteBlockerContext(
  binding: MathRunBinding,
  receipt: Receipt,
  payload: Record<string, unknown>,
  signal: AbortSignal
): Promise<string | undefined> {
  signal.throwIfAborted();
  const view = projectRuntimeMathAssignmentToExecutionView(receipt.assignment, {
    expectedRunId: binding.runId,
    expectedBindingDigest: mathDigest(canonicalMathJson(binding)),
    expectedTargetSlotId: receipt.slotId,
  });
  if (view.kind !== 'formalize' || !view.sourceRootRelative) return;
  const observation = mathLiteBlockerObservation(payload);
  if (!observation) return;
  const { sourceHash, diagnostics, goals, attempts } = observation;
  const { solverProjectRoot } = resolveMathRunProjectPaths(
    binding,
    binding.workspace,
    receipt.preparedGit?.worktreePath
  );
  const sourceRoot = path.resolve(solverProjectRoot, view.sourceRootRelative);
  const sources = (view.request.verificationTargets ?? []).flatMap((target) => {
    const file = path.resolve(sourceRoot, target.pathRelative);
    if (!file.startsWith(`${sourceRoot}${path.sep}`)) return [];
    assertMathCanonicalPath(file);
    if (!fs.existsSync(file) || fs.statSync(file).size > 2 * 1024 * 1024) return [];
    const source = fs.readFileSync(file, 'utf8');
    return mathDigest(source) === sourceHash ? [{ path: target.pathRelative, source }] : [];
  });
  if (!sources.length) return; // Never pair old diagnostics with newer source bytes.
  const content = {
    provisional: true,
    assignmentId: receipt.assignmentId,
    sourceHash,
    sources,
    diagnostics,
    goals,
    attempts,
    instruction:
      'Compiler diagnostic context only. Goal text includes local hypotheses. Investigate the specific unresolved bridge; preserve failed attempts as evidence, not proof.',
  };
  const text = canonicalMathJson(content);
  const artifactId = `blocker-${mathDigest(text)}`;
  const excerpt = (value: unknown) => String(value ?? '').slice(0, 768);
  const reference: BlockerReference = {
    artifactId,
    sourceHash,
    provenance: 'probe',
    diagnosticsExcerpt: excerpt(diagnostics),
    goalsExcerpt: excerpt(
      Array.isArray(goals)
        ? goals.map((goal) => (typeof goal === 'string' ? goal : canonicalMathJson(goal))).join('\n')
        : goals
    ),
    attemptsExcerpt: excerpt(
      Array.isArray(attempts)
        ? attempts
            .slice(0, 4)
            .map((attempt) => {
              const item = record(attempt);
              return `${String(item.action ?? '')}: ${String(item.status ?? '')} ${String(item.diagnostics ?? '')}`;
            })
            .join('\n')
        : ''
    ),
  };
  const store = await ensureMathBlockerStore(binding);
  await store.publishText({
    artifactId,
    assignmentId: receipt.assignmentId,
    kind: 'diagnostic',
    sensitivity: 'solver-visible',
    mediaType: 'application/json',
    text,
  });
  signal.throwIfAborted();
  await writeMathBlockerPointer(binding, receipt, reference, signal);
  return artifactId;
}

/** Publish for the advisory boundary index. Shared by probe and owner boundaries. */
async function ensureMathBlockerStore(binding: MathRunBinding): Promise<MathArtifactStore> {
  const store = new MathArtifactStore({
    runRoot: path.dirname(binding.artifactStoreRoot),
    runId: binding.runId,
    flockExecutable: '/usr/bin/flock',
  });
  await store.initialize();
  return store;
}

/** Prepend one reference to the slot's advisory index under the existing lock. */
async function writeMathBlockerPointer(
  binding: MathRunBinding,
  receipt: Receipt,
  reference: BlockerReference,
  signal: AbortSignal
): Promise<void> {
  const file = pointer(binding, receipt.assignmentId);
  assertMathCanonicalPath(file);
  fs.mkdirSync(path.dirname(file), { recursive: true, mode: 0o700 });
  await withMathRuntimeLease({ lockPath: `${file}.lock`, flockExecutable: '/usr/bin/flock', signal }, async (lease) => {
    let previous: BlockerReference[];
    try {
      previous = readBlockerPointer(binding, receipt);
    } catch (error) {
      if (!(error instanceof MathBlockerHistoryUnavailableError)) throw error;
      // The new observation has already been published and source-checked. Rebuild
      // only this advisory index; previously published artifacts remain intact.
      previous = [];
    }
    // Owner notes must not evict a measured observation: removing a probe would
    // change the checked-evidence revision even though no new check took place.
    let probes = 0;
    let ownerReports = 0;
    const recent = [reference, ...previous.filter((item) => item.artifactId !== reference.artifactId)].filter((item) =>
      item.provenance === 'owner_boundary' ? ++ownerReports <= 1 : ++probes <= MAX_RECENT_PROBES
    );
    lease.assertHeld();
    signal.throwIfAborted();
    writeMathJsonDurable(file, {
      bindingDigest: mathDigest(canonicalMathJson(binding)),
      assignmentId: receipt.assignmentId,
      artifactId: reference.artifactId,
      sourceHash: reference.sourceHash,
      recent,
    });
  });
}

/** Longest boundary report retained from one blocked delivery. */
const MAX_BLOCKER_BOUNDARY_CHARS = 4096;

/**
 * Record a proof owner's own account of a mathematical boundary when it hands the
 * assignment back as `blocked`.
 *
 * The diagnostic publisher below only fires from a Lean probe payload, so a
 * blocked delivery that never probed left no boundary record at all: run 23
 * attempt 14 published exactly one blocker for the whole run and its content was
 * `math_search_provider_unavailable`, not the mathematical gap. The slot then sat
 * idle for 26 minutes because nothing in the run could tell a successor where the
 * argument had stopped.
 *
 * This is the owner's own statement, not a host observation. It reuses the same
 * artifact and pointer contract so the existing lineage readers see it, and it
 * retains the latest owner report alongside the recent measured observations.
 * An earlier infrastructure diagnostic must not hide the later mathematical gap.
 */
export async function publishMathLiteBlockerBoundary(
  binding: MathRunBinding,
  receipt: Receipt,
  input: Readonly<{ summary?: string; blockers?: readonly string[] }>,
  signal: AbortSignal
): Promise<string | undefined> {
  signal.throwIfAborted();
  const view = projectRuntimeMathAssignmentToExecutionView(receipt.assignment, {
    expectedRunId: binding.runId,
    expectedBindingDigest: mathDigest(canonicalMathJson(binding)),
    expectedTargetSlotId: receipt.slotId,
  });
  if (view.kind !== 'formalize' || !view.sourceRootRelative) return;
  const goals = (input.blockers ?? [])
    .map((item) => String(item).slice(0, 512))
    .filter((item) => item.trim().length > 0)
    .slice(0, 8);
  const summary = String(input.summary ?? '').slice(0, MAX_BLOCKER_BOUNDARY_CHARS);
  if (!goals.length && !summary.trim()) return;
  const store = await ensureMathBlockerStore(binding);
  const { solverProjectRoot } = resolveMathRunProjectPaths(
    binding,
    binding.workspace,
    receipt.preparedGit?.worktreePath
  );
  const sourceRoot = path.resolve(solverProjectRoot, view.sourceRootRelative);
  const sources = (view.request.verificationTargets ?? []).flatMap((target) => {
    const file = path.resolve(sourceRoot, target.pathRelative);
    if (!file.startsWith(`${sourceRoot}${path.sep}`)) return [];
    assertMathCanonicalPath(file);
    if (!fs.existsSync(file) || fs.statSync(file).size > 2 * 1024 * 1024) return [];
    return [{ path: target.pathRelative, source: fs.readFileSync(file, 'utf8') }];
  });
  // The boundary is the owner's statement about its own captured source. Hash the
  // captured bytes so the reference still identifies concrete source, and mark the
  // provenance so no reader mistakes it for a checked diagnostic.
  const sourceHash = mathDigest(canonicalMathJson(sources.map(({ path: file, source }) => [file, mathDigest(source)])));
  const content = {
    provisional: true,
    provenance: 'owner_boundary_report',
    assignmentId: receipt.assignmentId,
    summary,
    sourceHash,
    sources,
    diagnostics: '',
    goals,
    attempts: [] as string[],
    instruction:
      'The proof owner reported this mathematical boundary when handing the assignment back. It is an unverified statement about its captured source, not a host observation and not a proof receipt. Treat the listed gaps as the starting point and verify anything you rely on.',
  };
  let text = canonicalMathJson(content);
  if (Buffer.byteLength(text, 'utf8') > MAX_BLOCKER_CONTEXT_BYTES) {
    // Long proof files must not hide a short handoff behind the reader's bound.
    // The sealed delivery owns the full source; this advisory artifact retains
    // its identity without duplicating arbitrarily large code in planning memory.
    const compact = {
      ...content,
      sources: sources.map(({ path: file, source }) => ({
        path: file,
        sha256: mathDigest(source),
        bytes: Buffer.byteLength(source, 'utf8'),
      })),
      sourceSnapshotsOmitted: true,
      sourceCount: sources.length,
    };
    text = canonicalMathJson(compact);
    // Extremely long path lists remain identifiable by the aggregate sourceHash.
    if (Buffer.byteLength(text, 'utf8') > MAX_BLOCKER_CONTEXT_BYTES)
      text = canonicalMathJson({ ...compact, sources: [], sourcePathsOmitted: true });
  }
  const artifactId = `blocker-${mathDigest(text)}`;
  const excerpt = (value: unknown) => String(value ?? '').slice(0, 768);
  const reference: BlockerReference = {
    artifactId,
    sourceHash,
    diagnosticsExcerpt: excerpt(summary),
    goalsExcerpt: excerpt(goals.join('\n')),
    attemptsExcerpt: '',
    provenance: 'owner_boundary',
  };
  await store.publishText({
    artifactId,
    assignmentId: receipt.assignmentId,
    kind: 'diagnostic',
    sensitivity: 'solver-visible',
    mediaType: 'application/json',
    text,
  });
  signal.throwIfAborted();
  await writeMathBlockerPointer(binding, receipt, reference, signal);
  return artifactId;
}

export function readMathLiteBlockerHistory(binding: MathRunBinding, receipt: Receipt): BlockerReference[] {
  const view = projectRuntimeMathAssignmentToExecutionView(receipt.assignment, {
    expectedRunId: binding.runId,
    expectedBindingDigest: mathDigest(canonicalMathJson(binding)),
    expectedTargetSlotId: receipt.slotId,
  });
  if (view.kind !== 'formalize') throw new Error('math_blocker_formalizer_required');
  return readBlockerPointer(binding, receipt);
}

export function readMathLiteBlockerLineage(
  binding: MathRunBinding,
  target: Receipt,
  receipts: readonly Receipt[]
): Array<BlockerReference & Readonly<{ assignmentId: string }>> {
  const seen = new Set<string>();
  const result: Array<BlockerReference & Readonly<{ assignmentId: string }>> = [];
  let current: Receipt | undefined = target;
  const scopeId = normalizeRuntimeMathAssignment(target.assignment).scopeId;
  while (current) {
    if (seen.has(current.assignmentId)) throw new Error('math_blocker_predecessor_cycle');
    seen.add(current.assignmentId);
    if (
      current.teamId !== target.teamId ||
      current.slotId !== target.slotId ||
      normalizeRuntimeMathAssignment(current.assignment).scopeId !== scopeId
    )
      throw new Error('math_blocker_predecessor_identity');
    try {
      result.push(
        ...readMathLiteBlockerHistory(binding, current).map((item) => ({
          ...item,
          assignmentId: current!.assignmentId,
        }))
      );
    } catch (error) {
      if (!(error instanceof MathBlockerHistoryUnavailableError)) throw error;
    }
    const parentId = normalizeRuntimeMathAssignment(current.assignment).request.predecessorAssignmentId;
    current = parentId ? receipts.find((receipt) => receipt.assignmentId === parentId) : undefined;
    if (parentId && (!current || current.state !== 'superseded'))
      throw new Error('math_blocker_predecessor_unavailable');
  }
  return result;
}

export function readMathLiteBlockerContext(binding: MathRunBinding, receipt: Receipt): string[] {
  const latest = readMathLiteBlockerHistory(binding, receipt)[0];
  return latest ? [`math-artifact://${binding.runId}/${latest.artifactId}`] : [];
}
