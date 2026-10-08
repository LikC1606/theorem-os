import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { z } from 'zod';
import { assertMathCanonicalPath, readMathRunBinding } from "./mathRunBinding";
import { canonicalMathJson, mathDigest, readMathJson, syncMathDirectory } from "./mathRuntimeIo";
import { MATH_RUN_INPUTS_ENV, verifyMathRunInputs, verifyMathRunInputsEnvironment } from "./mathRunInputs";
import { inspectLeanDeclarationRegions, type MathematicsVerifierResult } from "./verifier";

const hash = z.string().regex(/^[a-f0-9]{64}$/u);
const id = z.string().regex(/^[A-Za-z0-9_-]{1,160}$/u);
const time = z.number().finite().nonnegative().nullable();
const eventInput = z
  .object({
    kind: z.enum([
      'shared',
      'received',
      'artifact_read',
      'checked',
      'candidate_adopted',
      'final_checked',
      'final_dependency',
    ]),
    runId: id,
    assignmentId: id,
    consumerAssignmentId: id.optional(),
    shareId: hash.optional(),
    artifactId: id.optional(),
    blockId: hash.optional(),
    sourceHash: hash.optional(),
    candidateSourceHash: hash.optional(),
    declarationName: z
      .string()
      .regex(/^[A-Za-z_][A-Za-z0-9_'.]*$/u)
      .max(512)
      .optional(),
    declarationSourceHash: hash.optional(),
    supportingDeclarations: z
      .array(z.object({ name: z.string().max(512), sourceHash: hash }).strict())
      .max(32)
      .optional(),
    targetId: id.optional(),
    targetCommit: z
      .string()
      .regex(/^(?:[a-f0-9]{40}|[a-f0-9]{64})$/u)
      .optional(),
    statementHash: hash.optional(),
    outcome: z.enum(['verified', 'failed', 'blocked', 'unavailable']).optional(),
    openGoalsBefore: z.number().int().nonnegative().optional(),
    openGoalsAfter: z.number().int().nonnegative().optional(),
    observedAt: time,
    durationMs: time.optional(),
  })
  .strict();
const persistedEvent = eventInput
  .extend({
    schema: z.literal('deepscientist.math.proof-impact.v1'),
    eventId: hash,
  })
  .strict();
export type MathProofImpactEvent = z.infer<typeof eventInput>;
export type MathProofImpactScope = Readonly<{ runRoot: string; runId: string }>;

function eventIdentity(event: MathProofImpactEvent): string {
  const { observedAt: _observedAt, durationMs: _durationMs, ...identity } = event;
  return mathDigest(canonicalMathJson(identity));
}

/** Optional host telemetry, never proof authority. First durable observation survives replay. */
export function recordMathProofImpact(scope: MathProofImpactScope, input: MathProofImpactEvent): boolean {
  let temporary: string | undefined;
  try {
    const event = eventInput.parse(input);
    if (event.runId !== scope.runId) return false;
    assertMathCanonicalPath(scope.runRoot);
    const directory = path.join(scope.runRoot, 'proof-impact');
    fs.mkdirSync(directory, { recursive: true, mode: 0o700 });
    assertMathCanonicalPath(directory);
    const eventId = eventIdentity(event);
    const destination = path.join(directory, `${eventId}.json`);
    if (fs.existsSync(destination)) {
      const previous = persistedEvent.parse(readMathJson(destination));
      const { schema: _schema, eventId: previousId, ...previousInput } = previous;
      return previousId === eventId && eventIdentity(previousInput) === eventId;
    }
    temporary = path.join(directory, `.${crypto.randomUUID()}.tmp`);
    const serialized = canonicalMathJson({ ...event, schema: 'deepscientist.math.proof-impact.v1', eventId });
    if (Buffer.byteLength(serialized) > 64 * 1024) return false;
    const descriptor = fs.openSync(
      temporary,
      fs.constants.O_CREAT | fs.constants.O_EXCL | fs.constants.O_WRONLY,
      0o600
    );
    try {
      fs.writeFileSync(descriptor, serialized);
      fs.fsyncSync(descriptor);
    } finally {
      fs.closeSync(descriptor);
    }
    // Atomic no-replace publication allows independent MCP processes to replay safely.
    try {
      fs.linkSync(temporary, destination);
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code !== 'EEXIST') throw error;
    }
    fs.unlinkSync(temporary);
    temporary = undefined;
    syncMathDirectory(directory);
    return true;
  } catch {
    return false;
  } finally {
    if (temporary)
      try {
        fs.unlinkSync(temporary);
      } catch {
        /* Incomplete optional telemetry is not a proof failure. */
      }
  }
}

/** No user text or environment contents are returned or stored. */
export function readMathProofImpactScope(env: NodeJS.ProcessEnv = process.env): MathProofImpactScope | undefined {
  if (!env[MATH_RUN_INPUTS_ENV]) return undefined;
  verifyMathRunInputsEnvironment(env);
  const binding = readMathRunBinding(verifyMathRunInputs(JSON.parse(env[MATH_RUN_INPUTS_ENV]!)));
  return { runRoot: path.dirname(binding.artifactStoreRoot), runId: binding.runId };
}

export function readMathProofImpactEvents(runRoot: string, runId: string) {
  const events: z.infer<typeof persistedEvent>[] = [];
  let invalidRecords = 0;
  const directory = path.join(runRoot, 'proof-impact');
  if (!fs.existsSync(directory)) return { availability: 'missing' as const, events, invalidRecords };
  try {
    assertMathCanonicalPath(directory);
    for (const filename of fs.readdirSync(directory)) {
      if (!/^[a-f0-9]{64}\.json$/u.test(filename)) continue;
      try {
        const file = path.join(directory, filename);
        assertMathCanonicalPath(file);
        if (fs.lstatSync(file).size > 64 * 1024) throw new Error('oversized');
        const event = persistedEvent.parse(readMathJson(file));
        const { schema: _schema, eventId, ...input } = event;
        if (event.runId !== runId || eventId !== filename.slice(0, -5) || eventIdentity(input) !== eventId)
          throw new Error('identity');
        events.push(event);
      } catch {
        invalidRecords++;
      }
    }
  } catch {
    invalidRecords++;
  }
  return { availability: invalidRecords ? ('partial' as const) : ('available' as const), events, invalidRecords };
}

const firstTime = (events: readonly MathProofImpactEvent[], kind: MathProofImpactEvent['kind']) => {
  const times = events.filter((event) => event.kind === kind).map((event) => event.observedAt);
  return times.length && times.every((value): value is number => value !== null) ? Math.min(...times) : null;
};
const latency = (from: number | null, to: number | null) =>
  from !== null && to !== null && to >= from ? to - from : null;

/** Counts are observations. Receiving/reading/checking a report never implies adoption or final use. */
export function readMathProofImpactSummary(runRoot: string, runId: string, options: { targetCommit?: string } = {}) {
  const read = readMathProofImpactEvents(runRoot, runId);
  const { availability, invalidRecords } = read;
  const events = read.events.filter(
    (event) =>
      !options.targetCommit ||
      !['final_checked', 'final_dependency'].includes(event.kind) ||
      event.targetCommit === options.targetCommit
  );
  const shares = [...new Set(events.flatMap((event) => (event.shareId ? [event.shareId] : [])))]
    .toSorted()
    .map((shareId) => {
      const related = events.filter((event) => event.shareId === shareId);
      const sharedAt = firstTime(related, 'shared');
      const receivedAt = firstTime(related, 'received');
      const readAt = firstTime(related, 'artifact_read');
      const checkedAt = firstTime(
        related.filter((event) => event.outcome === 'verified'),
        'checked'
      );
      const adoptedAt = firstTime(related, 'candidate_adopted');
      const finalDependencyAt = firstTime(related, 'final_dependency');
      return {
        shareId,
        sharedAt,
        receivedAt,
        readAt,
        checkedAt,
        adoptedAt,
        finalDependencyAt,
        shareToReceivedMs: latency(sharedAt, receivedAt),
        shareToReadMs: latency(sharedAt, readAt),
        shareToAdoptionMs: latency(sharedAt, adoptedAt),
        shareToFinalDependencyMs: latency(sharedAt, finalDependencyAt),
      };
    });
  const kinds = eventInput.shape.kind.options;
  const progressTimes = events
    .filter((event) => event.kind === 'candidate_adopted' || event.kind === 'final_dependency')
    .map((event) => event.observedAt);
  return {
    schema: 'deepscientist.math.proof-impact-summary.v1' as const,
    runId,
    availability,
    invalidRecords,
    counts: Object.fromEntries(
      kinds.map((kind) => [kind, events.filter((event) => event.kind === kind).length])
    ) as Record<MathProofImpactEvent['kind'], number>,
    finalDependencyCoverage: events.some((event) => event.kind === 'final_checked')
      ? ('observed' as const)
      : ('unknown' as const),
    finalChecks: events
      .filter((event) => event.kind === 'final_checked')
      .map(({ targetId, targetCommit, sourceHash, observedAt }) => ({
        targetId,
        targetCommit,
        sourceHash,
        observedAt,
      })),
    lastVerifiedProgressAt:
      progressTimes.length && progressTimes.every((value): value is number => value !== null)
        ? Math.max(...progressTimes)
        : null,
    shares,
  };
}

/** Exact full declaration bytes, including proof body, prevent same-name replacement attribution. */
export function mathProofImpactDeclarationHash(source: string, name: string): string | undefined {
  const regions = inspectLeanDeclarationRegions(source).filter((region) => region.name === name);
  return regions.length === 1
    ? mathDigest(source.slice(regions[0]!.startOffset, regions[0]!.endOffset).trim())
    : undefined;
}

/** Bounded final-receipt projection; per-share identities stay in the run journal. */
export function compactMathProofImpactSummary(summary: ReturnType<typeof readMathProofImpactSummary>) {
  const { shares, finalChecks, ...compact } = summary;
  const latencyFields = [
    'shareToReceivedMs',
    'shareToReadMs',
    'shareToAdoptionMs',
    'shareToFinalDependencyMs',
  ] as const;
  return {
    ...compact,
    shareCount: shares.length,
    finalCheckCount: finalChecks.length,
    latencies: Object.fromEntries(
      latencyFields.map((field) => {
        const known = shares.map((share) => share[field]).filter((value): value is number => value !== null);
        return [
          field,
          {
            count: known.length,
            unknownCount: shares.length - known.length,
            minMs: known.length ? Math.min(...known) : null,
            maxMs: known.length ? Math.max(...known) : null,
            meanMs: known.length ? known.reduce((sum, value) => sum + value, 0) / known.length : null,
          },
        ];
      })
    ),
  };
}

export function selectMathProofImpactDependencies(events: readonly MathProofImpactEvent[], source: string) {
  return events.filter(
    (event) =>
      event.kind === 'checked' &&
      event.outcome === 'verified' &&
      event.declarationName &&
      event.declarationSourceHash &&
      mathProofImpactDeclarationHash(source, event.declarationName) === event.declarationSourceHash &&
      event.supportingDeclarations?.every(
        (declaration) => mathProofImpactDeclarationHash(source, declaration.name) === declaration.sourceHash
      )
  );
}

export function mathProofImpactSupportingDeclarations(source: string) {
  return inspectLeanDeclarationRegions(source).map((region) => ({
    name: region.name,
    sourceHash: mathDigest(source.slice(region.startOffset, region.endOffset).trim()),
  }));
}

export type MathProofImpactFinalCheck = Readonly<{
  scope: MathProofImpactScope;
  targetId: string;
  statementHash: string;
  sourceHash: string;
  candidates: readonly string[];
  evidence: readonly MathProofImpactEvent[];
}>;

/** Only immutable original-target identities can request final-dependency attribution. */
export function prepareMathProofImpactFinalCheck(input: {
  source: string;
  theoremName: string;
  statementHash: string;
  expectedSourceDeclarationHash: string;
  env?: NodeJS.ProcessEnv;
}): MathProofImpactFinalCheck | undefined {
  try {
    const env = input.env ?? process.env;
    const scope = readMathProofImpactScope(env);
    if (!scope) return undefined;
    const binding = readMathRunBinding(verifyMathRunInputs(JSON.parse(env[MATH_RUN_INPUTS_ENV]!)));
    const target = binding.problem?.verificationTargets?.find(
      (entry) =>
        entry.theoremName === input.theoremName &&
        entry.statementHash === input.statementHash &&
        entry.expectedSourceDeclarationHash === input.expectedSourceDeclarationHash
    );
    if (!target) return undefined;
    const read = readMathProofImpactEvents(scope.runRoot, scope.runId);
    if (read.availability !== 'available') return undefined;
    const evidence = selectMathProofImpactDependencies(read.events, input.source);
    const candidates = [...new Set(evidence.map((event) => event.declarationName!))].toSorted();
    if (!candidates.length || candidates.length > 32) return undefined;
    return {
      scope,
      targetId: target.targetId,
      statementHash: input.statementHash,
      sourceHash: mathDigest(input.source),
      candidates,
      evidence,
    };
  } catch {
    return undefined;
  }
}

/** Called only after source/commit/statement/kernel checks, never from model output. */
export function recordMathProofImpactFinalCheck(
  context: MathProofImpactFinalCheck,
  result: MathematicsVerifierResult
): void {
  if (
    result.status !== 'kernel_verified' ||
    result.verifier !== 'lean-kernel' ||
    result.proofHash !== context.sourceHash ||
    result.statementHash !== context.statementHash ||
    result.goalsRemaining ||
    result.sorryCount ||
    result.admitCount ||
    result.cleanupError ||
    !result.usedDeclarationDependencies ||
    result.usedDeclarationDependencies.some((name) => !context.candidates.includes(name))
  )
    return;
  const base = {
    runId: context.scope.runId,
    targetId: context.targetId,
    targetCommit: result.targetCommit,
    statementHash: context.statementHash,
    observedAt: Number.isFinite(result.checkedAt) ? result.checkedAt : null,
  };
  recordMathProofImpact(context.scope, {
    ...base,
    kind: 'final_checked',
    assignmentId: 'original-target',
    sourceHash: result.proofHash,
  });
  for (const event of context.evidence) {
    if (!result.usedDeclarationDependencies.includes(event.declarationName!)) continue;
    recordMathProofImpact(context.scope, {
      ...base,
      kind: 'final_dependency',
      assignmentId: event.assignmentId,
      consumerAssignmentId: event.consumerAssignmentId,
      shareId: event.shareId,
      artifactId: event.artifactId,
      blockId: event.blockId,
      sourceHash: event.sourceHash,
      candidateSourceHash: result.proofHash,
      declarationName: event.declarationName,
      declarationSourceHash: event.declarationSourceHash,
    });
  }
}

/** Records retained, checked helper declarations after an actual source replacement, including cold checkout. */
export function recordMathProofImpactAdoption(input: {
  env?: NodeJS.ProcessEnv;
  scope?: MathProofImpactScope;
  consumerAssignmentId: string;
  previousSource: string;
  source: string;
  openGoalsBefore: number;
  openGoalsAfter: number;
}): void {
  try {
    const scope = input.scope ?? readMathProofImpactScope(input.env);
    if (!scope) return;
    const checked = selectMathProofImpactDependencies(
      readMathProofImpactEvents(scope.runRoot, scope.runId).events,
      input.source
    );
    for (const event of checked) {
      if (
        event.consumerAssignmentId !== input.consumerAssignmentId ||
        mathProofImpactDeclarationHash(input.previousSource, event.declarationName!) === event.declarationSourceHash
      )
        continue;
      recordMathProofImpact(scope, {
        kind: 'candidate_adopted',
        runId: scope.runId,
        assignmentId: event.assignmentId,
        consumerAssignmentId: input.consumerAssignmentId,
        shareId: event.shareId,
        artifactId: event.artifactId,
        blockId: event.blockId,
        sourceHash: event.sourceHash,
        candidateSourceHash: mathDigest(input.source),
        declarationName: event.declarationName,
        declarationSourceHash: event.declarationSourceHash,
        openGoalsBefore: input.openGoalsBefore,
        openGoalsAfter: input.openGoalsAfter,
        observedAt: Date.now(),
      });
    }
  } catch {
    /* Optional observations never undo a successfully applied proof transition. */
  }
}
