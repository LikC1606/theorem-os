import fs from 'node:fs';
import { canonicalMathJson, readMathJson, syncMathDirectory, writeMathJsonDurable } from "./mathRuntimeIo";
import path from 'node:path';
import { assertMathCanonicalPath } from "./mathRunBinding";

export type MathCleanupOutcome = Readonly<{
  status: 'pending' | 'retained' | 'stopped' | 'completed' | 'deferred' | 'failed';
  reason: string;
  resourcesRemoved: boolean;
  manifestRetained: boolean;
}>;

export function mathRunExitCode(input: {
  runtimeError?: string;
  limitReached?: string;
  startupOnly: boolean;
  completionSignalValid: boolean;
  evaluatorStatus: unknown;
  cleanup: MathCleanupOutcome;
}): number {
  if (input.runtimeError) return 1;
  if (input.limitReached) return 4;
  if (input.startupOnly) return ['stopped', 'completed'].includes(input.cleanup.status) ? 0 : 3;
  if (!input.completionSignalValid || input.evaluatorStatus !== 'passed') return 2;
  return input.cleanup.status === 'completed' && input.cleanup.resourcesRemoved && !input.cleanup.manifestRetained
    ? 0
    : 3;
}

/** Bounded wall-limit window for integrating an already completed original-target proof. */
export const mathRunCompletedProofGraceMs = (maxRunSeconds: number): number =>
  Math.min(600, Math.ceil(maxRunSeconds / 4)) * 1000;

type ProgressState = {
  schema: 'deepscientist.math.proof-progress.v1';
  runId: string;
  startedAt: number;
  lastEvidenceAt: number | null;
  lastActivityAt: number | null;
  evidenceIds: string[];
  evidenceCoverage: 'complete' | 'bounded';
  activityFingerprint: string | null;
  /** Worker commits beyond their assignment base; retained work, not checked evidence. */
  workerCommitIds?: string[];
  lastWorkerCommitAt?: number | null;
};

/** Observed checked evidence is distinct from file activity and Core heartbeats.
 * This diagnostic cannot certify a theorem or infer a number of remaining goals. */
export function createMathProofProgressMonitor(input: {
  runId: string;
  startedAt: number;
  retained?: unknown;
  now?: () => number;
}) {
  const now = input.now ?? Date.now;
  const validTime = (value: unknown): value is number =>
    typeof value === 'number' && Number.isSafeInteger(value) && value >= 0 && value <= now();
  if (!input.runId || !validTime(input.startedAt)) throw new Error('math_progress_state_invalid');
  let state: ProgressState = {
    schema: 'deepscientist.math.proof-progress.v1',
    runId: input.runId,
    startedAt: input.startedAt,
    lastEvidenceAt: null,
    lastActivityAt: null,
    evidenceIds: [],
    evidenceCoverage: 'complete',
    activityFingerprint: null,
  };
  if (input.retained !== undefined) {
    const previous = input.retained as ProgressState;
    if (
      !previous ||
      previous.schema !== state.schema ||
      previous.runId !== input.runId ||
      previous.startedAt !== input.startedAt ||
      (previous.lastEvidenceAt !== null &&
        (!validTime(previous.lastEvidenceAt) || previous.lastEvidenceAt < input.startedAt)) ||
      (previous.lastActivityAt !== null &&
        (!validTime(previous.lastActivityAt) || previous.lastActivityAt < input.startedAt)) ||
      !Array.isArray(previous.evidenceIds) ||
      previous.evidenceIds.length > 4096 ||
      previous.evidenceIds.some((id) => typeof id !== 'string' || !/^[a-f0-9]{64}$/u.test(id)) ||
      new Set(previous.evidenceIds).size !== previous.evidenceIds.length ||
      !['complete', 'bounded'].includes(previous.evidenceCoverage) ||
      (previous.activityFingerprint !== null &&
        (typeof previous.activityFingerprint !== 'string' || !/^[a-f0-9]{64}$/u.test(previous.activityFingerprint))) ||
      (previous.workerCommitIds !== undefined &&
        (!Array.isArray(previous.workerCommitIds) ||
          previous.workerCommitIds.length > 4096 ||
          previous.workerCommitIds.some((id) => typeof id !== 'string' || !/^[a-f0-9]{40,64}$/u.test(id)) ||
          new Set(previous.workerCommitIds).size !== previous.workerCommitIds.length)) ||
      (previous.lastWorkerCommitAt !== undefined &&
        previous.lastWorkerCommitAt !== null &&
        (!validTime(previous.lastWorkerCommitAt) || previous.lastWorkerCommitAt < input.startedAt))
    )
      throw new Error('math_progress_state_invalid');
    state = { ...previous, evidenceIds: [...previous.evidenceIds] };
  }
  const evidence = new Set(state.evidenceIds);
  const workerCommits = new Set(state.workerCommitIds ?? []);
  let pendingProofAssignments: number | null = null;
  let solverReady = false;
  return {
    observe(observation: {
      checkedEvidenceIds: readonly string[];
      activityFingerprint: string;
      pendingProofAssignments: number;
      solverReady: boolean;
      workerCommitIds?: readonly string[];
    }) {
      const at = now();
      if (
        !/^[a-f0-9]{64}$/u.test(observation.activityFingerprint) ||
        !Number.isSafeInteger(observation.pendingProofAssignments) ||
        observation.pendingProofAssignments < 0 ||
        observation.checkedEvidenceIds.some((id) => !/^[a-f0-9]{64}$/u.test(id)) ||
        observation.workerCommitIds?.some((id) => !/^[a-f0-9]{40,64}$/u.test(id))
      )
        throw new Error('math_progress_observation_invalid');
      for (const id of observation.checkedEvidenceIds) {
        if (evidence.has(id)) continue;
        if (evidence.size >= 4096) {
          state.evidenceCoverage = 'bounded';
          continue;
        }
        evidence.add(id);
        state.lastEvidenceAt = Math.max(state.lastEvidenceAt ?? state.startedAt, at);
      }
      if (state.activityFingerprint !== observation.activityFingerprint) {
        state.activityFingerprint = observation.activityFingerprint;
        state.lastActivityAt = Math.max(state.lastActivityAt ?? state.startedAt, at);
      }
      for (const id of observation.workerCommitIds ?? []) {
        if (workerCommits.has(id) || workerCommits.size >= 4096) continue;
        workerCommits.add(id);
        state.lastWorkerCommitAt = Math.max(state.lastWorkerCommitAt ?? state.startedAt, at);
      }
      if (workerCommits.size) state.workerCommitIds = [...workerCommits];
      pendingProofAssignments = observation.pendingProofAssignments;
      solverReady = observation.solverReady;
      state.evidenceIds = [...evidence];
    },
    state: (): ProgressState => ({
      ...state,
      evidenceIds: [...state.evidenceIds],
      ...(state.workerCommitIds ? { workerCommitIds: [...state.workerCommitIds] } : {}),
    }),
    snapshot() {
      const at = now();
      return {
        elapsedMs: Math.max(0, at - state.startedAt),
        lastCheckedEvidenceAt: state.lastEvidenceAt,
        noNewCheckedEvidenceMs: Math.max(0, at - (state.lastEvidenceAt ?? state.startedAt)),
        lastActivityAt: state.lastActivityAt,
        distinctCheckedEvidenceCount: evidence.size,
        evidenceCoverage: state.evidenceCoverage,
        pendingProofAssignments,
        workerCommitCount: workerCommits.size,
        lastWorkerCommitAt: state.lastWorkerCommitAt ?? null,
        originalObligationsRemaining: solverReady ? 0 : null,
        semantics:
          'host-checked evidence observations; activity and unintegrated Worker commits are not proof progress; unknown goal count is null',
      };
    },
    limitReason(
      limits: { maxRunSeconds?: number; noProgressSeconds?: number },
      quiescent: boolean,
      options: { reviewPendingSince?: number; completedProofPendingSince?: number } = {}
    ) {
      const elapsed = Math.max(0, now() - state.startedAt);
      if (limits.maxRunSeconds !== undefined && elapsed >= limits.maxRunSeconds * 1000) {
        // A completed original-target delivery still needs host integration and
        // the official gate. Run 23 stopped 7.5 minutes after one arrived. Allow
        // one bounded window from that delivery; nothing else extends the wall.
        const graceMs = mathRunCompletedProofGraceMs(limits.maxRunSeconds);
        if (options.completedProofPendingSince === undefined || now() >= options.completedProofPendingSince + graceMs)
          return 'math_run_wall_limit';
      }
      // An unintegrated delivery still awaits the Lead; checked evidence can only
      // arrive through its review. Give that review one no-progress window from
      // the latest delivery before stopping (run 23 stopped on the same poll).
      const reviewPending =
        limits.noProgressSeconds !== undefined &&
        options.reviewPendingSince !== undefined &&
        now() - options.reviewPendingSince < limits.noProgressSeconds * 1000;
      // An explicit no-progress budget is the host's inactivity boundary. It
      // must apply while unrelated Team slots are still running; otherwise a
      // stalled proof owner can keep the run alive indefinitely. Without an
      // explicit budget, preserve the legacy quiescent-only behavior.
      if (
        (quiescent || limits.noProgressSeconds !== undefined) &&
        !reviewPending &&
        state.evidenceCoverage === 'complete' &&
        limits.noProgressSeconds !== undefined &&
        now() - (state.lastEvidenceAt ?? state.startedAt) >= limits.noProgressSeconds * 1000
      )
        return 'math_run_no_progress_limit';
      return undefined;
    },
  };
}

/** The result survives an interrupted cleanup. Readers can see pending, never a fabricated success. */
export async function finalizeMathRunReceipt(input: {
  output: string;
  receipt: Record<string, unknown>;
  pending: MathCleanupOutcome;
  cleanup: () => Promise<MathCleanupOutcome>;
}) {
  const initial = { ...input.receipt, cleanup: input.pending, finalized_at: null as string | null };
  const descriptor = fs.openSync(input.output, 'wx', 0o600);
  try {
    fs.writeFileSync(descriptor, JSON.stringify(initial));
    fs.fsyncSync(descriptor);
  } finally {
    fs.closeSync(descriptor);
  }
  syncMathDirectory(path.dirname(input.output));
  let cleanup: MathCleanupOutcome;
  try {
    cleanup = await input.cleanup();
  } catch {
    cleanup = { status: 'failed', reason: 'cleanup_exception', resourcesRemoved: false, manifestRetained: true };
  }
  // Fail closed if another writer replaced this run's result while cleanup ran.
  const saved = readMathJson(input.output) as Record<string, unknown>;
  if (canonicalMathJson(saved) !== canonicalMathJson(initial)) throw new Error('math_final_receipt_changed');
  const result = { ...input.receipt, cleanup, finalized_at: new Date().toISOString() };
  writeMathJsonDurable(input.output, result);
  return result;
}

/** Explicit cleanup recovery updates only the result bound to this run. */
export function recoverMathRunReceiptCleanup(input: {
  output: string;
  identity: {
    run_id: string;
    team_id: string | null;
    run_inputs_digest: string;
    run_binding_ref: string;
    run_binding_digest: string;
  };
}): void {
  assertMathCanonicalPath(input.output);
  if (!fs.existsSync(input.output)) return;
  const saved = readMathJson(input.output) as Record<string, unknown>;
  if (
    !saved ||
    saved.schema !== 'deepscientist.mathematics.proof-team-run.v2' ||
    Object.entries(input.identity).some(([key, value]) => saved[key] !== value)
  )
    throw new Error('math_cleanup_receipt_identity_mismatch');
  const cleanup: MathCleanupOutcome = {
    status: 'completed',
    reason: 'resources_removed',
    resourcesRemoved: true,
    manifestRetained: false,
  };
  if (canonicalMathJson(saved.cleanup) === canonicalMathJson(cleanup) && typeof saved.finalized_at === 'string') return;
  writeMathJsonDurable(input.output, { ...saved, cleanup, finalized_at: new Date().toISOString() });
}
