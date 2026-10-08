import fs from 'node:fs';
import path from 'node:path';

const FIELDS = new Set([
  'teamId',
  'teamRunId',
  'slotId',
  'turnId',
  'assignmentId',
  'receiptId',
  'deliveryId',
  'activeTurnStartedAtMs',
  'pendingDeliveryAtMs',
  'deliveredAt',
  'orphanedPostDeliveryTurn',
  'state',
  'status',
  'reason',
  'method',
  'pathname',
  'durationMs',
  'phase',
  'files',
  'bytes',
  'cacheHit',
  'measurement',
  'elapsedMs',
  'signal',
  'connectionGeneration',
  'invalidationVersion',
  'roleCount',
  'agentLimit',
  'reasoningConcurrency',
  'evaluatorStatus',
  'promptTokens',
  'toolDefinitionTokens',
  'reservedInputTokens',
  'attempt',
  'backoffMs',
  'progressKind',
  'failureCategory',
  'outcome',
  'directive',
  'inputTokens',
  'outputTokens',
  'totalTokens',
  'callCount',
  'cleanupStatus',
  'exitCode',
  'lastCheckedEvidenceAt',
  'noNewCheckedEvidenceMs',
  'lastActivityAt',
  'distinctCheckedEvidenceCount',
  'evidenceCoverage',
  'pendingProofAssignments',
  'workerCommitCount',
  'lastWorkerCommitAt',
  'originalObligationsRemaining',
]);

/** Best-effort telemetry is never part of the durable business transaction. */
export function createMathDiagnostics(
  file: string,
  options: Readonly<{
    maxBytes?: number;
    now?: () => number;
  }> = {}
): (event: string, details?: Readonly<Record<string, unknown>>) => boolean {
  const maxBytes = options.maxBytes ?? 1024 * 1024;
  if (!Number.isSafeInteger(maxBytes) || maxBytes < 4096) throw new Error('math_diagnostics_invalid_budget');
  let sequence = 0;
  return (event, details = {}) => {
    sequence++;
    try {
      if (!/^[a-zA-Z0-9_.-]{1,128}$/u.test(event)) return false;
      const safe = Object.fromEntries(
        Object.entries(details).filter(
          ([key, value]) =>
            FIELDS.has(key) &&
            ((typeof value === 'string' && Buffer.byteLength(value) <= 256) ||
              (typeof value === 'number' && Number.isFinite(value)) ||
              typeof value === 'boolean')
        )
      );
      const line = `${JSON.stringify({ sequence, event, observedAt: new Date(options.now?.() ?? Date.now()).toISOString(), ...safe })}\n`;
      if (Buffer.byteLength(line) > 4096) return false;
      const directory = path.dirname(file);
      fs.mkdirSync(directory, { recursive: true });
      if (fs.realpathSync(directory) !== directory) return false;
      const fd = fs.openSync(
        file,
        fs.constants.O_CREAT |
          fs.constants.O_APPEND |
          fs.constants.O_WRONLY |
          fs.constants.O_NOFOLLOW |
          fs.constants.O_NONBLOCK,
        0o600
      );
      let rotate = false;
      try {
        const stat = fs.fstatSync(fd);
        if (!stat.isFile() || stat.nlink !== 1 || (stat.mode & 0o777) !== 0o600) return false;
        rotate = stat.size + Buffer.byteLength(line) > maxBytes;
        if (!rotate) fs.writeSync(fd, line, undefined, 'utf8');
      } finally {
        fs.closeSync(fd);
      }
      if (rotate) {
        // Keep prior segments so long-running research does not erase its timeline.
        fs.renameSync(file, `${file}.${Date.now()}.${process.pid}.${sequence}.previous`);
        fs.writeFileSync(file, line, { flag: 'wx', mode: 0o600 });
      }
      return true;
    } catch {
      return false;
    }
  };
}

export type MathTimingPhase = 'transport' | 'final_evaluator';

/** Monotonic tool wall time includes nested Lean work; it is not model reasoning time. */
export function createMathToolTiming(now: () => number = () => performance.now()) {
  const started = now();
  return () => ({
    toolWallMs: Math.max(0, now() - started),
    measurement: 'tool_wall_including_lean' as const,
  });
}

/**
 * Measures host operations and sampled slot occupancy separately. Concurrent
 * slot milliseconds overlap and must never be summed into run wall time.
 * Missing provider/compile spans remain unknown rather than inferred from idle time.
 */
export function createMathTimingDiagnostics(
  emit: ReturnType<typeof createMathDiagnostics>,
  now: () => number = () => performance.now()
) {
  const phases: Record<MathTimingPhase, { durationMs: number; count: number; failures: number }> = {
    transport: { durationMs: 0, count: 0, failures: 0 },
    final_evaluator: { durationMs: 0, count: 0, failures: 0 },
  };
  const slotMs: Record<string, number> = {};
  let previous: { at: number; slots: Map<string, string> } | undefined;
  let gaps = 0;
  return {
    async measure<T>(phase: MathTimingPhase, operation: () => Promise<T>): Promise<T> {
      const start = now();
      let outcome = 'completed';
      try {
        return await operation();
      } catch (error) {
        outcome = 'threw';
        phases[phase].failures++;
        throw error;
      } finally {
        const durationMs = Math.max(0, now() - start);
        phases[phase].durationMs += durationMs;
        phases[phase].count++;
        emit('operation_timing', { phase, durationMs, outcome });
      }
    },
    invalidate() {
      previous = undefined;
      gaps++;
    },
    observeSlots(value: unknown) {
      if (!Array.isArray(value)) {
        this.invalidate();
        return;
      }
      const at = now();
      const slots = new Map<string, string>();
      for (const item of value) {
        if (!item || typeof item !== 'object') continue;
        const { slot_id: id, state } = item as Record<string, unknown>;
        if (
          typeof id !== 'string' ||
          !id ||
          typeof state !== 'string' ||
          !['idle', 'queued', 'starting', 'running', 'paused', 'blocked'].includes(state)
        )
          continue;
        slots.set(id, state);
      }
      if (previous) {
        const elapsed = at - previous.at;
        // Long observation gaps are unknown, never a fabricated model/queue stall.
        if (elapsed >= 0 && elapsed <= 120_000) {
          for (const [id, state] of previous.slots) {
            if (!slots.has(id)) continue;
            slotMs[state] = (slotMs[state] ?? 0) + elapsed;
            emit('slot_timing_sample', {
              slotId: id,
              state,
              durationMs: elapsed,
              measurement: 'sampled_slot_occupancy',
            });
          }
        } else {
          gaps++;
        }
      }
      previous = { at, slots };
    },
    snapshot() {
      return {
        phases: Object.fromEntries(Object.entries(phases).map(([phase, value]) => [phase, { ...value }])),
        sampledSlotMs: { ...slotMs },
        observationGaps: gaps,
        modelReasoningMs: null as number | null,
        leanCompileMs: null as number | null,
        semantics:
          'host phases overlap; slot occupancy is sampled and overlaps across slots; model and Lean durations require their own spans',
      };
    },
  };
}
