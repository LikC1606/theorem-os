import crypto from 'node:crypto';

type VerificationQueueEvent = 'verification_queue_waiting' | 'verification_queue_acquired' | 'verification_queue_finished';

/** Serialize complete verification operations; their execution may itself wait for a Lean lock. */
export function createSolverVerificationQueue(input: {
  signal?: AbortSignal;
  emit: (event: VerificationQueueEvent, details: Record<string, unknown>) => void;
  context?: Readonly<Record<string, unknown>>;
}) {
  let tail = Promise.resolve();
  let pending = 0;
  return async <T>(check: () => Promise<T>, context?: Readonly<Record<string, unknown>>): Promise<T> => {
    const previous = tail;
    let release!: () => void;
    tail = new Promise<void>(resolve => { release = resolve; });
    const queuedAt = performance.now();
    const details = { ...input.context, ...context, id: crypto.randomUUID(), queued: pending > 0,
      queueDepth: pending++, queuedAt: Date.now() };
    let acquiredAt: number | undefined;
    let status: 'completed' | 'failed' | 'aborted' = 'failed';
    try {
      input.emit('verification_queue_waiting', details);
      await previous;
      input.signal?.throwIfAborted();
      acquiredAt = performance.now();
      input.emit('verification_queue_acquired', { ...details, waitMs: Math.max(0, Math.round(acquiredAt - queuedAt)) });
      const result = await check();
      status = 'completed';
      return result;
    } catch (error) {
      if (input.signal?.aborted) status = 'aborted';
      throw error;
    } finally {
      // Even a failed observer must not let a successor overtake the current operation.
      await previous;
      const durationMs = Math.max(0, Math.round(performance.now() - queuedAt));
      const waitMs = acquiredAt === undefined ? durationMs : Math.min(durationMs, Math.max(0, Math.round(acquiredAt - queuedAt)));
      pending--;
      try {
        input.emit('verification_queue_finished', { ...details, status, acquired: acquiredAt !== undefined, waitMs, durationMs,
          ...(acquiredAt !== undefined ? { executionMs: durationMs - waitMs } : {}) });
      } finally { release(); }
    }
  };
}
