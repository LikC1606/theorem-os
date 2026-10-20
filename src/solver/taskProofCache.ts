import type { MathematicsVerifierBatchResult } from '../math/verifier';
import { hasDeterministicLeanFailure } from './proofReuse';

export type TaskVerificationArtifact = { projectionCommit: string; verification: MathematicsVerifierBatchResult; cacheable?: boolean };

/** A run owns this cache; it retains verifier artifacts rather than task attribution. */
export class TaskProofCache {
  private readonly entries = new Map<string, { value: TaskVerificationArtifact; bytes: number }>();
  private readonly pending = new Map<string, { signal: AbortSignal; result: Promise<TaskVerificationArtifact> }>();
  private bytes = 0;
  constructor(private readonly maxEntries = 32, private readonly maxBytes = 32 * 1024 * 1024) {}

  async check(key: string, signal: AbortSignal, valid: (artifact: TaskVerificationArtifact) => boolean,
    run: () => Promise<TaskVerificationArtifact>): Promise<TaskVerificationArtifact> {
    signal.throwIfAborted();
    const cached = this.entries.get(key);
    if (cached) {
      this.entries.delete(key); this.bytes -= cached.bytes;
      if (valid(cached.value)) {
        this.entries.set(key, cached); this.bytes += cached.bytes;
        return structuredClone(cached.value);
      }
    }
    const pending = this.pending.get(key);
    if (pending?.signal === signal) return structuredClone(await pending.result);
    const result = run().then(value => {
      signal.throwIfAborted();
      if (value.cacheable !== false && valid(value) &&
          (value.verification.status === 'kernel_verified' || hasDeterministicLeanFailure(value.verification))) {
        const bytes = Buffer.byteLength(JSON.stringify(value));
        if (this.maxEntries > 0 && bytes <= this.maxBytes) {
          const previous = this.entries.get(key);
          if (previous) { this.entries.delete(key); this.bytes -= previous.bytes; }
          while (this.entries.size && (this.entries.size >= this.maxEntries || this.bytes + bytes > this.maxBytes)) {
            const oldest = this.entries.keys().next().value!;
            this.bytes -= this.entries.get(oldest)!.bytes; this.entries.delete(oldest);
          }
          this.entries.set(key, { value: structuredClone(value), bytes }); this.bytes += bytes;
        }
      }
      return value;
    });
    const entry = { signal, result }; this.pending.set(key, entry);
    try { return structuredClone(await result); }
    finally { if (this.pending.get(key) === entry) this.pending.delete(key); }
  }
}
