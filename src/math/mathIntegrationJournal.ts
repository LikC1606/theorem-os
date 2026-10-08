import fs from 'node:fs';
import path from 'node:path';
import { z } from 'zod';
import { assertMathCanonicalPath } from "./mathRunBinding";
import {
  canonicalMathJson,
  mathDigest,
  readMathJson,
  withMathRuntimeLease,
  writeMathJsonDurable,
} from "./mathRuntimeIo";

const ID = /^[A-Za-z0-9_-]{1,128}$/u;
const DIGEST = /^[a-f0-9]{64}$/u;
const COMMIT = /^[a-f0-9]{40}(?:[a-f0-9]{24})?$/u;
const id = z.string().regex(ID);
const digest = z.string().regex(DIGEST);
const commit = z.string().regex(COMMIT);
const journalSchema = z
  .object({
    schema: z.literal('deepscientist.math.integration-effect.v1'),
    effectId: digest,
    assignmentId: id,
    branch: z.string().min(1).max(512),
    deliveredHead: commit,
    expectedBase: commit,
    payloadHash: digest,
    state: z.enum(['prepared', 'effect_observed', 'committed']),
    mergedCommit: commit.optional(),
    updatedAt: z.string().datetime(),
  })
  .strict();

export type MathIntegrationEffect = Readonly<z.infer<typeof journalSchema>>;

/**
 * Durable side-effect identity for Git integration. This is deliberately
 * separate from the assignment WAL: the assignment records ownership, while
 * this journal records whether the external merge was observed.
 */
export class MathIntegrationJournal {
  private readonly directory: string;

  constructor(
    private readonly options: Readonly<{
      runRoot: string;
      flockExecutable: string;
      /** Resolve the canonical project HEAD before replaying an observed merge. */
      resolveCanonicalHead: () => string;
      /** Prefer ancestry validation so a later merge does not invalidate an earlier effect. */
      isCanonicalHeadAtOrAfter?: (mergedCommit: string) => boolean;
    }>
  ) {
    assertMathCanonicalPath(options.runRoot);
    if (!ID.test(path.basename(options.runRoot)) || path.basename(path.dirname(options.runRoot)) !== 'runs')
      throw new Error('math_integration_journal_integrity');
    this.directory = path.join(options.runRoot, 'integrations');
    fs.mkdirSync(this.directory, { recursive: true, mode: 0o700 });
    assertMathCanonicalPath(this.directory);
    if ((fs.statSync(this.directory).mode & 0o777) !== 0o700) throw new Error('math_integration_journal_integrity');
  }

  private file(effectId: string): string {
    if (!DIGEST.test(effectId)) throw new Error('math_integration_effect_identity');
    return path.join(this.directory, `${effectId}.json`);
  }

  private read(effectId: string): MathIntegrationEffect | undefined {
    const file = this.file(effectId);
    try {
      fs.lstatSync(file);
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code === 'ENOENT') return undefined;
      throw error;
    }
    const parsed = journalSchema.safeParse(readMathJson(file));
    if (!parsed.success || parsed.data.effectId !== effectId) throw new Error('math_integration_journal_integrity');
    return parsed.data as MathIntegrationEffect;
  }

  async prepare(
    input: Readonly<{
      assignmentId: string;
      branch: string;
      deliveredHead: string;
      expectedBase: string;
    }>
  ): Promise<Readonly<{ effectId: string; replay: boolean; observed: boolean; mergedCommit?: string }>> {
    const payload = {
      assignmentId: input.assignmentId,
      branch: input.branch,
      deliveredHead: input.deliveredHead,
      expectedBase: input.expectedBase,
    };
    const payloadHash = mathDigest(canonicalMathJson(payload));
    // One assignment owns one merge effect. A changed delivery under that
    // identity is a conflict and must never create a second merge record.
    const effectId = mathDigest(canonicalMathJson({ assignmentId: input.assignmentId, kind: 'git-merge' }));
    for (const value of [input.assignmentId, input.branch])
      if (!value || value.length > 512) throw new Error('math_integration_effect_identity');
    if (!COMMIT.test(input.deliveredHead) || !COMMIT.test(input.expectedBase))
      throw new Error('math_integration_effect_identity');
    return withMathRuntimeLease(
      { lockPath: path.join(this.options.runRoot, 'integration.lock'), flockExecutable: this.options.flockExecutable },
      async (lease) => {
        const existing = this.read(effectId);
        if (existing) {
          if (
            existing.payloadHash !== payloadHash ||
            existing.assignmentId !== input.assignmentId ||
            existing.branch !== input.branch ||
            existing.deliveredHead !== input.deliveredHead ||
            existing.expectedBase !== input.expectedBase
          )
            throw new Error('math_integration_effect_conflict');
          if (existing.state !== 'prepared' && existing.mergedCommit) {
            try {
              if (this.options.isCanonicalHeadAtOrAfter) {
                if (!this.options.isCanonicalHeadAtOrAfter(existing.mergedCommit))
                  throw new Error('math_integration_effect_replay_mismatch');
              } else if (this.options.resolveCanonicalHead().toLowerCase() !== existing.mergedCommit.toLowerCase()) {
                throw new Error('math_integration_effect_replay_mismatch');
              }
            } catch (error) {
              if (error instanceof Error && error.message === 'math_integration_effect_replay_mismatch') throw error;
              throw new Error('math_integration_effect_head_unavailable');
            }
          }
          return {
            effectId,
            replay: true,
            observed: existing.state !== 'prepared',
            ...(existing.mergedCommit ? { mergedCommit: existing.mergedCommit } : {}),
          };
        }
        lease.assertHeld();
        writeMathJsonDurable(this.file(effectId), {
          schema: 'deepscientist.math.integration-effect.v1',
          effectId,
          ...payload,
          payloadHash,
          state: 'prepared',
          updatedAt: new Date().toISOString(),
        });
        return { effectId, replay: false, observed: false };
      }
    );
  }

  async observe(effectId: string, mergedCommit: string): Promise<void> {
    if (!COMMIT.test(mergedCommit)) throw new Error('math_integration_effect_identity');
    await withMathRuntimeLease(
      { lockPath: path.join(this.options.runRoot, 'integration.lock'), flockExecutable: this.options.flockExecutable },
      async (lease) => {
        const existing = this.read(effectId);
        if (!existing) throw new Error('math_integration_effect_missing');
        if (existing.state === 'committed') {
          if (existing.mergedCommit !== mergedCommit) throw new Error('math_integration_effect_conflict');
          return;
        }
        lease.assertHeld();
        writeMathJsonDurable(this.file(effectId), {
          ...existing,
          state: 'effect_observed',
          mergedCommit,
          updatedAt: new Date().toISOString(),
        });
      }
    );
  }

  async commit(effectId: string, mergedCommit: string): Promise<void> {
    await withMathRuntimeLease(
      { lockPath: path.join(this.options.runRoot, 'integration.lock'), flockExecutable: this.options.flockExecutable },
      async (lease) => {
        const existing = this.read(effectId);
        if (!existing || existing.state === 'prepared' || existing.mergedCommit !== mergedCommit)
          throw new Error('math_integration_effect_integrity');
        if (existing.state === 'committed') return;
        lease.assertHeld();
        writeMathJsonDurable(this.file(effectId), {
          ...existing,
          state: 'committed',
          updatedAt: new Date().toISOString(),
        });
      }
    );
  }
}
