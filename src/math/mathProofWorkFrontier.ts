import crypto from 'node:crypto';
import { buildMathDiscoveryCandidates } from "./mathDiscoveryFrontier";
import { hashMathFormalSourceDeclaration, inspectLeanDeclarations } from "./verifier";
import {
  assertCheckedMathProofBlock,
  type buildMathProofBlockCandidates,
  verifyMathProofBlock,
  type CheckedMathProofBlock,
  type MathProofBlockRequest,
} from "./mathProofBlocks";

const digest = (value: unknown) => crypto.createHash('sha256').update(JSON.stringify(value)).digest('hex');
export type MathNamedProofObligation = Readonly<{
  request: MathProofBlockRequest;
  /** Host resolved named declaration, never an arbitrary displayed metavariable goal. */
  targetName: string;
  prepared: boolean;
  goal: Parameters<typeof buildMathProofBlockCandidates>[0];
}>;
export type MathProofConsumerResult = Readonly<{
  status: 'satisfied' | 'open' | 'needs_mathematical_judgment' | 'already_prepared';
  obligationId: string;
  candidateSource?: string;
  checked?: CheckedMathProofBlock;
  attemptedBlockIds: readonly string[];
  reason?: string;
}>;

/** Exact source, artifact, assignment, type and environment identity. No goal-string equality. */
export function mathNamedProofObligationId(obligation: MathNamedProofObligation): string {
  return digest([
    obligation.request.scope,
    obligation.request.projectRoot,
    obligation.request.proofPath,
    obligation.request.source,
    obligation.targetName,
  ]);
}

/** A reconstructible, process-local projection. Persisted booleans are never completion evidence. */
export class MathProofWorkFrontier {
  private readonly blocks = new Map<string, CheckedMathProofBlock>();
  private readonly attempts = new WeakMap<MathNamedProofObligation, Map<string, Promise<MathProofConsumerResult>>>();

  register(block: CheckedMathProofBlock): boolean {
    assertCheckedMathProofBlock(block);
    if (this.blocks.has(block.id)) return false;
    this.blocks.set(block.id, block);
    return true;
  }

  /** Caller has already resolved sharing permission; run/environment alone do not grant access. */
  async consume(
    obligation: MathNamedProofObligation,
    authorizedBlockIds: readonly string[]
  ): Promise<MathProofConsumerResult> {
    obligation.request.signal?.throwIfAborted();
    if (Date.now() >= obligation.request.deadlineAt) throw new Error('Consumer verification deadline exceeded.');
    const obligationId = mathNamedProofObligationId(obligation);
    const base = { obligationId, attemptedBlockIds: [] as string[] };
    if (obligation.prepared)
      return {
        ...base,
        status: 'already_prepared',
        reason: 'Prepared WAL and active assignments retain their normal lifecycle.',
      };
    const request = obligation.request;
    if (
      request.theoremName !== obligation.targetName ||
      request.source !== obligation.goal.source ||
      inspectLeanDeclarations(request.source).filter((item) => item.name === obligation.targetName).length !== 1
    )
      return {
        ...base,
        status: 'needs_mathematical_judgment',
        reason:
          'Only a uniquely located full named declaration can be projected; arbitrary local goals remain coupled.',
      };
    const blocks = [...new Set(authorizedBlockIds)].flatMap((id) => {
      const block = this.blocks.get(id);
      return block &&
        block.scope.runId === request.scope.runId &&
        block.scope.environmentId === request.scope.environmentId
        ? [block]
        : [];
    });
    const key = digest([obligationId, request.deadlineAt, blocks.map((block) => block.id).toSorted()]);
    // Different calls own different cancellation/deadline and environment resources.
    // Only the identical immutable obligation object may share an in-flight check.
    const pending = this.attempts.get(obligation) ?? new Map<string, Promise<MathProofConsumerResult>>();
    this.attempts.set(obligation, pending);
    const previous = pending.get(key);
    if (previous) return previous;
    const attempt = this.tryConsumer(obligation, blocks);
    pending.set(key, attempt);
    // Coalesce only overlapping work. Without a protected immutable base environment,
    // a settled caller-provided environment identity cannot authorize reuse forever.
    const release = () => {
      if (pending.get(key) === attempt) pending.delete(key);
    };
    void attempt.then(release, release);
    return attempt;
  }

  private async tryConsumer(
    obligation: MathNamedProofObligation,
    blocks: readonly CheckedMathProofBlock[]
  ): Promise<MathProofConsumerResult> {
    const request = obligation.request;
    const obligationId = mathNamedProofObligationId(obligation);
    const originalHeader = hashMathFormalSourceDeclaration(request.source, obligation.targetName);
    const attemptedBlockIds: string[] = [];
    const candidates = buildMathDiscoveryCandidates(obligation.goal, blocks);
    if (candidates.length) attemptedBlockIds.push(...blocks.map((block) => block.id));
    for (const candidate of candidates) {
      if (hashMathFormalSourceDeclaration(candidate.source, obligation.targetName) !== originalHeader)
        throw new Error('Consumer declaration changed during block adaptation.');
      const checked = await verifyMathProofBlock({ ...request, source: candidate.source });
      if (checked.block)
        return {
          status: 'satisfied',
          obligationId,
          candidateSource: candidate.source,
          checked: checked.block,
          attemptedBlockIds,
        };
      if (checked.verification?.status === 'blocked' || checked.verification?.status === 'unavailable')
        throw new Error(checked.reason ?? 'Consumer verification environment unavailable.');
    }
    return {
      status: 'open',
      obligationId,
      attemptedBlockIds,
      reason: 'No complete consumer instance was verified; conditional premises remain open.',
    };
  }
}
