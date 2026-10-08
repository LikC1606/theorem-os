import path from 'node:path';
import fs from 'node:fs';
import { randomUUID } from 'node:crypto';
import { applyPatch, parsePatch } from 'diff';
import type { MathSourceArtifact, RuntimeMathAssignment } from "../common/types/team/mathRuntimeContracts";
import { mathDigest } from "./mathRuntimeIo";
import { assertMathCanonicalPath, isMathPathWithin } from "./mathRunBinding";
import { mathSourceArtifactSchema } from "./mathPublicWire";

export type { MathSourceArtifact } from "../common/types/team/mathRuntimeContracts";

export type MathAtomicWriteResult = Readonly<{
  target: string;
  status: 'replaced_durable' | 'replaced_uncertain';
}>;

export class MathAtomicWriteError extends Error {
  readonly status = 'not_replaced' as const;
  readonly target: string;
  readonly cause: unknown;

  constructor(target: string, cause: unknown) {
    super(cause instanceof Error ? cause.message : 'math_source_artifact_write_failed');
    this.name = 'MathAtomicWriteError';
    this.target = target;
    this.cause = cause;
  }
}

/**
 * The rename is the visibility commit point. A directory fsync failure leaves
 * the new bytes visible, but does not prove their durability.
 */
export function writeMathTextAtomicallyWithStatus(
  target: string,
  content: string,
  options: Readonly<{ beforeRename?: () => void }> = {}
): MathAtomicWriteResult {
  const temporary = path.join(path.dirname(target), `.math-source-${randomUUID()}.tmp`);
  let created = false;
  let replaced = false;
  try {
    const fd = fs.openSync(temporary, 'wx', 0o600);
    created = true;
    try {
      fs.writeFileSync(fd, content, 'utf8');
      fs.fsyncSync(fd);
    } finally {
      fs.closeSync(fd);
    }
    assertMathCanonicalPath(target);
    options.beforeRename?.();
    assertMathCanonicalPath(target);
    fs.renameSync(temporary, target);
    created = false;
    replaced = true;
    try {
      const directory = fs.openSync(path.dirname(target), 'r');
      try {
        fs.fsyncSync(directory);
      } finally {
        fs.closeSync(directory);
      }
    } catch {
      return Object.freeze({ target, status: 'replaced_uncertain' });
    }
    return Object.freeze({ target, status: 'replaced_durable' });
  } catch (error) {
    if (!replaced) throw new MathAtomicWriteError(target, error);
    throw error;
  } finally {
    if (created) fs.rmSync(temporary, { force: true });
  }
}

function normalizePayload(value: unknown): MathSourceArtifact {
  const parsed = mathSourceArtifactSchema.safeParse(value);
  if (!parsed.success) {
    const field = parsed.error.issues[0]?.path[0];
    const reason =
      field === 'pathRelative'
        ? 'path'
        : field === 'mode'
          ? 'mode'
          : field === 'content'
            ? 'content'
            : field === 'contentSha256'
              ? 'hash'
              : field === 'resultContentSha256'
                ? 'result_hash'
                : field
                  ? 'identity'
                  : 'invalid';
    throw new Error(`math_source_artifact_${reason}`);
  }
  const item = parsed.data;
  const contentSha256 = mathDigest(item.content);
  if (item.contentSha256 !== contentSha256) throw new Error('math_source_artifact_hash');
  return Object.freeze({
    schema: item.schema,
    assignmentId: item.assignmentId,
    deliveryId: item.deliveryId,
    baseCommit: item.baseCommit,
    pathRelative: item.pathRelative,
    mode: item.mode,
    content: item.content,
    contentSha256,
    ...(item.resultContentSha256 ? { resultContentSha256: item.resultContentSha256 } : {}),
    verificationTargetId: item.verificationTargetId,
    theoremName: item.theoremName,
    statementHash: item.statementHash,
    ...(item.leanStatementHash ? { leanStatementHash: item.leanStatementHash } : {}),
    expectedSourceDeclarationHash: item.expectedSourceDeclarationHash,
    ...(item.claim ? { claim: item.claim } : {}),
  });
}

const normalizePatchPath = (value?: string): string | undefined => {
  if (!value || value === '/dev/null') return value;
  return value.replace(/^[ab][\\/]/u, '');
};

function parseSingleFilePatch(content: string, pathRelative: string): ReturnType<typeof parsePatch>[number] {
  let patches: ReturnType<typeof parsePatch>;
  try {
    patches = parsePatch(content);
  } catch {
    throw new Error('math_source_artifact_patch_invalid');
  }
  if (patches.length !== 1 || patches[0]!.hunks.length === 0) {
    throw new Error('math_source_artifact_patch_invalid');
  }
  const patch = patches[0]!;
  const oldPath = normalizePatchPath(patch.oldFileName);
  const newPath = normalizePatchPath(patch.newFileName);
  if (oldPath !== pathRelative || newPath !== pathRelative) {
    throw new Error('math_source_artifact_patch_path');
  }
  return patch;
}

export function applyMathSourceArtifactToText(artifact: MathSourceArtifact, current: string): string {
  const validated = normalizePayload(artifact);
  if (validated.mode === 'file') return validated.content;
  const patch = parseSingleFilePatch(validated.content, validated.pathRelative);
  const result = applyPatch(current, patch, { fuzzFactor: 0 });
  if (result === false) throw new Error('math_source_artifact_patch_failed');
  if (mathDigest(result) !== validated.resultContentSha256) throw new Error('math_source_artifact_result_hash');
  return result;
}

export function mathSourceArtifactOutputSha256(artifact: MathSourceArtifact): string {
  if (artifact.mode === 'patch') {
    if (!artifact.resultContentSha256) throw new Error('math_source_artifact_result_hash');
    return artifact.resultContentSha256;
  }
  return artifact.contentSha256;
}

export function writeMathTextAtomically(target: string, content: string): void {
  // Keep the historical throwing API for callers that do not need the
  // durability distinction; staging uses the status-returning variant.
  const result = writeMathTextAtomicallyWithStatus(target, content);
  if (result.status === 'replaced_uncertain') {
    const error = new Error('math_source_artifact_durability_uncertain');
    error.name = 'MathAtomicWriteUncertainError';
    throw error;
  }
}

function resolveTarget(root: string, relative: string): string {
  if (typeof root !== 'string' || root === path.parse(root).root) throw new Error('math_source_artifact_path');
  assertMathCanonicalPath(root);
  if (fs.existsSync(root) && !fs.lstatSync(root).isDirectory()) throw new Error('math_source_artifact_path');
  const target = path.resolve(root, relative);
  if (target === root || !isMathPathWithin(root, target)) throw new Error('math_source_artifact_path');
  // Check the full target before mkdir: existing parents may redirect outside the draft.
  assertMathCanonicalPath(target);
  if (fs.existsSync(target) && !fs.lstatSync(target).isFile()) throw new Error('math_source_artifact_path');
  return target;
}

export function normalizeMathSourceArtifact(
  value: unknown,
  expected: Readonly<{
    assignmentId: string;
    deliveryId: string;
    baseCommit: string;
    sourceRoot: string;
    verificationTargets?: RuntimeMathAssignment['request']['verificationTargets'];
  }>
): MathSourceArtifact {
  const item = normalizePayload(value);
  if (
    item.assignmentId !== expected.assignmentId ||
    item.deliveryId !== expected.deliveryId ||
    item.baseCommit !== expected.baseCommit
  )
    throw new Error('math_source_artifact_identity');
  const target = expected.verificationTargets?.find((candidate) => candidate.targetId === item.verificationTargetId);
  if (
    !target ||
    target.pathRelative !== item.pathRelative ||
    target.theoremName !== item.theoremName ||
    target.statementHash !== item.statementHash ||
    target.leanStatementHash !== item.leanStatementHash ||
    target.expectedSourceDeclarationHash !== item.expectedSourceDeclarationHash ||
    (target.claim ?? 'statement') !== (item.claim ?? 'statement')
  )
    throw new Error('math_source_artifact_verification_target');
  resolveTarget(expected.sourceRoot, item.pathRelative);
  return item;
}

export function writeMathSourceArtifactToDraft(artifact: MathSourceArtifact, draftRoot: string): string {
  const validated = normalizePayload(artifact);
  const target = resolveTarget(draftRoot, validated.pathRelative);
  fs.mkdirSync(path.dirname(target), { recursive: true, mode: 0o700 });
  resolveTarget(draftRoot, validated.pathRelative);
  if (validated.mode === 'patch') {
    if (!fs.existsSync(target) || !fs.lstatSync(target).isFile()) throw new Error('math_source_artifact_patch_target');
    const descriptor = fs.openSync(target, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW);
    let current: string;
    try {
      current = new TextDecoder('utf-8', { fatal: true }).decode(fs.readFileSync(descriptor));
    } finally {
      fs.closeSync(descriptor);
    }
    const result = applyMathSourceArtifactToText(validated, current);
    writeMathTextAtomically(target, result);
  } else {
    writeMathTextAtomically(target, validated.content);
  }
  return target;
}

export function assertMathSourceArtifactBatch(
  artifacts: readonly MathSourceArtifact[] | undefined,
  deliveryIds: readonly string[]
): void {
  if (artifacts === undefined) return;
  if (!Array.isArray(artifacts) || !Array.isArray(deliveryIds) || !deliveryIds.length || !artifacts.length)
    throw new Error('math_source_artifact_batch_invalid');
  const expected = new Set(deliveryIds);
  if (expected.size !== deliveryIds.length) throw new Error('math_source_artifact_batch_identity');
  const seen = new Set<string>();
  const deliveries = new Set<string>();
  for (const rawArtifact of artifacts) {
    const artifact = normalizePayload(rawArtifact);
    if (!expected.has(artifact.deliveryId))
      throw new Error('math_source_artifact_batch_identity');
    const key = `${artifact.deliveryId}\u0000${artifact.pathRelative}\u0000${artifact.verificationTargetId}`;
    if (seen.has(key)) throw new Error('math_source_artifact_batch_identity');
    seen.add(key);
    deliveries.add(artifact.deliveryId);
  }
  if (deliveries.size !== expected.size) throw new Error('math_source_artifact_batch_identity');
}
