import fs from 'node:fs';
import path from 'node:path';
import { isMathRelativePath, normalizeMathDelivery, normalizeMathLiteDeliveryIntent } from "./mathPublicWire";
import { mathDigest, canonicalMathJson, readMathJson, writeMathJsonDurable } from "./mathRuntimeIo";
import type {
  MathFormalVerificationTarget,
  MathSourceArtifact,
  MathWorkerDelivery,
} from "../common/types/team/mathRuntimeContracts";

export const MATH_DELIVERY_ENVELOPE_SCHEMA = 'deepscientist.math.delivery.envelope.v2' as const;

export class MathWorkerDeliveryAdapterError extends Error {
  constructor(readonly code: 'invalid' | 'identity_mismatch') {
    super(`math_delivery_${code}`);
    this.name = 'MathWorkerDeliveryAdapterError';
  }
}

export type MathWorkerDeliveryEnvelope = Readonly<{
  schema: typeof MATH_DELIVERY_ENVELOPE_SCHEMA;
  deliveryId: string;
  assignmentId: string;
  targetSlotId: string;
  payloadHash: string;
  delivery: MathWorkerDelivery;
}>;

export type MathLiteFrozenFile = Readonly<{
  pathRelative: string;
  ref: string;
  text: string;
  sha256: string;
}>;

type MathLiteCapturedFile = Readonly<{
  pathRelative: string;
  sourceFile: string;
  text: string;
  sha256: string;
  identity: Readonly<{
    dev: bigint;
    ino: bigint;
    size: bigint;
    mtimeNs: bigint;
    ctimeNs: bigint;
  }>;
}>;

export type MathLiteDeliveryPreparation = Readonly<{
  delivery: MathWorkerDelivery;
  sourceArtifacts: readonly MathSourceArtifact[];
  frozenFiles: readonly MathLiteFrozenFile[];
}>;

export type MathLiteSealedFile = Readonly<{
  pathRelative: string;
  ref: string;
  sha256: string;
  bytes: number;
}>;

export type MathLiteSealedSourceArtifact = Readonly<Omit<MathSourceArtifact, 'content'>>;

export type MathLiteSealedSet = Readonly<{
  schema: 'deepscientist.math.lite-sealed-set.v1';
  runId: string;
  deliveryId: string;
  assignmentId: string;
  targetSlotId: string;
  intentHash: string;
  delivery: MathWorkerDelivery;
  files: readonly MathLiteSealedFile[];
  sourceArtifacts: readonly MathLiteSealedSourceArtifact[];
}>;

function mathLiteFileIdentity(stat: fs.BigIntStats): MathLiteCapturedFile['identity'] {
  return Object.freeze({
    dev: stat.dev,
    ino: stat.ino,
    size: stat.size,
    mtimeNs: stat.mtimeNs,
    ctimeNs: stat.ctimeNs,
  });
}

function mathLiteFileIdentityMatches(stat: fs.BigIntStats, identity: MathLiteCapturedFile['identity']): boolean {
  return (
    stat.isFile() &&
    stat.nlink === BigInt(1) &&
    stat.dev === identity.dev &&
    stat.ino === identity.ino &&
    stat.size === identity.size &&
    stat.mtimeNs === identity.mtimeNs &&
    stat.ctimeNs === identity.ctimeNs
  );
}

function assertMathLiteCapturedFilesCurrent(captured: readonly MathLiteCapturedFile[]): void {
  for (const file of captured) {
    let current: fs.BigIntStats;
    try {
      current = fs.lstatSync(file.sourceFile, { bigint: true });
    } catch (error) {
      throw new Error('math_lite_delivery_source_changed', { cause: error });
    }
    if (!mathLiteFileIdentityMatches(current, file.identity)) throw new Error('math_lite_delivery_source_changed');
  }
}

/** Capture the complete authorized set before publishing any member, then recheck it before returning. */
export async function freezeMathLiteDeliveryFileSet(
  input: Readonly<{
    sourceRoot: string;
    pathRelatives: readonly string[];
    assertHeld?: () => void;
    publish: (file: Readonly<Omit<MathLiteCapturedFile, 'sourceFile' | 'identity'>>) => Promise<string>;
  }>
): Promise<readonly MathLiteFrozenFile[]> {
  const sourceRoot = path.resolve(input.sourceRoot);
  if (fs.realpathSync(sourceRoot) !== sourceRoot || !fs.lstatSync(sourceRoot).isDirectory()) {
    throw new Error('math_lite_delivery_source_root_integrity');
  }
  const captured: MathLiteCapturedFile[] = [];
  for (const pathRelative of input.pathRelatives) {
    input.assertHeld?.();
    if (!isMathRelativePath(pathRelative)) throw new Error('math_lite_delivery_file_unauthorized');
    const sourceFile = path.resolve(sourceRoot, pathRelative);
    const relative = path.relative(sourceRoot, sourceFile);
    if (!relative || relative.startsWith(`..${path.sep}`) || relative === '..' || path.isAbsolute(relative)) {
      throw new Error('math_lite_delivery_file_unauthorized');
    }
    let realSource: string;
    try {
      realSource = fs.realpathSync(sourceFile);
    } catch (error) {
      throw new Error('math_lite_delivery_file_missing', { cause: error });
    }
    if (realSource !== sourceFile) throw new Error('math_lite_delivery_file_invalid');
    const descriptor = fs.openSync(
      sourceFile,
      fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK
    );
    try {
      const before = fs.fstatSync(descriptor, { bigint: true });
      if (!before.isFile() || before.nlink !== BigInt(1) || before.size > BigInt(5 * 1024 * 1024)) {
        throw new Error('math_lite_delivery_file_invalid');
      }
      const rawBytes = fs.readFileSync(descriptor);
      const after = fs.fstatSync(descriptor, { bigint: true });
      const current = fs.lstatSync(sourceFile, { bigint: true });
      const identity = mathLiteFileIdentity(before);
      if (!mathLiteFileIdentityMatches(after, identity) || !mathLiteFileIdentityMatches(current, identity)) {
        throw new Error('math_lite_delivery_source_changed');
      }
      let text: string;
      try {
        text = new TextDecoder('utf-8', { fatal: true }).decode(rawBytes);
      } catch {
        throw new Error('math_lite_delivery_file_encoding');
      }
      if (!Buffer.from(text, 'utf8').equals(rawBytes)) throw new Error('math_lite_delivery_file_encoding');
      captured.push(
        Object.freeze({
          pathRelative,
          sourceFile,
          text,
          sha256: mathDigest(rawBytes),
          identity,
        })
      );
    } finally {
      fs.closeSync(descriptor);
    }
  }
  input.assertHeld?.();
  assertMathLiteCapturedFilesCurrent(captured);
  const frozen: MathLiteFrozenFile[] = [];
  for (const file of captured) {
    input.assertHeld?.();
    // eslint-disable-next-line no-await-in-loop -- publications follow one already-captured immutable batch.
    const ref = await input.publish({
      pathRelative: file.pathRelative,
      text: file.text,
      sha256: file.sha256,
    });
    frozen.push(Object.freeze({ pathRelative: file.pathRelative, ref, text: file.text, sha256: file.sha256 }));
  }
  input.assertHeld?.();
  assertMathLiteCapturedFilesCurrent(captured);
  return Object.freeze(frozen);
}

export function mathLiteDeliveryArtifactId(deliveryId: string, pathRelative: string, contentSha256?: string): string {
  return `delivery-${mathDigest(canonicalMathJson({ deliveryId, pathRelative, ...(contentSha256 ? { contentSha256 } : {}) })).slice(0, 64)}`;
}

export function mathLiteSealedSetPath(runRoot: string, deliveryId: string): string {
  if (!/^[A-Za-z0-9_:-]{1,512}$/u.test(deliveryId)) throw new Error('math_lite_delivery_identity');
  const directory = path.join(runRoot, 'lite-deliveries');
  fs.mkdirSync(directory, { recursive: true, mode: 0o700 });
  if (fs.realpathSync(directory) !== directory) throw new Error('math_lite_delivery_integrity');
  return path.join(directory, `${deliveryId}.json`);
}

export function readMathLiteSealedSet(runRoot: string, deliveryId: string): MathLiteSealedSet | undefined {
  const file = mathLiteSealedSetPath(runRoot, deliveryId);
  try {
    fs.lstatSync(file);
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code === 'ENOENT') return undefined;
    throw new Error('math_lite_delivery_integrity', { cause: error });
  }
  const value = readMathJson(file) as Partial<MathLiteSealedSet>;
  if (
    value.schema !== 'deepscientist.math.lite-sealed-set.v1' ||
    value.deliveryId !== deliveryId ||
    typeof value.runId !== 'string' ||
    typeof value.assignmentId !== 'string' ||
    typeof value.targetSlotId !== 'string' ||
    !/^[a-f0-9]{64}$/u.test(String(value.intentHash)) ||
    !value.delivery ||
    !Array.isArray(value.files) ||
    !Array.isArray(value.sourceArtifacts)
  )
    throw new Error('math_lite_delivery_integrity');
  for (const fileEntry of value.files) {
    if (
      !fileEntry ||
      typeof fileEntry.pathRelative !== 'string' ||
      path.isAbsolute(fileEntry.pathRelative) ||
      fileEntry.pathRelative.split(/[\\/]/u).includes('..') ||
      fileEntry.pathRelative.includes('\0') ||
      typeof fileEntry.ref !== 'string' ||
      !/^[a-f0-9]{64}$/u.test(fileEntry.sha256) ||
      !Number.isSafeInteger(fileEntry.bytes) ||
      fileEntry.bytes < 0
    )
      throw new Error('math_lite_delivery_integrity');
  }
  if (new Set(value.files.map((entry) => entry.pathRelative)).size !== value.files.length) {
    throw new Error('math_lite_delivery_integrity');
  }
  const fileByPath = new Map(value.files.map((entry) => [entry.pathRelative, entry]));
  const artifactKeys = new Set<string>();
  for (const artifact of value.sourceArtifacts) {
    if (
      !artifact ||
      typeof artifact.assignmentId !== 'string' ||
      artifact.assignmentId !== value.assignmentId ||
      typeof artifact.deliveryId !== 'string' ||
      artifact.deliveryId !== deliveryId ||
      typeof artifact.pathRelative !== 'string' ||
      !fileByPath.has(artifact.pathRelative) ||
      !/^[a-f0-9]{64}$/u.test(artifact.contentSha256) ||
      artifact.contentSha256 !== fileByPath.get(artifact.pathRelative)!.sha256 ||
      typeof artifact.verificationTargetId !== 'string' ||
      typeof artifact.theoremName !== 'string' ||
      !/^[a-f0-9]{64}$/u.test(artifact.statementHash) ||
      (artifact.leanStatementHash !== undefined && !/^[a-f0-9]{64}$/u.test(artifact.leanStatementHash)) ||
      !/^[a-f0-9]{64}$/u.test(artifact.expectedSourceDeclarationHash)
    )
      throw new Error('math_lite_delivery_integrity');
    const key = `${artifact.pathRelative}\u0000${artifact.verificationTargetId}`;
    if (artifactKeys.has(key)) throw new Error('math_lite_delivery_integrity');
    artifactKeys.add(key);
  }
  return Object.freeze({
    ...(value as MathLiteSealedSet),
    files: Object.freeze(value.files.map((entry) => Object.freeze({ ...entry }))),
    sourceArtifacts: Object.freeze(value.sourceArtifacts.map((entry) => Object.freeze({ ...entry }))),
  });
}

export function writeMathLiteSealedSet(runRoot: string, sealed: MathLiteSealedSet): void {
  const file = mathLiteSealedSetPath(runRoot, sealed.deliveryId);
  const existing = readMathLiteSealedSet(runRoot, sealed.deliveryId);
  if (existing) {
    if (canonicalMathJson(existing) !== canonicalMathJson(sealed)) throw new Error('math_lite_delivery_conflict');
    return;
  }
  writeMathJsonDurable(file, sealed, 0o400);
}

type Options = Readonly<{
  expectedDeliveryId?: string;
  expectedAssignmentId?: string;
  expectedTargetSlotId?: string;
}>;

function freeze<T>(value: T): T {
  if (!value || typeof value !== 'object' || Object.isFrozen(value)) return value;
  Object.freeze(value);
  for (const child of Object.values(value)) freeze(child);
  return value;
}

function requireIdentity(value: unknown, delivery = false): string {
  const pattern = delivery ? /^[A-Za-z0-9_:-]{1,512}$/u : /^[A-Za-z0-9_-]{1,128}$/u;
  if (typeof value !== 'string' || !pattern.test(value)) throw new MathWorkerDeliveryAdapterError('invalid');
  return value;
}

/** Convert the small model intent into the existing strict internal delivery. */
export async function prepareMathLiteWorkerDelivery(
  value: unknown,
  input: Readonly<{
    deliveryId: string;
    assignmentId: string;
    baseCommit: string;
    assignmentKind: 'research' | 'formalize';
    verificationTargets?: readonly MathFormalVerificationTarget[];
    preflightFile?: (pathRelative: string) => Promise<void> | void;
    freezeFiles?: (pathRelatives: readonly string[]) => Promise<readonly MathLiteFrozenFile[]>;
    freezeFile?: (pathRelative: string) => Promise<MathLiteFrozenFile>;
  }>
): Promise<MathLiteDeliveryPreparation> {
  const intent = normalizeMathLiteDeliveryIntent(value);
  const targets = input.verificationTargets ?? [];
  const targetsByPath = new Map<string, MathFormalVerificationTarget[]>();
  for (const target of targets) {
    const entries = targetsByPath.get(target.pathRelative) ?? [];
    entries.push(target);
    targetsByPath.set(target.pathRelative, entries);
  }
  const requestedFiles = [...(intent.files ?? [])];
  const targetFiles = requestedFiles.filter((file) => targetsByPath.has(file));
  for (const file of requestedFiles) {
    // A lane may deliver its own Lean-checked auxiliary file. It is published as
    // analysis evidence only (below), never as a source artifact, so it gains no
    // authority over the proof target. The host preflight keeps it inside the
    // solver project and away from the original sources. Run 23e lost eight such
    // deliveries to this check although share accepted them, and run 23 attempt
    // 14 lost the proof owner's DirectStep.lean and TranslationObstruction.lean
    // twice for the same reason.
    const auxiliaryLean = file.endsWith('.lean') && !targetsByPath.has(file);
    if (!targetsByPath.has(file) && file !== 'RESEARCH.md' && !auxiliaryLean)
      throw new Error('math_lite_delivery_file_unauthorized');
  }
  if (
    intent.status === 'completed' &&
    input.assignmentKind === 'formalize' &&
    targetFiles.length !== targetsByPath.size
  ) {
    throw new Error('math_lite_delivery_source_required');
  }
  for (const file of requestedFiles) {
    // Complete the whole no-side-effect validation pass before publishing the first object.
    // eslint-disable-next-line no-await-in-loop
    await input.preflightFile?.(file);
  }
  const evidence: Array<{ kind: 'source' | 'analysis'; ref: string }> = [];
  const sourceArtifacts: MathSourceArtifact[] = [];
  const frozenFiles = !requestedFiles.length
    ? []
    : input.freezeFiles
      ? [...(await input.freezeFiles(requestedFiles))]
      : await (async () => {
          const files: MathLiteFrozenFile[] = [];
          if (!input.freezeFile) throw new Error('math_lite_delivery_freeze_unavailable');
          for (const file of requestedFiles) {
            // eslint-disable-next-line no-await-in-loop -- fallback is retained for existing callers.
            if (!input.freezeFile) throw new Error('math_lite_delivery_freeze_unavailable');
            files.push(await input.freezeFile(file));
          }
          return files;
        })();
  if (frozenFiles.length !== requestedFiles.length) throw new Error('math_lite_delivery_file_identity');
  for (let index = 0; index < requestedFiles.length; index += 1) {
    const file = requestedFiles[index]!;
    const fileTargets = targetsByPath.get(file);
    const frozen = frozenFiles[index]!;
    if (frozen.pathRelative !== file || frozen.sha256 !== mathDigest(frozen.text)) {
      throw new Error('math_lite_delivery_file_identity');
    }
    if (!fileTargets?.length) {
      evidence.push({ kind: 'analysis', ref: frozen.ref });
      continue;
    }
    for (const target of fileTargets) {
      sourceArtifacts.push({
        schema: 'deepscientist.math.source-artifact.v1',
        assignmentId: input.assignmentId,
        deliveryId: input.deliveryId,
        baseCommit: input.baseCommit,
        pathRelative: file,
        mode: 'file',
        content: frozen.text,
        contentSha256: frozen.sha256,
        verificationTargetId: target.targetId,
        theoremName: target.theoremName,
        statementHash: target.statementHash,
        ...(target.leanStatementHash ? { leanStatementHash: target.leanStatementHash } : {}),
        expectedSourceDeclarationHash: target.expectedSourceDeclarationHash,
        ...(target.claim ? { claim: target.claim } : {}),
      });
    }
    evidence.push({ kind: 'source', ref: frozen.ref });
  }
  const delivery: MathWorkerDelivery = Object.freeze({
    status: intent.status,
    summary: intent.summary,
    evidence: Object.freeze(evidence),
    ...(intent.blockers ? { blockers: Object.freeze([...intent.blockers]) } : {}),
  });
  return Object.freeze({
    delivery,
    sourceArtifacts: Object.freeze(sourceArtifacts),
    frozenFiles: Object.freeze(frozenFiles),
  });
}

export function projectMathWorkerDeliveryToEnvelope(
  value: unknown,
  identityInput: Readonly<{ deliveryId: string; assignmentId: string; targetSlotId: string }>,
  options: Options = {}
): MathWorkerDeliveryEnvelope {
  const deliveryId = requireIdentity(identityInput.deliveryId, true);
  const assignmentId = requireIdentity(identityInput.assignmentId);
  const targetSlotId = requireIdentity(identityInput.targetSlotId);
  if (
    (options.expectedDeliveryId !== undefined && options.expectedDeliveryId !== deliveryId) ||
    (options.expectedAssignmentId !== undefined && options.expectedAssignmentId !== assignmentId) ||
    (options.expectedTargetSlotId !== undefined && options.expectedTargetSlotId !== targetSlotId)
  )
    throw new MathWorkerDeliveryAdapterError('identity_mismatch');
  let delivery: MathWorkerDelivery;
  try {
    delivery = normalizeMathDelivery(value);
  } catch {
    throw new MathWorkerDeliveryAdapterError('invalid');
  }
  return freeze({
    schema: MATH_DELIVERY_ENVELOPE_SCHEMA,
    deliveryId,
    assignmentId,
    targetSlotId,
    payloadHash: mathDigest(canonicalMathJson(delivery)),
    delivery,
  });
}
