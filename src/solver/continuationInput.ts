import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { z } from 'zod';
import { canonicalMathJson, mathDigest, readMathFile, syncMathDirectory } from '../math/mathRuntimeIo';
import { assertMathCanonicalPath } from '../math/paths';
import type { ContextSection } from './contextCompiler';

const maxAttachmentBytes = 16_000_000, maxTotalBytes = 64_000_000, maxManifestBytes = 1_000_000;
const digest = z.string().regex(/^[a-f0-9]{64}$/u);
const provenance = z.object({
  source: z.string().min(1).max(1000).optional(),
  evidence: z.enum(['unverified', 'recorded-not-replayed']).default('unverified'),
  runId: z.string().min(1).max(128).optional(), commit: z.string().regex(/^(?:[a-f0-9]{40}|[a-f0-9]{64})$/u).optional(),
}).strict().default({ evidence: 'unverified' });
const attachment = z.object({
  id: z.string().regex(/^[A-Za-z0-9][A-Za-z0-9_.-]{0,63}$/u),
  kind: z.enum(['proof-source', 'research-notes', 'diagnostics']),
  path: z.string().min(1).max(4096).refine(value => !value.includes('\0')),
  bytes: z.number().int().min(0).max(maxAttachmentBytes), sha256: digest, provenance,
}).strict();
const identity = { taskDigest: digest, problemReceiptDigest: digest };
const inputSchema = z.object({ schema: z.literal('theorem-os.continuation-input.v1'), ...identity,
  attachments: z.array(attachment).min(1).max(32) }).strict();
const snapshotSchema = z.object({ schema: z.literal('theorem-os.continuation-snapshot.v1'), ...identity,
  attachments: z.array(attachment.extend({ contentPath: z.string() }).strict()).min(1).max(32) }).strict();

export type ContinuationIdentity = Readonly<{ taskDigest: string; problemReceiptDigest: string }>;
type ContinuationAttachment = Required<Omit<z.infer<typeof attachment>, 'provenance'>> & {
  provenance: z.infer<typeof provenance> & { evidence: 'unverified' | 'recorded-not-replayed' };
};
type InputManifest = ContinuationIdentity & { schema: 'theorem-os.continuation-input.v1'; attachments: ContinuationAttachment[] };
export type ContinuationManifest = ContinuationIdentity & { schema: 'theorem-os.continuation-snapshot.v1';
  attachments: (ContinuationAttachment & { contentPath: string })[] };
export type ContinuationSnapshot = Readonly<{ file: string; digest: string; manifest: ContinuationManifest }>;
export type ContinuationInput = Readonly<{ digest: string; manifest: ContinuationManifest; contents: ReadonlyMap<string, string> }>;

function validateAttachments(manifest: { attachments: ContinuationAttachment[] }) {
  if (new Set(manifest.attachments.map(item => item.id)).size !== manifest.attachments.length ||
      manifest.attachments.reduce((total, item) => total + item.bytes, 0) > maxTotalBytes)
    throw new Error('math_continuation_attachments_invalid');
  const sizes = new Map<string, number>();
  for (const item of manifest.attachments) {
    if (sizes.has(item.sha256) && sizes.get(item.sha256) !== item.bytes) throw new Error('math_continuation_attachments_invalid');
    sizes.set(item.sha256, item.bytes);
  }
}

function assertIdentity(manifest: ContinuationIdentity, expected?: ContinuationIdentity) {
  if (expected && (manifest.taskDigest !== expected.taskDigest || manifest.problemReceiptDigest !== expected.problemReceiptDigest))
    throw new Error('math_continuation_identity_changed');
}

function readText(file: string, maxBytes: number, frozen = false) {
  assertMathCanonicalPath(file);
  const loaded = readMathFile(file, maxBytes);
  if (frozen && (fs.lstatSync(file).mode & 0o777) !== 0o400) throw new Error('math_continuation_file_not_frozen');
  try {
    return { bytes: loaded.bytes, text: new TextDecoder('utf-8', { fatal: true, ignoreBOM: true }).decode(loaded.bytes) };
  } catch { throw new Error('math_continuation_invalid_utf8'); }
}

function readContent(file: string, item: Pick<ContinuationAttachment, 'bytes' | 'sha256'>, frozen: boolean) {
  const loaded = readText(file, item.bytes, frozen);
  if (loaded.bytes.length !== item.bytes || mathDigest(loaded.bytes) !== item.sha256)
    throw new Error('math_continuation_content_changed');
  return loaded.text;
}

function validateSnapshot(value: unknown): ContinuationManifest {
  const parsed = snapshotSchema.safeParse(value);
  if (!parsed.success) throw new Error('math_continuation_snapshot_invalid');
  const manifest = parsed.data as ContinuationManifest;
  validateAttachments(manifest);
  if (manifest.attachments.some(item => item.contentPath !== `continuation/${item.sha256}.txt`))
    throw new Error('math_continuation_snapshot_invalid');
  return manifest;
}

/** Explicit attachments supplement the unchanged task; historical claims never become proof evidence. */
export function readContinuationInput(file: string, expected: ContinuationIdentity): ContinuationInput {
  const resolved = path.resolve(file), loaded = readText(resolved, maxManifestBytes);
  let value: unknown;
  try { value = JSON.parse(loaded.text); } catch { throw new Error('math_continuation_manifest_invalid'); }
  const parsed = inputSchema.safeParse(value);
  if (!parsed.success) throw new Error('math_continuation_manifest_invalid');
  const manifest = parsed.data as InputManifest;
  assertIdentity(manifest, expected); validateAttachments(manifest);
  const contents = new Map<string, string>();
  for (const item of manifest.attachments)
    contents.set(item.sha256, readContent(path.resolve(path.dirname(resolved), item.path), item, false));
  const snapshot: ContinuationManifest = { ...manifest, schema: 'theorem-os.continuation-snapshot.v1',
    attachments: manifest.attachments.map(item => ({ ...item, contentPath: `continuation/${item.sha256}.txt` })) };
  return { digest: mathDigest(canonicalMathJson(snapshot)), manifest: snapshot, contents };
}

/** Publish complete blobs first and the immutable manifest last; matching interrupted writes are reusable. */
function writeFrozen(file: string, text: string) {
  assertMathCanonicalPath(file);
  if (fs.lstatSync(file, { throwIfNoEntry: false })) {
    if (readText(file, Buffer.byteLength(text), true).text !== text) throw new Error('math_continuation_frozen_file_changed');
    return;
  }
  fs.mkdirSync(path.dirname(file), { recursive: true, mode: 0o700 });
  const temporary = `${file}.${crypto.randomUUID()}.tmp`;
  const descriptor = fs.openSync(temporary, fs.constants.O_WRONLY | fs.constants.O_CREAT | fs.constants.O_EXCL | fs.constants.O_NOFOLLOW, 0o600);
  try {
    fs.writeFileSync(descriptor, text, 'utf8'); fs.fchmodSync(descriptor, 0o400); fs.fsyncSync(descriptor);
  } finally { fs.closeSync(descriptor); }
  fs.renameSync(temporary, file); syncMathDirectory(path.dirname(file));
}

export function freezeContinuationInput(input: ContinuationInput, runtimeDirectory: string): ContinuationSnapshot {
  const manifest = validateSnapshot(input.manifest), text = canonicalMathJson(manifest);
  if (!digest.safeParse(input.digest).success || mathDigest(text) !== input.digest) throw new Error('math_continuation_identity_changed');
  const directory = path.resolve(runtimeDirectory), file = path.join(directory, 'continuation.json');
  assertMathCanonicalPath(directory);
  for (const item of manifest.attachments) {
    const content = input.contents.get(item.sha256);
    if (typeof content !== 'string' || Buffer.byteLength(content) !== item.bytes || mathDigest(content) !== item.sha256)
      throw new Error('math_continuation_content_changed');
  }
  for (const item of manifest.attachments) writeFrozen(path.join(directory, item.contentPath), input.contents.get(item.sha256)!);
  writeFrozen(file, text);
  return readContinuationSnapshot(file, input.digest, manifest);
}

/** Resume and readers use only pinned blobs, even when original paths have disappeared or changed. */
export function readContinuationSnapshot(file: string, expectedDigest: string, expected?: ContinuationIdentity): ContinuationSnapshot {
  if (!digest.safeParse(expectedDigest).success) throw new Error('math_continuation_identity_changed');
  const resolved = path.resolve(file), loaded = readText(resolved, maxManifestBytes, true);
  if (mathDigest(loaded.bytes) !== expectedDigest) throw new Error('math_continuation_identity_changed');
  let value: unknown;
  try { value = JSON.parse(loaded.text); } catch { throw new Error('math_continuation_snapshot_invalid'); }
  const manifest = validateSnapshot(value);
  if (canonicalMathJson(manifest) !== loaded.text) throw new Error('math_continuation_snapshot_invalid');
  assertIdentity(manifest, expected);
  const checked = new Set<string>();
  for (const item of manifest.attachments) if (!checked.has(item.sha256)) {
    readContent(path.join(path.dirname(resolved), item.contentPath), item, true); checked.add(item.sha256);
  }
  return { file: resolved, digest: expectedDigest, manifest };
}

export function copyContinuationSnapshot(snapshot: ContinuationSnapshot, projectRoot: string): ContinuationSnapshot {
  const current = readContinuationSnapshot(snapshot.file, snapshot.digest, snapshot.manifest);
  const contents = new Map(current.manifest.attachments.map(item => [item.sha256,
    readContent(path.join(path.dirname(current.file), item.contentPath), item, true)]));
  return freezeContinuationInput({ ...current, contents }, path.join(path.resolve(projectRoot), '.lake'));
}

const shellArgument = (value: string) => "'" + value.replaceAll("'", "'\\''") + "'";

export function continuationContextSection(snapshot: ContinuationSnapshot, command: string, projectRelative: string): ContextSection {
  const current = readContinuationSnapshot(snapshot.file, snapshot.digest, snapshot.manifest);
  const packet = { schema: 'theorem-os.continuation-index.v1', authority: 'advisory-continuation',
    proofAcceptance: 'not-assessed', taskDigest: current.manifest.taskDigest, problemReceiptDigest: current.manifest.problemReceiptDigest,
    snapshot: path.posix.join(projectRelative.replaceAll('\\', '/'), '.lake/continuation.json'), sha256: current.digest,
    attachments: current.manifest.attachments.map(item => ({ ...item,
      readCommand: `${command} continuation read --snapshot ${shellArgument(current.file)} --sha256 ${shellArgument(current.digest)} --id ${shellArgument(item.id)} --offset 0 --max-bytes 16000` })) };
  return { id: `continuation-input:${current.digest}`, kind: 'continuation',
    text: 'Historical continuation attachments (advisory; recorded checks require fresh verification). Read exact text pages as needed; concatenate them using nextOffset. Old hypotheses and proof drafts do not change the original statement or its assumptions.\n' + JSON.stringify(packet) };
}

const splitsSurrogate = (text: string, offset: number) => offset > 0 && offset < text.length &&
  text.charCodeAt(offset - 1) >= 0xd800 && text.charCodeAt(offset - 1) <= 0xdbff &&
  text.charCodeAt(offset) >= 0xdc00 && text.charCodeAt(offset) <= 0xdfff;

export function readContinuationPage(file: string, expectedDigest: string, id: string,
  options: { offset?: number; maxBytes?: number } = {}) {
  const { offset = 0, maxBytes = 16000 } = options;
  if (!Number.isSafeInteger(offset) || offset < 0 || !Number.isSafeInteger(maxBytes) || maxBytes < 1024 || maxBytes > 16000)
    throw new Error('math_continuation_read_options_invalid');
  const current = readContinuationSnapshot(file, expectedDigest), item = current.manifest.attachments.find(item => item.id === id);
  if (!item) throw new Error('math_continuation_attachment_not_found');
  const text = readContent(path.join(path.dirname(current.file), item.contentPath), item, true);
  if (offset > text.length || splitsSurrogate(text, offset)) throw new Error('math_continuation_read_position_invalid');
  const packet = (end: number) => ({ schema: 'theorem-os.continuation-page.v1' as const,
    authority: 'advisory-continuation' as const, proofAcceptance: 'not-assessed' as const,
    taskDigest: current.manifest.taskDigest, problemReceiptDigest: current.manifest.problemReceiptDigest,
    snapshotDigest: current.digest, id: item.id, kind: item.kind, evidence: item.provenance.evidence,
    sha256: item.sha256, bytes: item.bytes, offsetEncoding: 'utf16-code-unit' as const, endOffsetExclusive: true as const,
    startOffset: offset, endOffset: end, text: text.slice(offset, end), truncated: end < text.length,
    ...(end < text.length ? { nextOffset: end } : {}) });
  const fits = (end: number) => Buffer.byteLength(JSON.stringify(packet(end))) + 1 <= maxBytes;
  if (text.length - offset <= maxBytes && fits(text.length)) return packet(text.length);
  if (!fits(offset)) throw new Error('math_continuation_read_budget_too_small');
  let lower = offset + 1, upper = Math.min(text.length - 1, offset + maxBytes), best = offset;
  while (lower <= upper) {
    const middle = Math.floor((lower + upper) / 2), end = splitsSurrogate(text, middle) ? middle - 1 : middle;
    if (fits(end)) { best = end; lower = middle + 1; } else upper = middle - 1;
  }
  if (best === offset && offset < text.length) throw new Error('math_continuation_read_budget_too_small');
  return packet(best);
}
