import fs from 'node:fs';
import path from 'node:path';
import { z } from 'zod';
import { canonicalMathJson, mathDigest, readMathFile, readMathText, syncMathDirectory } from '../math/mathRuntimeIo';
import { assertMathCanonicalPath } from '../math/paths';
import { theoremKnowledgeEntrySchema, theoremKnowledgeStats, validateKnowledgeMetadata, validateTheoremKnowledge,
  type TheoremKnowledgeBase } from './theoremKnowledge';
import { knowledgeRouteFindingSchema } from './theoremKnowledgeFindings';

const hash = z.string().regex(/^[a-f0-9]{64}$/u);
const maxBytes = 256 * 1024 * 1024;
const sourceIdentity = z.object({ bytes: z.number().int().nonnegative().max(maxBytes) }).strict();
const directoryName = z.string().min(1).max(255).refine(value => !value.startsWith('.') &&
  !value.includes('/') && !value.includes('\\') && !value.includes('\0') && Buffer.byteLength(value) <= 255);
const packedSchema = z.object({
  schema: z.literal('theorem-os.theorem-knowledge.v2'), evidence: z.literal('recorded-not-replayed'),
  requiresFreshCheck: z.literal(true), entries: z.array(theoremKnowledgeEntrySchema),
  routeFindings: z.array(knowledgeRouteFindingSchema).optional(),
  contexts: z.record(hash, z.record(z.string(), hash)), sources: z.record(hash, sourceIdentity),
  objectsDirectory: directoryName, originSha256: hash.optional(),
}).strict();
type PackedManifest = Omit<z.infer<typeof packedSchema>, 'sources'> & { sources: Record<string, { bytes: number }> };

function validateManifest(value: unknown): PackedManifest {
  const parsed = packedSchema.safeParse(value);
  if (!parsed.success) throw new Error('math_knowledge_packed_schema_invalid');
  if (Object.values(parsed.data.sources).reduce((total, item) => total + item.bytes, 0) > maxBytes)
    throw new Error('math_knowledge_packed_sources_too_large');
  return parsed.data as PackedManifest;
}

function parseManifest(text: string): PackedManifest {
  let value: unknown;
  try { value = JSON.parse(text); }
  catch { throw new Error('math_knowledge_packed_schema_invalid'); }
  return validateManifest(value);
}

function objectsRoot(file: string, manifest: PackedManifest) {
  const root = path.join(path.dirname(file), manifest.objectsDirectory);
  assertMathCanonicalPath(root);
  const stat = fs.lstatSync(root, { throwIfNoEntry: false });
  if (!stat?.isDirectory()) throw new Error('math_knowledge_packed_objects_missing');
  return root;
}

function inspectSource(root: string, digest: string, bytes: number) {
  const file = path.join(root, digest);
  assertMathCanonicalPath(file);
  const stat = fs.lstatSync(file, { throwIfNoEntry: false });
  if (!stat?.isFile() || stat.nlink !== 1) throw new Error('math_knowledge_packed_source_missing_or_invalid');
  if (stat.size !== bytes) throw new Error('math_knowledge_source_changed');
  if ((stat.mode & 0o222) !== 0) throw new Error('math_knowledge_packed_source_not_frozen');
  return file;
}

function readSource(root: string, digest: string, bytes: number) {
  const file = inspectSource(root, digest, bytes), loaded = readMathFile(file, bytes).bytes;
  if (loaded.length !== bytes || mathDigest(loaded) !== digest) throw new Error('math_knowledge_source_changed');
  try { return new TextDecoder('utf-8', { fatal: true }).decode(loaded); }
  catch { throw new Error('math_knowledge_packed_source_invalid_utf8'); }
}

function packedView(resolved: string, text: string, digest: string, manifest: PackedManifest) {
  const sources: Record<string, string> = {};
  const root = path.join(path.dirname(resolved), manifest.objectsDirectory);
  for (const [sourceDigest, identity] of Object.entries(manifest.sources))
    Object.defineProperty(sources, sourceDigest, { enumerable: true, get: () => {
      objectsRoot(resolved, manifest);
      return readSource(root, sourceDigest, identity.bytes);
    } });
  const base: TheoremKnowledgeBase = { schema: 'theorem-os.theorem-knowledge.v1',
    evidence: manifest.evidence, requiresFreshCheck: manifest.requiresFreshCheck,
    entries: manifest.entries, contexts: manifest.contexts, sources,
    ...(manifest.routeFindings ? { routeFindings: manifest.routeFindings } : {}) };
  validateKnowledgeMetadata(base, manifest.sources);
  objectsRoot(resolved, manifest);
  for (const [sourceDigest, identity] of Object.entries(manifest.sources)) inspectSource(root, sourceDigest, identity.bytes);
  return { base, digest, text, format: 'v2' as const };
}

/** The pinned manifest authenticates metadata and source hashes; proof bytes are checked only when requested. */
export function readPackedKnowledge(file: string, expectedDigest?: string) {
  const resolved = path.resolve(file);
  assertMathCanonicalPath(resolved);
  const text = readMathText(resolved, maxBytes), digest = mathDigest(text);
  if (expectedDigest && (!hash.safeParse(expectedDigest).success || expectedDigest !== digest))
    throw new Error('math_knowledge_identity_changed');
  return packedView(resolved, text, digest, parseManifest(text));
}

function writeFrozen(file: string, contents: string) {
  assertMathCanonicalPath(file);
  const fd = fs.openSync(file, fs.constants.O_WRONLY | fs.constants.O_CREAT | fs.constants.O_EXCL | fs.constants.O_NOFOLLOW, 0o400);
  try { fs.writeFileSync(fd, contents); fs.fsyncSync(fd); }
  finally { fs.closeSync(fd); }
}

/** Publish blobs before their immutable manifest; an interrupted publication never exposes a complete catalog. */
export function writePackedKnowledge(file: string, base: TheoremKnowledgeBase, originSha256?: string) {
  const resolved = path.resolve(file);
  assertMathCanonicalPath(resolved);
  const objectsDirectory = path.basename(resolved) + '.objects';
  if (!directoryName.safeParse(objectsDirectory).success || (originSha256 !== undefined && !hash.safeParse(originSha256).success))
    throw new Error('math_knowledge_packed_schema_invalid');
  const root = path.join(path.dirname(resolved), objectsDirectory);
  if (fs.lstatSync(resolved, { throwIfNoEntry: false }) || fs.lstatSync(root, { throwIfNoEntry: false }))
    throw new Error('math_knowledge_packed_output_exists');
  const checked = validateTheoremKnowledge(base);
  const manifest: PackedManifest = { schema: 'theorem-os.theorem-knowledge.v2', evidence: checked.evidence,
    requiresFreshCheck: checked.requiresFreshCheck, entries: checked.entries, contexts: checked.contexts,
    ...(checked.routeFindings ? { routeFindings: checked.routeFindings } : {}),
    sources: Object.fromEntries(Object.entries(checked.sources).map(([digest, text]) => [digest, { bytes: Buffer.byteLength(text) }])),
    objectsDirectory, ...(originSha256 === undefined ? {} : { originSha256 }) };
  const text = canonicalMathJson(manifest) + '\n';
  parseManifest(text);
  fs.mkdirSync(path.dirname(resolved), { recursive: true, mode: 0o700 });
  assertMathCanonicalPath(path.dirname(resolved));
  fs.mkdirSync(root, { mode: 0o700 });
  for (const [sourceDigest, source] of Object.entries(checked.sources)) writeFrozen(path.join(root, sourceDigest), source);
  syncMathDirectory(root);
  writeFrozen(resolved, text);
  syncMathDirectory(path.dirname(resolved));
  return { file: resolved, sha256: mathDigest(text), format: 'v2' as const, ...theoremKnowledgeStats(checked) };
}

/** Worker copies retain the exact manifest bytes, and verify existing objects before an idempotent retry. */
export function copyPackedKnowledge(manifestText: string, fromCatalogFile: string, toCatalogFile: string) {
  const digest = mathDigest(manifestText), source = readPackedKnowledge(fromCatalogFile, digest);
  const manifest = parseManifest(manifestText), resolved = path.resolve(toCatalogFile);
  assertMathCanonicalPath(resolved);
  const root = path.join(path.dirname(resolved), manifest.objectsDirectory);
  assertMathCanonicalPath(root);
  const existingManifest = fs.lstatSync(resolved, { throwIfNoEntry: false });
  if (existingManifest && (!existingManifest.isFile() || (existingManifest.mode & 0o222) !== 0 ||
      mathDigest(readMathText(resolved, maxBytes)) !== digest)) throw new Error('math_knowledge_identity_changed');
  const existingRoot = fs.lstatSync(root, { throwIfNoEntry: false });
  if (existingRoot && !existingRoot.isDirectory()) throw new Error('math_knowledge_packed_objects_missing');

  const sources = Object.entries(source.base.sources);
  for (const [sourceDigest] of sources) {
    const target = path.join(root, sourceDigest);
    if (fs.lstatSync(target, { throwIfNoEntry: false })) readSource(root, sourceDigest, manifest.sources[sourceDigest]!.bytes);
  }
  fs.mkdirSync(path.dirname(resolved), { recursive: true, mode: 0o700 });
  assertMathCanonicalPath(path.dirname(resolved));
  if (!existingRoot) fs.mkdirSync(root, { mode: 0o700 });
  for (const [sourceDigest, text] of sources) {
    const target = path.join(root, sourceDigest);
    if (!fs.lstatSync(target, { throwIfNoEntry: false })) writeFrozen(target, text);
  }
  syncMathDirectory(root);
  if (!existingManifest) writeFrozen(resolved, manifestText);
  syncMathDirectory(path.dirname(resolved));
  return { file: resolved, sha256: digest, format: 'v2' as const, ...theoremKnowledgeStats(source.base) };
}

/** Existing monolithic catalogs remain readable while new manifests load only their metadata. */
export function readKnowledgeCatalog(file: string, expectedDigest?: string) {
  const resolved = path.resolve(file);
  assertMathCanonicalPath(resolved);
  const text = readMathText(resolved, maxBytes), digest = mathDigest(text);
  if (expectedDigest && (!hash.safeParse(expectedDigest).success || expectedDigest !== digest))
    throw new Error('math_knowledge_identity_changed');
  let value: unknown;
  try { value = JSON.parse(text); }
  catch { throw new Error('math_knowledge_schema_invalid'); }
  const version = (value as { schema?: unknown } | null)?.schema;
  if (version === 'theorem-os.theorem-knowledge.v2') return packedView(resolved, text, digest, validateManifest(value));
  if (version !== 'theorem-os.theorem-knowledge.v1') throw new Error('math_knowledge_schema_invalid');
  return { base: validateTheoremKnowledge(value), digest, text, format: 'v1' as const };
}

export function copyKnowledgeSnapshot(knowledge: { text: string; digest: string; format: 'v1' | 'v2' },
  fromFile: string, toFile: string) {
  if (!hash.safeParse(knowledge.digest).success || mathDigest(knowledge.text) !== knowledge.digest)
    throw new Error('math_knowledge_identity_changed');
  if (knowledge.format === 'v2') return copyPackedKnowledge(knowledge.text, fromFile, toFile);
  const resolved = path.resolve(toFile);
  assertMathCanonicalPath(resolved);
  const existing = fs.lstatSync(resolved, { throwIfNoEntry: false });
  if (existing) {
    if (!existing.isFile() || (existing.mode & 0o222) !== 0 || mathDigest(readMathText(resolved, maxBytes)) !== knowledge.digest)
      throw new Error('math_knowledge_identity_changed');
  } else {
    fs.mkdirSync(path.dirname(resolved), { recursive: true, mode: 0o700 });
    writeFrozen(resolved, knowledge.text);
    syncMathDirectory(path.dirname(resolved));
  }
  return { file: resolved, sha256: knowledge.digest, format: 'v1' as const };
}
