import fs from 'node:fs';
import path from 'node:path';
import { z } from 'zod';
import { canonicalMathJson, mathDigest, writeMathFrozen } from '../math/mathRuntimeIo';
import { assertMathCanonicalPath } from '../math/paths';
import { inspectLeanDeclarationRegions, inspectScopedLeanDeclarations } from '../math/leanSource';
import { knowledgeSearchGroup, knowledgeVersionSummary } from './theoremKnowledgeSearch';
import { buildKnowledgeRouteFindings, knowledgeRouteFindingSchema, validateKnowledgeRouteFindings,
  type KnowledgeRouteFindingCandidate } from './theoremKnowledgeFindings';

export { searchTheoremKnowledge, searchTheoremKnowledgeBatch, searchTheoremKnowledgeRequests } from './theoremKnowledgeSearch';
export type { KnowledgeSearchOptions, KnowledgeSearchRequest } from './theoremKnowledgeSearch';
export { getKnowledgeConsumers } from './theoremKnowledgeConsumers';
export type { KnowledgeConsumersOptions } from './theoremKnowledgeConsumers';
export { searchKnowledgeRouteFindings, searchKnowledgeRouteFindingRequests, getKnowledgeRouteFinding,
  getKnowledgeRouteFindingPage } from './theoremKnowledgeFindings';
export type { KnowledgeRouteFinding, KnowledgeRouteFindingCandidate, KnowledgeRouteContract,
  KnowledgeRouteFindingSearchOptions, KnowledgeRouteFindingSearchRequest } from './theoremKnowledgeFindings';

const hash = z.string().regex(/^[a-f0-9]{64}$/u);
const reference = z.object({ file: z.string(), name: z.string() }).strict();
const statementContext = z.object({
  type: z.string().min(1).refine(value => Buffer.byteLength(value) <= 24000),
  constants: z.array(z.object({ name: z.string().max(1000), module: z.string().max(1000),
    type: z.string().refine(value => Buffer.byteLength(value) <= 8000),
    definition: z.string().refine(value => Buffer.byteLength(value) <= 12000).optional() }).strict()).max(256),
  omitted: z.array(z.string().max(1000)).max(257),
  references: z.object({ statement: z.array(reference).max(256), proof: z.array(reference).max(256) }).strict().optional(),
}).strict();
/** An elaborated historical interface stays separate from its original source header. */
export const knowledgeElaborationSchema = z.object({
  schema: z.literal('theorem-os.knowledge-elaboration.v1'), evidence: z.literal('recorded-not-replayed'),
  fullType: z.string().min(1).refine(value => Buffer.byteLength(value) <= 2_000_000),
  universes: z.array(z.string().min(1).max(1000)).max(256), statementContext: statementContext.optional(),
  omissions: z.array(z.string().max(1000)).max(512), enrichmentDigest: hash, sourceDigest: hash,
  declarationDigest: hash, collectorDigest: hash, queryDigest: hash, artifactsDigest: hash,
  environmentDigest: hash, toolIdentity: z.string().min(1).max(4096), sealedEnvironmentIdentity: z.string().max(4096).optional(),
}).strict();
const provenance = z.object({
  kind: z.enum(['solver-check', 'accepted-archive', 'local-verified-archive']), problemId: z.string().min(1),
  source: z.string(), sourceDigest: hash, sourceCommit: z.string().optional(),
  archiveRecordDigest: hash.optional(),
  runId: z.string().optional(), taskId: z.string().optional(), taskDigest: z.string().optional(),
  environmentDigest: z.string().optional(), problemReceiptDigest: z.string().optional(),
  checkedCommit: z.string().optional(), receiptIds: z.array(z.string()),
  resultUrl: z.string().optional(),
}).strict();
const theorem = z.object({
  name: z.string().min(1), file: z.string(), type: z.string().min(1),
  typeKind: z.enum(['closed-task-type', 'source-header']), kind: z.enum(['lemma', 'goal']),
  description: z.string(), premises: z.array(z.string()),
  elaboration: knowledgeElaborationSchema.optional(),
  dependencies: z.object({ statement: z.array(reference), proof: z.array(reference),
    tasks: z.array(z.object({ taskId: z.string(), taskDigest: z.string() }).strict()),
    coverage: z.enum(['recorded', 'unavailable']),
  }).strict(),
}).strict();
export const theoremKnowledgeEntrySchema = theorem.extend({ id: hash, contextDigest: hash, environmentDigest: z.string().optional(), declaration: z.string().min(1),
  provenance: z.array(provenance).min(1) }).strict();
const schema = z.object({
  schema: z.literal('theorem-os.theorem-knowledge.v1'),
  evidence: z.literal('recorded-not-replayed'), requiresFreshCheck: z.literal(true),
  entries: z.array(theoremKnowledgeEntrySchema), contexts: z.record(hash, z.record(z.string(), hash)), sources: z.record(hash, z.string()),
  routeFindings: z.array(knowledgeRouteFindingSchema).optional(),
}).strict();

export type KnowledgeProvenance = z.infer<typeof provenance>;
export type KnowledgeTheorem = z.infer<typeof theorem>;
export type KnowledgeCandidate = KnowledgeTheorem & { files: Record<string, string>; provenance: KnowledgeProvenance };
export type KnowledgeImportResult = { candidates: KnowledgeCandidate[]; findings?: KnowledgeRouteFindingCandidate[];
  skipped: { source: string; name?: string; reason: string }[] };
export type TheoremKnowledgeBase = z.infer<typeof schema>;
export type TheoremKnowledgeEntry = z.infer<typeof theoremKnowledgeEntrySchema>;

const metadataSchema = schema.omit({ sources: true });
const sourceIdentitiesSchema = z.record(hash, z.object({ bytes: z.number().int().nonnegative().max(256 * 1024 * 1024) }).strict());
const sourceIdentitiesByBase = new WeakMap<TheoremKnowledgeBase, Record<string, { bytes: number }>>();

/** Only proof sources and pinned Lean project manifests belong in this corpus. */
export function allowedKnowledgeFile(file: string): boolean {
  return Boolean(file && !path.posix.isAbsolute(file) && !file.includes('\\') && !file.includes('\0') &&
    file.split('/').every(part => part && part !== '.' && part !== '..' && !part.startsWith('.') && part !== 'Solution.lean') &&
    (file.endsWith('.lean') || ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json'].includes(file)));
}

export type KnowledgeDeclarationLocation = {
  name: string; qualifiedName: string; namespace: string;
  kind: ReturnType<typeof inspectScopedLeanDeclarations>[number]['kind'];
  startOffset: number; bodyOffset: number; endOffset: number; declarationType: string;
};
const declarationCache = new Map<string, {
  qualified: Map<string, KnowledgeDeclarationLocation[]>; aliases: Map<string, KnowledgeDeclarationLocation[]>; bytes: number;
}>();
let declarationCacheBytes = 0;
export function locateKnowledgeDeclaration(source: string, name: string): KnowledgeDeclarationLocation {
  const digest = mathDigest(source);
  let cached = declarationCache.get(digest);
  if (!cached) {
    const regions = new Map(inspectLeanDeclarationRegions(source).map(item => [item.startOffset, item]));
    const qualified = new Map<string, KnowledgeDeclarationLocation[]>(), aliases = new Map<string, KnowledgeDeclarationLocation[]>();
    for (const declaration of inspectScopedLeanDeclarations(source)) {
      const region = regions.get(declaration.startOffset);
      if (!region) continue;
      const location: KnowledgeDeclarationLocation = { ...region, qualifiedName: declaration.qualifiedName,
        namespace: declaration.namespace, kind: declaration.kind };
      qualified.set(declaration.qualifiedName, [...(qualified.get(declaration.qualifiedName) ?? []), location]);
      aliases.set(declaration.name, [...(aliases.get(declaration.name) ?? []), location]);
    }
    cached = { qualified, aliases, bytes: Buffer.byteLength(source) };
    const allowance = 32 * 1024 * 1024;
    while (declarationCache.size && (declarationCacheBytes + cached.bytes > allowance || declarationCache.size >= 64)) {
      const oldest = declarationCache.keys().next().value!;
      declarationCacheBytes -= declarationCache.get(oldest)!.bytes; declarationCache.delete(oldest);
    }
    if (cached.bytes <= allowance) { declarationCache.set(digest, cached); declarationCacheBytes += cached.bytes; }
  }
  const requested = name.startsWith('_root_.') ? name.slice(7) : name;
  const matches = cached.qualified.get(requested) ?? (name.startsWith('_root_.') ? undefined : cached.aliases.get(requested));
  if (matches?.length !== 1) throw new Error('math_knowledge_declaration_missing_or_ambiguous');
  return matches[0]!;
}

export function knowledgeDeclaration(source: string, name: string): string {
  const location = locateKnowledgeDeclaration(source, name);
  return source.slice(location.startOffset, location.endOffset);
}

const entryIdentity = (item: Omit<TheoremKnowledgeEntry, 'id' | 'provenance'>) => mathDigest(canonicalMathJson(item));

/** Deduplicate bytes and exact contextual versions; names alone never identify a theorem. */
export function buildTheoremKnowledge(candidates: readonly KnowledgeCandidate[], previous?: TheoremKnowledgeBase,
  findings: readonly KnowledgeRouteFindingCandidate[] = []): TheoremKnowledgeBase {
  const result: TheoremKnowledgeBase = previous ? structuredClone(validateTheoremKnowledge(previous)) : {
    schema: 'theorem-os.theorem-knowledge.v1', evidence: 'recorded-not-replayed', requiresFreshCheck: true,
    entries: [], contexts: {}, sources: {},
  };
  const entries = new Map(result.entries.map(item => [item.id, item]));
  for (const candidate of candidates) {
    const { files, provenance: origin, ...raw } = candidate;
    const details = theorem.parse(raw);
    provenance.parse(origin);
    if (!allowedKnowledgeFile(details.file) || !files[details.file]) throw new Error('math_knowledge_root_source_missing');
    const context: Record<string, string> = {};
    for (const file of Object.keys(files).sort()) {
      if (!allowedKnowledgeFile(file)) throw new Error('math_knowledge_forbidden_source');
      const source = files[file]!, digest = mathDigest(source);
      context[file] = digest; result.sources[digest] = source;
    }
    const contextDigest = mathDigest(canonicalMathJson(context));
    result.contexts[contextDigest] = context;
    const value = { ...details, contextDigest, ...(origin.environmentDigest ? { environmentDigest: origin.environmentDigest } : {}),
      declaration: knowledgeDeclaration(files[details.file]!, details.name) };
    const id = entryIdentity(value), existing = entries.get(id);
    if (existing) {
      if (!existing.provenance.some(item => canonicalMathJson(item) === canonicalMathJson(origin))) existing.provenance.push(origin);
    } else entries.set(id, { ...value, id, provenance: [origin] });
  }
  result.entries = [...entries.values()].sort((a, b) => a.id.localeCompare(b.id));
  for (const item of result.entries) item.provenance.sort((a, b) => canonicalMathJson(a).localeCompare(canonicalMathJson(b)));
  result.contexts = Object.fromEntries(Object.entries(result.contexts).sort(([a], [b]) => a.localeCompare(b)));
  result.sources = Object.fromEntries(Object.entries(result.sources).sort(([a], [b]) => a.localeCompare(b)));
  if (findings.length || result.routeFindings) result.routeFindings = buildKnowledgeRouteFindings(findings, result.routeFindings);
  return result;
}

export function validateTheoremKnowledge(value: unknown): TheoremKnowledgeBase {
  const parsed = schema.safeParse(value);
  if (!parsed.success) throw new Error('math_knowledge_schema_invalid');
  const base = parsed.data;
  const identities: Record<string, { bytes: number }> = {};
  for (const [digest, source] of Object.entries(base.sources)) {
    if (mathDigest(source) !== digest) throw new Error('math_knowledge_source_changed');
    identities[digest] = { bytes: Buffer.byteLength(source) };
  }
  validateKnowledgeMetadata(base, identities);
  for (const item of base.entries) {
    const source = base.sources[base.contexts[item.contextDigest]![item.file]!]!;
    if (knowledgeDeclaration(source, item.name) !== item.declaration)
      throw new Error('math_knowledge_declaration_changed');
  }
  return base;
}

/** Validate the pinned catalog metadata without opening content-addressed source objects. */
export function validateKnowledgeMetadata(base: TheoremKnowledgeBase, sourceIdentities: Record<string, { bytes: number }>): void {
  const { sources: _sources, ...metadata } = base;
  if (!metadataSchema.safeParse(metadata).success || !sourceIdentitiesSchema.safeParse(sourceIdentities).success)
    throw new Error('math_knowledge_schema_invalid');
  for (const [digest, files] of Object.entries(base.contexts)) {
    if (mathDigest(canonicalMathJson(files)) !== digest) throw new Error('math_knowledge_context_changed');
    for (const [file, source] of Object.entries(files))
      if (!allowedKnowledgeFile(file) || !Object.hasOwn(sourceIdentities, source))
        throw new Error('math_knowledge_forbidden_or_missing_source');
  }
  const ids = new Set<string>();
  for (const item of base.entries) {
    const { id, provenance: _origins, ...identity } = item;
    if (ids.has(id) || entryIdentity(identity) !== id) throw new Error('math_knowledge_entry_changed');
    ids.add(id);
    const digest = base.contexts[item.contextDigest]?.[item.file];
    if (!digest || !allowedKnowledgeFile(item.file) || !Object.hasOwn(sourceIdentities, digest))
      throw new Error('math_knowledge_forbidden_or_missing_source');
  }
  sourceIdentitiesByBase.set(base, sourceIdentities);
  validateKnowledgeRouteFindings(base.routeFindings ?? []);
}

/** A new snapshot is immutable; refreshes use a new filename and an explicit merge. */
export function writeTheoremKnowledge(file: string, base: TheoremKnowledgeBase) {
  const resolved = path.resolve(file); assertMathCanonicalPath(resolved);
  validateTheoremKnowledge(base);
  const text = canonicalMathJson(base) + '\n';
  if (Buffer.byteLength(text) > 256 * 1024 * 1024) throw new Error('math_knowledge_too_large');
  fs.mkdirSync(path.dirname(resolved), { recursive: true, mode: 0o700 });
  writeMathFrozen(resolved, text);
  return { file: resolved, sha256: mathDigest(text), ...theoremKnowledgeStats(base) };
}

export function theoremKnowledgeStats(base: TheoremKnowledgeBase) {
  const problems = [...new Set([...base.entries.flatMap(item => item.provenance.map(origin => origin.problemId)),
    ...(base.routeFindings ?? []).map(item => item.scope.problemId)])].sort();
  return { entries: base.entries.length, problems, contexts: Object.keys(base.contexts).length,
    sourceBlobs: Object.keys(base.sources).length,
    solverCheckedEntries: base.entries.filter(item => item.provenance.some(origin => origin.kind === 'solver-check')).length,
    acceptedArchiveEntries: base.entries.filter(item => item.provenance.some(origin => origin.kind === 'accepted-archive')).length,
    localVerifiedArchiveEntries: base.entries.filter(item => item.provenance.some(origin => origin.kind === 'local-verified-archive')).length,
    routeFindings: base.routeFindings?.length ?? 0,
    evidence: base.evidence, requiresFreshCheck: base.requiresFreshCheck };
}

/** Verify the root declaration and any explicitly selected file within its exact archived context. */
export function readKnowledgeSource(base: TheoremKnowledgeBase, id: string, sourceFile?: string) {
  const item = base.entries.find(entry => entry.id === id);
  if (!item) throw new Error('math_knowledge_theorem_not_found');
  const files = base.contexts[item.contextDigest]!;
  if (sourceFile !== undefined && (!allowedKnowledgeFile(sourceFile) || !files[sourceFile]))
    throw new Error('math_knowledge_source_not_found');
  const rootSource = base.sources[files[item.file]!]!;
  if (mathDigest(rootSource) !== files[item.file] || knowledgeDeclaration(rootSource, item.name) !== item.declaration)
    throw new Error('math_knowledge_declaration_changed');
  const file = sourceFile ?? item.file, sha256 = files[file]!, source = file === item.file ? rootSource : base.sources[sha256]!;
  if (mathDigest(source) !== sha256) throw new Error('math_knowledge_source_changed');
  return { entry: item, files, file, sha256, source };
}

export function getKnowledgeTheorem(base: TheoremKnowledgeBase, id: string, sourceFile?: string) {
  const { entry: item, files, source } = readKnowledgeSource(base, id, sourceFile);
  const sourceIdentities = sourceIdentitiesByBase.get(base);
  const group = knowledgeSearchGroup(item);
  return { evidence: base.evidence, requiresFreshCheck: true,
    reuse: 'Adapt the declaration and required context only in owned sources. Confirm its type and every premise with Lean; historical receipts never grant current or official acceptance.',
    ...item,
    relatedVersions: base.entries.filter(other => knowledgeSearchGroup(other) === group)
      .map(other => knowledgeVersionSummary(other)),
    files: Object.entries(files).map(([file, sha256]) => ({ file, sha256,
      bytes: sourceIdentities?.[sha256]?.bytes ?? Buffer.byteLength(base.sources[sha256]!) })),
    ...(sourceFile === undefined ? {} : { source: { file: sourceFile, text: source } }),
  };
}
