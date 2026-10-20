import fs from 'node:fs';
import path from 'node:path';
import { z } from 'zod';
import { canonicalMathJson, mathDigest, readMathFile, syncMathDirectory } from '../math/mathRuntimeIo';
import { assertMathCanonicalPath } from '../math/paths';
import { collectLeanKnowledgeEnrichment, leanKnowledgeCollectorIdentity, leanKnowledgeSourceDigest,
  leanKnowledgeQuery, parseLeanKnowledgeReferences, leanKnowledgeReferenceOmissions,
  parseLeanKnowledgeContext } from '../math/leanKnowledgeEnrichment';
import { mathLocalModuleBuildOrder } from '../math/mathConstructionSources';
import { allowedKnowledgeFile, knowledgeDeclaration, knowledgeElaborationSchema, type KnowledgeCandidate } from './theoremKnowledge';
import { importAcceptedKnowledge } from './theoremKnowledgeAccepted';

const hash = z.string().regex(/^[a-f0-9]{64}$/u);
const commit = z.string().regex(/^[a-f0-9]{40,64}$/u);
const maxBytes = 256 * 1024 * 1024;
const collectorVersion = z.enum(['complete-proof-knowledge-collector-v1', 'complete-proof-knowledge-collector-v2',
  'complete-proof-knowledge-collector-v3']);
const byteCount = z.number().int().nonnegative().max(maxBytes);
const relative = (file: string) => Boolean(file && !path.posix.isAbsolute(file) && !file.includes('\\') && !file.includes('\0') &&
  file.split('/').every(part => part && part !== '.' && part !== '..'));
const fileName = z.string().min(1).max(4096).refine(relative);
const identity = z.object({ file: fileName, digest: hash, bytes: byteCount }).strict();
const configurationIdentity = identity.extend({ digest: hash.nullable() }).strict();
const reference = z.object({ name: z.string().min(1).max(1000), file: fileName }).strict();
const references = z.object({ statement: z.array(reference).max(4096), proof: z.array(reference).max(4096) }).strict();
const statementContext = knowledgeElaborationSchema.shape.statementContext.unwrap();
const artifact = z.object({ kind: z.enum(['query', 'full-type', 'statement-context', 'diagnostics']),
  path: fileName, digest: hash, bytes: byteCount }).strict();
const root = z.object({ id: hash, name: z.string().min(1).max(1000), file: fileName,
  sourceDigest: hash, declarationDigest: hash,
  modules: z.array(z.object({ file: fileName, sourceRoot: z.string().refine(value => value === '' || value === '.' || relative(value)),
    module: z.string().min(1).max(1000) }).strict()).min(1).max(4096) }).strict();
const collectedRoot = root.omit({ sourceDigest: true, declarationDigest: true, modules: true }).extend({
  status: z.enum(['collected', 'failed', 'unavailable']), sourceDigest: hash.optional(), declarationDigest: hash.optional(),
  fullType: knowledgeElaborationSchema.shape.fullType.optional(), universes: knowledgeElaborationSchema.shape.universes.optional(),
  statementContext: statementContext.optional(), references: references.optional(),
  omissions: knowledgeElaborationSchema.shape.omissions, queryDigest: hash.optional(), artifacts: z.array(artifact).max(4096),
  reason: z.string().optional(),
}).strict();
const collection = z.object({ schema: z.literal('theorem-os.lean-knowledge-enrichment.v1'),
  authority: z.literal('advisory-lean-process'), proofAcceptance: z.literal('not-assessed'),
  identity: z.object({ sourceDigest: hash, sources: z.array(identity).max(4096),
    configuration: z.array(configurationIdentity).max(32), toolchain: z.string().nullable(),
    executionConfiguration: z.array(configurationIdentity).max(32).optional(), executionSourceDigest: hash.optional(),
    toolIdentity: z.string().min(1).optional(), tools: z.array(z.object({ command: z.enum(['lean', 'lake']),
      file: z.string().min(1), digest: hash }).strict()).max(32),
    environmentDigest: hash.optional(), sealedEnvironmentIdentity: z.string().min(1).optional(),
    collector: z.object({ version: collectorVersion, source: z.string().min(1), digest: hash }).strict(),
  }).strict(), roots: z.array(collectedRoot).max(4096),
}).strict();
const snapshot = z.object({
  schema: z.literal('theorem-os.knowledge-enrichment.v1'), evidence: z.literal('recorded-not-replayed'),
  requiresFreshCheck: z.literal(true),
  manifest: z.object({ file: z.string().min(1), digest: hash, bytes: byteCount }).strict(),
  records: z.array(z.object({ problemId: z.string().min(1).max(256), directory: fileName,
    recordDigest: hash, sourceCommit: commit, files: z.array(identity).min(1).max(4096),
    configuration: z.array(configurationIdentity).max(32), roots: z.array(root).max(4096), collection,
  }).strict()).min(1).max(1024),
  artifacts: z.array(z.object({ path: fileName, digest: hash, bytes: byteCount,
    contentsBase64: z.string().max(maxBytes * 4 / 3 + 4) }).strict()).max(16384),
}).strict();
const schema = snapshot.extend({ digest: hash }).strict();
export type KnowledgeEnrichment = z.infer<typeof schema>;
type EnrichmentRecord = KnowledgeEnrichment['records'][number];
type RetainedDiagnostics = { stdout?: string; exitCode?: number; timedOut?: boolean; aborted?: boolean;
  sourceDigest?: string; environmentDigest?: string };
const configurationFiles = ['lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json', '.lake/package-overrides.json'];
const mismatch = () => new Error('math_knowledge_enrichment_mismatch');
const equal = (left: unknown, right: unknown) => left === undefined || right === undefined
  ? left === right : canonicalMathJson(left) === canonicalMathJson(right);
const ordered = <T extends { file?: string }>(files: readonly T[]) => [...files].sort((a, b) => a.file < b.file ? -1 : a.file > b.file ? 1 : 0);
const sourceIdentities = (items: readonly z.infer<typeof identity>[]) => items.map(item => ({ file: item.file, digest: item.digest, bytes: item.bytes }));
const unique = (items: readonly string[]) => new Set(items).size === items.length;
const rootId = (manifestDigest: string, record: Pick<EnrichmentRecord, 'recordDigest' | 'sourceCommit'>,
  item: Omit<EnrichmentRecord['roots'][number], 'id'>) => mathDigest(canonicalMathJson({ manifestDigest,
    recordDigest: record.recordDigest, sourceCommit: record.sourceCommit, ...item }));

/** Validate frozen advisory output without starting Lean or requiring its old environment. */
export function validateKnowledgeEnrichment(value: unknown): KnowledgeEnrichment {
  const parsed = schema.safeParse(value);
  if (!parsed.success) throw new Error('math_knowledge_enrichment_schema_invalid');
  const result = parsed.data, { digest, ...payload } = result;
  if (mathDigest(canonicalMathJson(payload)) !== digest) throw new Error('math_knowledge_enrichment_changed');
  if (!path.isAbsolute(result.manifest.file) || path.resolve(result.manifest.file) !== result.manifest.file ||
      !unique(result.records.map(record => record.problemId)) || !unique(result.records.map(record => record.directory)) ||
      !unique(result.artifacts.map(item => item.path))) throw mismatch();
  const embedded = new Map(result.artifacts.map(item => [item.path, item]));
  const artifactBytes = new Map<string, Buffer>();
  let totalBytes = 0;
  for (const item of result.artifacts) {
    if (!/^\.lake\/knowledge-enrichment\/[^/]+\/.+/u.test(item.path)) throw mismatch();
    const bytes = Buffer.from(item.contentsBase64, 'base64'); totalBytes += bytes.length;
    if (totalBytes > maxBytes || bytes.toString('base64') !== item.contentsBase64 || bytes.length !== item.bytes ||
        mathDigest(bytes) !== item.digest) throw new Error('math_knowledge_enrichment_artifact_changed');
    artifactBytes.set(item.path, bytes);
  }
  const referencedArtifacts = new Set<string>();
  for (const record of result.records) {
    if (!unique(record.files.map(item => item.file)) || !unique(record.configuration.map(item => item.file)) ||
        !equal(ordered(record.configuration).map(item => item.file), [...configurationFiles].sort()) ||
        record.configuration.some(item => item.digest === null && item.bytes !== 0) ||
        !unique(record.roots.map(item => item.id)) || !unique(record.roots.map(item => `${item.file}\0${item.name}`))) throw mismatch();
    const collected = record.collection;
    const version = collected.identity.collector.version, collector = leanKnowledgeCollectorIdentity(version);
    if (!equal(collected.identity.collector, collector) || mathDigest(collector.source) !== collector.digest)
      throw new Error('math_knowledge_enrichment_collector_changed');
    if (!unique(collected.identity.sources.map(item => item.file)) ||
        !unique(collected.identity.configuration.map(item => item.file)) || !unique(collected.roots.map(item => item.id))) throw mismatch();
    const expectedSources = ordered(record.files.filter(item => allowedKnowledgeFile(item.file) && item.file.endsWith('.lean') && item.file !== 'lakefile.lean'));
    if (!equal(collected.identity.sources, expectedSources) || !equal(collected.identity.configuration, record.configuration) ||
        leanKnowledgeSourceDigest(sourceIdentities(collected.identity.sources), sourceIdentities(collected.identity.configuration)) !== collected.identity.sourceDigest ||
        !unique(collected.identity.tools.map(item => item.command)) ||
        collected.identity.tools.some(item => !path.isAbsolute(item.file) || path.resolve(item.file) !== item.file)) throw mismatch();
    if (Boolean(collected.identity.executionConfiguration) !== Boolean(collected.identity.executionSourceDigest)) throw mismatch();
    if (collected.identity.executionConfiguration &&
        (!equal(ordered(collected.identity.executionConfiguration).map(item => item.file), [...configurationFiles].sort()) ||
        collected.identity.executionConfiguration.some(item => item.digest === null && item.bytes !== 0) ||
        leanKnowledgeSourceDigest(sourceIdentities(collected.identity.sources), sourceIdentities(collected.identity.executionConfiguration)) !== collected.identity.executionSourceDigest))
      throw mismatch();
    const roots = new Map(record.roots.map(item => [item.id, item]));
    for (const item of record.roots) {
      const { id, ...details } = item;
      if (rootId(result.manifest.digest, record, details) !== id ||
          !record.files.some(file => file.file === item.file && file.digest === item.sourceDigest) ||
          !unique(item.modules.map(module => module.file)) || !item.modules.some(module => module.file === item.file) ||
          item.modules.some(module => !expectedSources.some(source => source.file === module.file))) throw mismatch();
    }
    for (const item of collected.roots) {
      const typeBound = version === 'complete-proof-knowledge-collector-v1' ? 24000
        : version === 'complete-proof-knowledge-collector-v2' ? 256000 : 2_000_000;
      if (item.fullType !== undefined && Buffer.byteLength(item.fullType) > typeBound)
        throw new Error('math_knowledge_enrichment_type_export_invalid');
      const declared = roots.get(item.id);
      if (!declared || item.name !== declared.name || item.file !== declared.file ||
          item.sourceDigest !== undefined && item.sourceDigest !== declared.sourceDigest ||
          item.declarationDigest !== undefined && item.declarationDigest !== declared.declarationDigest) throw mismatch();
      if (!unique(item.artifacts.map(artifact => artifact.kind))) throw mismatch();
      if (item.status !== 'collected' && (item.fullType !== undefined || item.universes !== undefined ||
          item.statementContext !== undefined || item.references !== undefined)) throw mismatch();
      const refs = [item.references, item.statementContext?.references].filter(value => value !== undefined);
      if (refs.some(refs => [...refs.statement, ...refs.proof].some(ref =>
        !allowedKnowledgeFile(ref.file) || !record.files.some(file => file.file === ref.file)))) throw mismatch();
      for (const artifact of item.artifacts) {
        const contents = embedded.get(artifact.path);
        if (!contents || contents.digest !== artifact.digest || contents.bytes !== artifact.bytes) throw mismatch();
        referencedArtifacts.add(artifact.path);
      }
      const modules = declared.modules.map(module => ({ file: module.file, module: module.module }));
      const query = leanKnowledgeQuery({ id: declared.id, name: declared.name, file: declared.file },
        modules, record.roots.indexOf(declared), version);
      const text = (kind: z.infer<typeof artifact>['kind']) => {
        const artifact = item.artifacts.find(artifact => artifact.kind === kind);
        return artifact ? new TextDecoder('utf-8', { fatal: true }).decode(artifactBytes.get(artifact.path)!) : undefined;
      };
      if (text('query') !== undefined && text('query') !== query.source) throw new Error('math_knowledge_enrichment_artifact_changed');
      if (item.queryDigest !== undefined && !item.artifacts.some(artifact => artifact.kind === 'query' && artifact.digest === item.queryDigest))
        throw mismatch();
      for (const fullType of item.artifacts.filter(artifact => artifact.kind === 'full-type')) {
        let value: unknown;
        try { value = JSON.parse(new TextDecoder('utf-8', { fatal: true }).decode(artifactBytes.get(fullType.path)!)); }
        catch { throw new Error('math_knowledge_enrichment_artifact_changed'); }
        if (!equal(value, { name: item.name, fullType: item.fullType, universes: item.universes, typeComplete: true }))
          throw new Error('math_knowledge_enrichment_artifact_changed');
      }
      let context: typeof item.statementContext, contextOmissions: string[] = [], diagnostics: RetainedDiagnostics | undefined;
      try {
        if (text('statement-context') !== undefined) {
          const parsedContext = parseLeanKnowledgeContext(text('statement-context')!, item.id, version);
          context = parsedContext.context; contextOmissions = parsedContext.omissions;
        }
        if (text('diagnostics') !== undefined) diagnostics = JSON.parse(text('diagnostics')!);
      } catch { throw new Error('math_knowledge_enrichment_artifact_changed'); }
      if (diagnostics && (typeof diagnostics !== 'object' || Array.isArray(diagnostics)))
        throw new Error('math_knowledge_enrichment_artifact_changed');
      if (diagnostics) {
        const configuration = collected.identity.executionConfiguration ?? collected.identity.configuration;
        const sourceDigests = declared.modules.map(module => [module.file, expectedSources.find(source => source.file === module.file)!.digest]);
        sourceDigests.push([query.queryFile, mathDigest(query.source)]);
        const sourceDigest = mathDigest(JSON.stringify([configurationFiles.map(file => configuration.find(item => item.file === file)!.digest ?? ''), sourceDigests]));
        if (diagnostics.sourceDigest !== undefined && diagnostics.sourceDigest !== sourceDigest ||
            collected.identity.environmentDigest !== undefined && diagnostics.environmentDigest !== undefined &&
            diagnostics.environmentDigest !== collected.identity.environmentDigest)
          throw new Error('math_knowledge_enrichment_artifact_changed');
      }
      if (!equal(context, item.statementContext)) throw new Error('math_knowledge_enrichment_artifact_changed');
      if (item.status === 'collected') {
        if (diagnostics && (diagnostics.exitCode !== 0 || diagnostics.timedOut || diagnostics.aborted))
          throw new Error('math_knowledge_enrichment_artifact_changed');
        const parsedReferences = diagnostics?.exitCode === 0 && !diagnostics?.timedOut && !diagnostics?.aborted && typeof diagnostics?.stdout === 'string'
          ? parseLeanKnowledgeReferences(diagnostics.stdout, query.referenceMarker, modules.map(module => module.file), version,
            { name: declared.name, modules }) : undefined;
        const referenceOmissions = leanKnowledgeReferenceOmissions(typeof diagnostics?.stdout === 'string' ? diagnostics.stdout : '',
          query.referenceMarker, modules.map(module => module.file), version, { name: declared.name, modules });
        if (!equal(parsedReferences, item.references) ||
            !equal(item.omissions, [...contextOmissions, ...referenceOmissions]))
          throw new Error('math_knowledge_enrichment_artifact_changed');
      }
    }
  }
  if (referencedArtifacts.size !== embedded.size) throw mismatch();
  return result;
}

export function readKnowledgeEnrichment(file: string, expectedSha256?: string): KnowledgeEnrichment {
  const absolute = path.resolve(file); assertMathCanonicalPath(absolute);
  const bytes = readMathFile(absolute, maxBytes).bytes;
  if (expectedSha256 !== undefined && mathDigest(bytes) !== expectedSha256) throw new Error('math_knowledge_enrichment_changed');
  let value: unknown;
  try { value = JSON.parse(new TextDecoder('utf-8', { fatal: true }).decode(bytes)); }
  catch { throw new Error('math_knowledge_enrichment_schema_invalid'); }
  return validateKnowledgeEnrichment(value);
}

/** Enrichment snapshots are immutable and retain the exact query and diagnostic bytes. */
export function writeKnowledgeEnrichment(file: string, value: unknown) {
  const result = validateKnowledgeEnrichment(value), absolute = path.resolve(file); assertMathCanonicalPath(absolute);
  const text = canonicalMathJson(result) + '\n';
  if (Buffer.byteLength(text) > maxBytes) throw new Error('math_knowledge_enrichment_too_large');
  fs.mkdirSync(path.dirname(absolute), { recursive: true, mode: 0o700 });
  const descriptor = fs.openSync(absolute, 'wx', 0o400);
  try { fs.writeFileSync(descriptor, text); fs.fsyncSync(descriptor); } finally { fs.closeSync(descriptor); }
  syncMathDirectory(path.dirname(absolute));
  const roots = result.records.flatMap(record => record.collection.roots);
  const missing = result.records.reduce((total, record) => total + record.roots.length - record.collection.roots.length, 0);
  return { file: absolute, sha256: mathDigest(text), digest: result.digest, records: result.records.length,
    roots: roots.length + missing, reportedRoots: roots.length, missing, collected: roots.filter(root => root.status === 'collected').length,
    failed: roots.filter(root => root.status === 'failed').length, unavailable: roots.filter(root => root.status === 'unavailable').length + missing };
}

function readIdentity(projectRoot: string, file: string): z.infer<typeof configurationIdentity> {
  const absolute = path.join(projectRoot, file); assertMathCanonicalPath(absolute);
  if (!fs.existsSync(absolute)) return { file, digest: null, bytes: 0 };
  const bytes = readMathFile(absolute, 16 * 1024 * 1024).bytes;
  return { file, digest: mathDigest(bytes), bytes: bytes.length };
}

function acceptedSnapshot(manifestFile: string) {
  const file = path.resolve(manifestFile); assertMathCanonicalPath(file);
  const bytes = readMathFile(file, 16 * 1024 * 1024).bytes;
  // A second default import makes this API safe independently of the importer caller.
  const candidates = importAcceptedKnowledge(file).candidates;
  if (!bytes.equals(readMathFile(file, 16 * 1024 * 1024).bytes)) throw mismatch();
  const records = JSON.parse(new TextDecoder('utf-8', { fatal: true }).decode(bytes)) as {
    problem_id: string; directory: string; original_source_commit: string; source_sha256: Record<string, string> }[];
  const manifest = { file, digest: mathDigest(bytes), bytes: bytes.length };
  const recordsById = new Map(records.map(record => [record.problem_id, record]));
  function prepare(problemId: string) {
    const record = recordsById.get(problemId);
    if (!record) throw new Error('math_knowledge_enrichment_problem_not_found');
    const selected = candidates.filter(candidate => candidate.provenance.problemId === problemId);
    if (!relative(record.directory) || record.directory.split('/').some(part => part.startsWith('.'))) throw mismatch();
    const projectRoot = path.join(path.dirname(file), record.directory); assertMathCanonicalPath(projectRoot);
    const files = ordered(Object.entries(record.source_sha256).map(([source, digest]) => {
      if (!relative(source)) throw mismatch();
      const current = readIdentity(projectRoot, source);
      if (current.digest !== digest) throw mismatch();
      return { ...current, digest };
    }));
    const configuration = configurationFiles.map(source => readIdentity(projectRoot, source));
    const sourceFiles: string[] = [];
    const visit = (directory: string) => {
      for (const entry of fs.readdirSync(path.join(projectRoot, directory), { withFileTypes: true })) {
        if (entry.name.startsWith('.') || entry.name === 'Solution.lean') continue;
        const file = directory ? `${directory}/${entry.name}` : entry.name;
        if (entry.isDirectory()) visit(file);
        else if (file.endsWith('.lean') && file !== 'lakefile.lean' && allowedKnowledgeFile(file)) {
          assertMathCanonicalPath(path.join(projectRoot, file)); sourceFiles.push(file);
        }
      }
    };
    visit('');
    const expectedSources = files.filter(item => allowedKnowledgeFile(item.file) && item.file.endsWith('.lean') && item.file !== 'lakefile.lean');
    if (!equal(sourceFiles.sort(), expectedSources.map(item => item.file).sort())) throw mismatch();
    const binding = { problemId, directory: record.directory, recordDigest: mathDigest(canonicalMathJson(record)),
      sourceCommit: record.original_source_commit, files, configuration };
    const roots = selected.map(candidate => {
      if (candidate.provenance.source !== manifest.file || candidate.provenance.sourceDigest !== manifest.digest ||
          candidate.provenance.sourceCommit !== binding.sourceCommit || candidate.provenance.archiveRecordDigest !== binding.recordDigest)
        throw mismatch();
      const source = candidate.files[candidate.file]!;
      const details = { name: candidate.name, file: candidate.file, sourceDigest: files.find(item => item.file === candidate.file)!.digest,
        declarationDigest: mathDigest(knowledgeDeclaration(source, candidate.name)), modules: mathLocalModuleBuildOrder(projectRoot, candidate.file) };
      return { id: rootId(manifest.digest, binding, details), ...details };
    });
    const toolchain = configuration.find(item => item.file === 'lean-toolchain')?.digest
      ? new TextDecoder('utf-8', { fatal: true }).decode(readMathFile(path.join(projectRoot, 'lean-toolchain'), 1024 * 1024).bytes).trim() : null;
    return { projectRoot, binding: { ...binding, roots }, selected, toolchain };
  }
  return { manifest, candidates, prepare };
}

/** Apply only explicitly supplied, exactly bound advisory data; missing coverage stays unknown. */
export function applyKnowledgeEnrichment(candidates: readonly KnowledgeCandidate[], value: unknown,
  options: { manifestFile: string }): KnowledgeCandidate[] {
  const sidecar = validateKnowledgeEnrichment(value), current = acceptedSnapshot(options.manifestFile);
  if (!equal(sidecar.manifest, current.manifest)) throw mismatch();
  const bound = new Map<string, { record: EnrichmentRecord; root: EnrichmentRecord['collection']['roots'][number] }>();
  for (const record of sidecar.records) {
    const prepared = current.prepare(record.problemId), { collection: _collection, ...binding } = record;
    if (!equal(binding, prepared.binding) || record.collection.identity.toolchain !== prepared.toolchain) throw mismatch();
    for (const root of record.collection.roots) bound.set(`${record.problemId}\0${root.file}\0${root.name}`, { record, root });
  }
  const baseline = new Map(current.candidates.map(candidate => [`${candidate.provenance.problemId}\0${candidate.file}\0${candidate.name}`, candidate]));
  const comparedFiles = new Map<KnowledgeCandidate['files'], Set<KnowledgeCandidate['files']>>();
  const artifactContents = new Map(sidecar.artifacts.map(item => [item.path, item.contentsBase64]));
  return candidates.map(candidate => {
    const key = `${candidate.provenance.problemId}\0${candidate.file}\0${candidate.name}`, original = baseline.get(key);
    if (!original || !equal(candidate.provenance, original.provenance) ||
        candidate.type !== original.type || candidate.typeKind !== original.typeKind || candidate.kind !== original.kind) throw mismatch();
    const paired = comparedFiles.get(candidate.files) ?? new Set<KnowledgeCandidate['files']>();
    if (!paired.has(original.files)) {
      if (!equal(candidate.files, original.files)) throw mismatch();
      paired.add(original.files); comparedFiles.set(candidate.files, paired);
    }
    const result = { ...candidate, provenance: { ...candidate.provenance } }, match = bound.get(key);
    if (!match) return result;
    const { record, root } = match, identity = record.collection.identity;
    const diagnosticsArtifact = root.artifacts.find(item => item.kind === 'diagnostics');
    const diagnostics = diagnosticsArtifact && JSON.parse(Buffer.from(artifactContents.get(diagnosticsArtifact.path)!, 'base64').toString('utf8')) as RetainedDiagnostics | undefined;
    if (root.status !== 'collected' || !root.fullType || !root.universes || !root.sourceDigest || !root.declarationDigest ||
        !root.queryDigest || !identity.environmentDigest || !identity.toolIdentity || !identity.toolchain ||
        !diagnostics?.sourceDigest || !diagnostics.environmentDigest ||
        !['lean', 'lake'].every(command => identity.tools.some(tool => tool.command === command)) ||
        !root.artifacts.some(item => item.kind === 'full-type') || !root.artifacts.some(item => item.kind === 'diagnostics')) return result;
    result.elaboration = knowledgeElaborationSchema.parse({ schema: 'theorem-os.knowledge-elaboration.v1', evidence: 'recorded-not-replayed',
      fullType: root.fullType, universes: [...root.universes], ...(root.statementContext ? { statementContext: structuredClone(root.statementContext) } : {}),
      omissions: [...root.omissions], enrichmentDigest: sidecar.digest, sourceDigest: root.sourceDigest,
      declarationDigest: root.declarationDigest, collectorDigest: identity.collector.digest, queryDigest: root.queryDigest,
      artifactsDigest: mathDigest(canonicalMathJson(root.artifacts)), environmentDigest: identity.environmentDigest,
      toolIdentity: identity.toolIdentity, ...(identity.sealedEnvironmentIdentity ? { sealedEnvironmentIdentity: identity.sealedEnvironmentIdentity } : {}) });
    result.provenance = { ...result.provenance, environmentDigest: identity.environmentDigest };
    if (root.references) result.dependencies = { ...result.dependencies, statement: structuredClone(root.references.statement),
      proof: structuredClone(root.references.proof), coverage: 'recorded' };
    return result;
  });
}

/** The explicit enrichment operation alone runs Lean; it grants no proof acceptance. */
export async function enrichAcceptedKnowledge(manifestFile: string, problemId: string,
  options: { env?: NodeJS.ProcessEnv; signal?: AbortSignal; timeoutMs?: number; retryFile?: string } = {}): Promise<KnowledgeEnrichment> {
  options.signal?.throwIfAborted();
  const initial = acceptedSnapshot(manifestFile), prepared = initial.prepare(problemId);
  if (!prepared.binding.roots.length) throw new Error('math_knowledge_enrichment_no_roots');
  let queryIndices = prepared.binding.roots.map((_, index) => index);
  if (options.retryFile !== undefined) {
    const previous = readKnowledgeEnrichment(options.retryFile), record = previous.records.find(record => record.problemId === problemId);
    if (!equal(previous.manifest, initial.manifest) || !record) throw mismatch();
    const { collection, ...binding } = record;
    if (!equal(binding, prepared.binding) || collection.identity.toolchain !== prepared.toolchain) throw mismatch();
    const previousRoots = new Map(collection.roots.map(root => [root.id, root]));
    queryIndices = queryIndices.filter(index => previousRoots.get(prepared.binding.roots[index]!.id)?.status !== 'collected');
    if (!queryIndices.length) throw new Error('math_knowledge_enrichment_no_retry_roots');
  }
  const roots = queryIndices.map(index => prepared.binding.roots[index]!);
  const collected = await collectLeanKnowledgeEnrichment({ projectRoot: prepared.projectRoot,
    roots: roots.map(({ id, name, file }) => ({ id, name, file })),
    ...(options.retryFile === undefined ? {} : { queryIndices }),
    env: options.env, signal: options.signal, timeoutMs: options.timeoutMs ?? Infinity });
  options.signal?.throwIfAborted();
  if (collected.roots.some(root => !roots.some(requested => requested.id === root.id))) throw mismatch();
  if (collected.identity.toolchain !== prepared.toolchain) throw mismatch();
  const after = acceptedSnapshot(manifestFile), current = after.prepare(problemId);
  if (!equal(initial.manifest, after.manifest) || !equal(prepared.binding, current.binding)) throw mismatch();
  const artifacts = new Map<string, KnowledgeEnrichment['artifacts'][number]>();
  for (const root of collected.roots) for (const item of root.artifacts) {
    if (!relative(item.path) || !/^\.lake\/knowledge-enrichment\/[^/]+\/.+/u.test(item.path)) throw mismatch();
    const absolute = path.join(prepared.projectRoot, item.path); assertMathCanonicalPath(absolute);
    const bytes = readMathFile(absolute, 16 * 1024 * 1024).bytes;
    if (bytes.length !== item.bytes || mathDigest(bytes) !== item.digest) throw new Error('math_knowledge_enrichment_artifact_changed');
    const embedded = { path: item.path, digest: item.digest, bytes: item.bytes, contentsBase64: bytes.toString('base64') };
    const previous = artifacts.get(item.path);
    if (previous && !equal(previous, embedded)) throw mismatch();
    artifacts.set(item.path, embedded);
  }
  const payload = { schema: 'theorem-os.knowledge-enrichment.v1' as const, evidence: 'recorded-not-replayed' as const,
    requiresFreshCheck: true as const, manifest: initial.manifest,
    records: [{ ...prepared.binding, collection: collected }], artifacts: [...artifacts.values()].sort((a, b) => a.path.localeCompare(b.path)) };
  return validateKnowledgeEnrichment({ ...payload, digest: mathDigest(canonicalMathJson(payload)) });
}
