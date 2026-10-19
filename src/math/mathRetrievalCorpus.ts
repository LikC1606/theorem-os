import fs from 'node:fs';
import crypto from 'node:crypto';
import path from 'node:path';
import { z } from 'zod';
import { captureInstalledLeanSources, INSTALLED_CORPUS_POLICY, MAX_INSTALLED_SOURCE_FILE_BYTES, isAllowedInstalledLeanSource } from "./installedPackageSearch";
import { canonicalMathJson, mathDigest, mathFileIdentity, readMathText } from "./mathRuntimeIo";
import { assertMathCanonicalPath } from './paths';
import { inspectLeanDeclarations } from './leanSource';
import { maskLeanCommentsAndStrings, leanScopeCommands, leanScopeNamespace, updateLeanScopes, type LeanScope } from './leanSyntax';
const MAX_FILE_BYTES = MAX_INSTALLED_SOURCE_FILE_BYTES;
const digestSchema = z.string().regex(/^[0-9a-f]{64}$/u);
const relativeFileSchema = z
  .string()
  .min(1)
  .max(1024)
  .refine(
    (value) =>
      !value.includes('\\') &&
      !path.posix.isAbsolute(value) &&
      value.split('/').every((part) => part !== '' && part !== '.' && part !== '..')
  );
const identitySchema = z
  .object({
    path: relativeFileSchema,
    sha256: digestSchema,
    bytes: z.number().int().nonnegative().max(MAX_FILE_BYTES),
  })
  .strict();
const corpusSchema = z
  .object({
    schema: z.literal('deepscientist.math.retrieval-corpus.v1'),
    algorithm: z.literal('installed-lexical-v1-codepoint'),
    originSha256: digestSchema.optional(),
    projectSubdirectory: relativeFileSchema.optional(),
    packageSourceRoot: z
      .string()
      .refine((value) => path.isAbsolute(value))
      .optional(),
    implementation: z
      .object({
        sha256: digestSchema,
        bytes: z
          .number()
          .int()
          .positive()
          .max(256 * 1024 * 1024),
      })
      .strict()
      .optional(),
    policy: z
      .unknown()
      .refine(
        (value) => canonicalMathJson(value) === canonicalMathJson(INSTALLED_CORPUS_POLICY),
        'math_corpus_policy_changed'
      ),
    scopes: z.array(z.string().min(1).max(128)).min(1).max(2),
    environment: z
      .array(z.object({ path: relativeFileSchema, identity: identitySchema.nullable() }).strict())
      .min(2)
      .max(9),
    sources: z
      .array(
        z
          .object({
            identity: identitySchema,
            packageName: z.string().min(1).max(256),
            packageRevision: z.string().max(256).optional(),
            sourceModule: z.string().min(1).max(1024),
          })
          .strict()
      )
      .min(1),
  })
  .strict();

export type MathRetrievalCorpus = z.infer<typeof corpusSchema>;

const sourceCache = new Map<string, { identity: string; bytes: Buffer; sha256: string }>();
let sourceCacheBytes = 0;
const MAX_SOURCE_CACHE_BYTES = 64 * 1024 * 1024;

function readSource(root: string, relative: string) {
  relativeFileSchema.parse(relative);
  const file = path.join(fs.realpathSync(root), relative);
  if (fs.realpathSync(file) !== file) throw new Error('math_corpus_symlink');
  const fd = fs.openSync(file, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK);
  try {
    const before = fs.fstatSync(fd, { bigint: true });
    if (!before.isFile() || before.size > BigInt(MAX_FILE_BYTES)) throw new Error('math_corpus_invalid_file');
    const stamp = mathFileIdentity(before), previous = sourceCache.get(file);
    if (previous?.identity === stamp && mathFileIdentity(fs.lstatSync(file, { bigint: true })) === stamp) {
      return previous;
    }
    const buffer = Buffer.alloc(Number(before.size) + 1);
    let length = 0;
    while (length < buffer.length) {
      const count = fs.readSync(fd, buffer, length, buffer.length - length, length);
      if (count === 0) break;
      length += count;
    }
    if (length > MAX_FILE_BYTES) throw new Error('math_corpus_invalid_file');
    const bytes = buffer.subarray(0, length);
    const after = fs.fstatSync(fd, { bigint: true });
    const current = fs.lstatSync(file, { bigint: true });
    if (
      stamp !== mathFileIdentity(after) || stamp !== mathFileIdentity(current) ||
      fs.realpathSync(file) !== file
    ) {
      throw new Error('math_corpus_file_changed');
    }
    if (previous) { sourceCacheBytes -= previous.bytes.length; sourceCache.delete(file); }
    const source = { identity: stamp, bytes, sha256: mathDigest(bytes) };
    // Sequential scans larger than the budget must not evict every cached file on each pass.
    if (sourceCacheBytes + bytes.length <= MAX_SOURCE_CACHE_BYTES && sourceCache.size < 32768) {
      sourceCache.set(file, source); sourceCacheBytes += bytes.length;
    }
    return source;
  } finally {
    fs.closeSync(fd);
  }
}

const identity = (relative: string, bytes: Buffer, sha256 = mathDigest(bytes)) => ({
  path: relative,
  bytes: bytes.length,
  sha256,
});
const compare = (a: string, b: string): number => (a < b ? -1 : a > b ? 1 : 0);

function environmentIdentity(root: string, relative: string) {
  try {
    const source = readSource(root, relative);
    return identity(relative, source.bytes, source.sha256);
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code === 'ENOENT') return null;
    throw error;
  }
}

const packagePrefix = '.lake/packages/';

function sourceLocation(projectRoot: string, corpus: Pick<MathRetrievalCorpus, 'packageSourceRoot'>, relative: string) {
  if (!relative.startsWith(packagePrefix)) return { root: projectRoot, relative };
  const lakeRoot = path.join(projectRoot, '.lake');
  if (!corpus.packageSourceRoot && fs.realpathSync(lakeRoot) !== lakeRoot) throw new Error('math_corpus_symlink');
  // Only the packages entry may point to a shared cache; reads below reject links inside it.
  const packageRoot = corpus.packageSourceRoot || fs.realpathSync(path.join(lakeRoot, 'packages'));
  if (fs.realpathSync(packageRoot) !== packageRoot)
    throw new Error('math_corpus_package_root_changed');
  return { root: packageRoot, relative: relative.slice(packagePrefix.length) };
}

export async function createMathRetrievalCorpus(root: string, scopes: readonly string[]): Promise<MathRetrievalCorpus> {
  const sources = await captureInstalledLeanSources(root, scopes);
  const environmentPaths = new Set(['lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'lakefile.lean']);
  for (const source of sources) {
    const packageRoot = source.packageRoot!;
    environmentPaths.add(`${packageRoot}/lakefile.toml`);
    environmentPaths.add(`${packageRoot}/lakefile.lean`);
  }
  const corpus = corpusSchema.parse({
    schema: 'deepscientist.math.retrieval-corpus.v1',
    algorithm: 'installed-lexical-v1-codepoint',
    policy: INSTALLED_CORPUS_POLICY,
    scopes: [...scopes],
    environment: [...environmentPaths]
      .toSorted(compare)
      .map((file) => {
        const location = sourceLocation(fs.realpathSync(root), {}, file);
        const actual = environmentIdentity(location.root, location.relative);
        return { path: file, identity: actual ? { ...actual, path: file } : null };
      }),
    sources: sources
      .map((source) => ({
        identity: identity(source.sourceFile, Buffer.from(source.source, 'utf8')),
        packageName: source.packageName,
        packageRevision: source.packageRevision,
        sourceModule: source.sourceModule,
      }))
      .toSorted((a, b) => compare(a.identity.path, b.identity.path)),
  });
  // Re-capture at publication to detect changes in package metadata or file selection during creation.
  const recaptured = await captureInstalledLeanSources(root, scopes);
  if (recaptured.length !== sources.length || recaptured.some((source, index) => {
    const original = sources[index]!;
    return source.packageName !== original.packageName || source.packageRevision !== original.packageRevision ||
      source.packageRoot !== original.packageRoot || source.sourceModule !== original.sourceModule ||
      source.sourceFile !== original.sourceFile || source.source !== original.source;
  })) {
    throw new Error('math_corpus_capture_changed');
  }
  // Re-capture already checked every source's path and stable bytes. Validate that
  // snapshot and current environment without a third full source read.
  verifyMathRetrievalCorpusWithVisitor(root, corpus, undefined, new Map(recaptured.map(source => [source.sourceFile, source.source])));
  return corpus;
}

type VerifiedMathRetrievalSource = Readonly<{
  sourceFile: string;
  sourceModule: string;
  packageName: string;
  packageRevision?: string;
  source: string;
  sha256: string;
}>;

/** Verify every frozen source; an optional visitor avoids retaining the full corpus in memory. */
function verifyMathRetrievalCorpusWithVisitor(
  root: string,
  value: unknown,
  visit?: (source: VerifiedMathRetrievalSource) => void,
  capturedSources?: ReadonlyMap<string, string>
) {
  const corpus = corpusSchema.parse(value);
  const projectRoot = path.join(fs.realpathSync(root), corpus.projectSubdirectory ?? '');
  if (fs.realpathSync(projectRoot) !== projectRoot) throw new Error('math_corpus_project_path_invalid');
  if (
    new Set(corpus.sources.map((s) => s.identity.path)).size !== corpus.sources.length ||
    new Set(corpus.scopes).size !== corpus.scopes.length ||
    new Set(corpus.environment.map((f) => f.path)).size !== corpus.environment.length
  ) {
    throw new Error('math_corpus_duplicate_entry');
  }
  for (const required of ['lean-toolchain', 'lake-manifest.json']) {
    if (!corpus.environment.find((entry) => entry.path === required)?.identity)
      throw new Error('math_corpus_environment_missing');
  }
  if (
    corpus.packageSourceRoot &&
    !corpus.environment.find((entry) => entry.path === '.lake/package-overrides.json')?.identity
  )
    throw new Error('math_corpus_environment_missing');
  for (const entry of corpus.environment) {
    const location = sourceLocation(projectRoot, corpus, entry.path);
    const actual = environmentIdentity(location.root, location.relative);
    if (canonicalMathJson(actual ? { ...actual, path: entry.path } : null) !== canonicalMathJson(entry.identity)) {
      throw new Error('math_corpus_environment_changed');
    }
  }
  const decoder = new TextDecoder('utf-8', { fatal: true });
  for (const entry of corpus.sources) {
    if (!entry.identity.path.startsWith('.lake/packages/')) throw new Error('math_corpus_source_outside_packages');
    if (!isAllowedInstalledLeanSource(entry.identity.path.slice('.lake/packages/'.length)))
      throw new Error('math_corpus_source_excluded');
    const location = sourceLocation(projectRoot, corpus, entry.identity.path);
    const captured = capturedSources?.get(entry.identity.path);
    const bytesFromCapture = captured === undefined ? undefined : Buffer.from(captured, 'utf8');
    const { bytes, sha256 } = bytesFromCapture
      ? { bytes: bytesFromCapture, sha256: mathDigest(bytesFromCapture) }
      : readSource(location.root, location.relative);
    if (bytes.length !== entry.identity.bytes || sha256 !== entry.identity.sha256)
      throw new Error('math_corpus_source_changed');
    const source = captured ?? decoder.decode(bytes);
    visit?.({
      sourceFile: corpus.packageSourceRoot
        ? path.join(location.root, location.relative)
        : corpus.projectSubdirectory
          ? `${corpus.projectSubdirectory}/${entry.identity.path}`
          : entry.identity.path,
      sourceModule: entry.sourceModule,
      packageName: entry.packageName,
      packageRevision: entry.packageRevision,
      source,
      sha256,
    });
  }
  return corpus;
}

export function assertMathRetrievalCorpus(root: string, value: unknown): void {
  verifyMathRetrievalCorpusWithVisitor(root, value);
}

/** Track ordinary source scopes; names remain lookup hints until checked in Lean. */
function searchableDeclarations(source: string) {
  const clean = maskLeanCommentsAndStrings(source);
  const commands = leanScopeCommands(clean);
  const scopes: LeanScope[] = [];
  const context: string[][] = [[]];
  let command = commands.next();
  let sourceLine = 1;
  let newline = source.indexOf('\n');
  return inspectLeanDeclarations(source).map(declaration => {
    while (!command.done && command.value.index < declaration.startOffset) {
      const [, kind, rest] = command.value;
      const name = rest?.trim();
      if (kind === 'namespace' || kind === 'section') { updateLeanScopes(scopes, kind, name); context.push([]); }
      else if (kind === 'end') { updateLeanScopes(scopes, kind, name); if (context.length > 1) context.pop(); }
      else if (kind === 'variable' || (kind === 'open' && name && !/\bin\s*$/u.test(name))) {
        let text = command.value[0].trim();
        let end = command.value.index + command.value[0].length;
        const balance = (s: string) => [...s].reduce((n, c) => n + ('([{'.includes(c) ? 1 : ')]}'.includes(c) ? -1 : 0), 0);
        while (kind === 'variable' && balance(text) > 0 && end < declaration.startOffset) {
          const next = clean.indexOf('\n', end + 1);
          const finish = Math.min(next < 0 ? clean.length : next, declaration.startOffset);
          text += clean.slice(end, finish); end = finish;
        }
        const sectionContext = context.at(-1)!;
        sectionContext.push(text.trim());
      }
      command = commands.next();
    }
    while (newline >= 0 && newline < declaration.startOffset) {
      sourceLine++;
      newline = source.indexOf('\n', newline + 1);
    }
    const qualifiedName = declaration.name.startsWith('_root_.') ? declaration.name.slice('_root_.'.length) :
      [leanScopeNamespace(scopes), declaration.name].filter(Boolean).join('.');
    const sourceContext = context.flat().join('\n');
    return { ...declaration, qualifiedName, sourceLine, sourceContext: sourceContext.slice(0, 2000),
      contextTruncated: sourceContext.length > 2000 };
  });
}

export type MathRetrievalCache = Readonly<{ directory: string; implementation: string; secret: string }>;

/** Cache parsed hints only; current frozen source verification always runs first. */
function indexedDeclarations(source: VerifiedMathRetrievalSource, cache?: MathRetrievalCache) {
  if (!cache) return searchableDeclarations(source.source);
  const key = mathDigest(`math-retrieval-index.v1\0${cache.implementation}\0${source.sha256}`);
  const file = path.join(cache.directory, `${key}.json`);
  const signature = (payload: string) => crypto.createHmac('sha256', cache.secret).update(key).update('\0').update(payload).digest('hex');
  try {
    assertMathCanonicalPath(cache.directory);
    const saved = JSON.parse(readMathText(file, 32 * 1024 * 1024));
    if (typeof saved.payload === 'string' && saved.signature === signature(saved.payload))
      return JSON.parse(saved.payload) as ReturnType<typeof searchableDeclarations>;
  } catch { /* Missing or changed caches are rebuilt from verified source. */ }
  const declarations = searchableDeclarations(source.source);
  const temporary = path.join(cache.directory, `${key}.${crypto.randomUUID()}.tmp`);
  try {
    fs.mkdirSync(cache.directory, { recursive: true, mode: 0o700 });
    assertMathCanonicalPath(cache.directory);
    const payload = JSON.stringify(declarations);
    const contents = JSON.stringify({ payload, signature: signature(payload) });
    if (Buffer.byteLength(contents) <= 32 * 1024 * 1024) {
      fs.writeFileSync(temporary, contents, { flag: 'wx', mode: 0o600 });
      fs.renameSync(temporary, file);
    }
  } catch { /* Cache availability cannot change lookup results. */ }
  finally { try { fs.rmSync(temporary, { force: true }); } catch {} }
  return declarations;
}

/** Surface syntax ranks lookup hints; Lean still decides whether a premise applies. */
function goalRanker(goal: string) {
  const relations: Record<string, string> = { '=': 'Eq', '≠': 'Ne', '<': 'LT.lt', '>': 'GT.gt', '≤': 'LE.le', '≥': 'GE.ge',
    '<=': 'LE.le', '>=': 'GE.ge', '∈': 'Membership.mem', '∧': 'And', '∨': 'Or', '↔': 'Iff', '¬': 'Not' };
  const aliases: Record<string, string> = { 'ℕ': 'Nat', 'ℤ': 'Int', 'ℚ': 'Rat', 'ℝ': 'Real', 'ℂ': 'Complex' };
  const identifiers = /[\p{L}_][\p{L}\p{M}\p{N}_'.]*/gu;
  const topLevel = (tokens: readonly string[]) => {
    const indexes: number[] = [];
    let depth = 0;
    for (const [index, token] of tokens.entries()) {
      if ('([{'.includes(token)) { if (depth === 0) indexes.push(index); depth++; }
      else if (')]}'.includes(token)) { depth--; if (depth === 0) indexes.push(index); }
      else if (depth === 0) indexes.push(index);
    }
    return indexes;
  };
  const shape = (source: string, context = '', declaration = false) => {
    const clean = maskLeanCommentsAndStrings(source);
    const scope = context ? `${context}\n${clean}` : clean;
    const bound = new Set<string>();
    for (const match of scope.matchAll(/(?:^|[\n({∀∃])\s*([\p{L}\p{M}\p{N}_'\s]+?)\s*:/gu))
      for (const name of match[1].match(identifiers) ?? []) bound.add(name);
    for (const match of scope.matchAll(/(?:[∀∃]|\bforall)\s+([\p{L}\p{M}\p{N}_'\s]+?)\s*,/gu))
      for (const name of match[1].match(identifiers) ?? []) bound.add(name);
    const marker = Math.max(clean.lastIndexOf('⊢'), clean.lastIndexOf('|-'));
    const target = marker < 0 ? clean : clean.slice(marker + (clean[marker] === '⊢' ? 1 : 2));
    let tokens: string[] = target.match(/[\p{L}_][\p{L}\p{M}\p{N}_'.]*|->|<=|>=|\S/gu) ?? [];
    if (declaration) {
      const colon = topLevel(tokens).find(index => tokens[index] === ':');
      tokens = colon === undefined ? [] : tokens.slice(colon + 1);
    }
    let head: string | undefined;
    while (tokens.length) {
      const indexes = topLevel(tokens);
      if (tokens[0] === '(' && tokens.at(-1) === ')' && indexes.length === 2) {
        tokens = tokens.slice(1, -1);
        continue;
      }
      if (tokens[0] === '∃') { head = 'Exists'; break; }
      if (tokens[0] === '∀' || tokens[0] === 'forall') {
        const comma = indexes.find(index => tokens[index] === ',');
        if (comma === undefined) break;
        tokens = tokens.slice(comma + 1);
        continue;
      }
      const outer = indexes.map(index => tokens[index]);
      if (outer.includes('↔')) { head = 'Iff'; break; }
      const arrow = indexes.find(index => tokens[index] === '→' || tokens[index] === '->');
      if (arrow !== undefined) { tokens = tokens.slice(arrow + 1); continue; }
      const connective = ['∨', '∧', '¬'].find(token => outer.includes(token));
      head = (connective ? relations[connective] : outer.map(token => relations[token]).find(Boolean)) ??
        outer.find(token => /^[\p{L}_]/u.test(token) && !bound.has(token));
      break;
    }
    const terms = new Set((scope.match(identifiers) ?? []).filter(token => !bound.has(token) &&
      !['variable', 'open', 'scoped', 'Type', 'Prop', 'Sort', 'forall'].includes(token))
      .flatMap(token => (aliases[token] ?? token).split('.')));
    return { head, terms };
  };
  const target = shape(goal);
  return (header: string, context: string) => {
    const candidate = shape(header.slice(0, 4000), context, true);
    // Keep this bonus below the exact-name bonus; local variable names add no relevance.
    return (target.head && target.head === candidate.head ? 8 : 0) +
      Math.min(8, [...target.terms].filter(term => candidate.terms.has(term)).length);
  };
}

/** Source headers are lookup hints, not closed Lean types or proof evidence. */
export function searchMathRetrievalCorpus(root: string, value: unknown, query: string, limit = 15, goal?: string, cache?: MathRetrievalCache) {
  return searchMathRetrievalCorpusBatch(root, value, [query], limit, goal, cache).queries[0]!;
}

/** Verify and parse the installed library once for several independent lookups. */
export function searchMathRetrievalCorpusBatch(root: string, value: unknown, queries: readonly string[], limit = 15, goal?: string, cache?: MathRetrievalCache) {
  if (!queries.length || queries.length > 8) throw new Error('math_search_invalid_queries');
  if (goal !== undefined && (!goal.trim() || goal.includes('\0') || Buffer.byteLength(goal) > 16_000))
    throw new Error('math_search_invalid_goal');
  const rankGoal = goal === undefined ? undefined : goalRanker(goal);
  type Match = { name: string; qualifiedName: string; sourceLine: number; kind: string; sourceHeader: string; headerTruncated: boolean;
    sourceContext: string; contextTruncated: boolean; sourceModule: string; sourceFile: string; packageName: string; score: number };
  const compareMatches = (a: Match, b: Match) => b.score - a.score || compare(a.name, b.name) ||
    compare(a.sourceModule, b.sourceModule) || compare(a.sourceFile, b.sourceFile);
  const parsed = queries.map(query => {
    const normalized = query.toLowerCase();
    const terms = [...new Set(normalized.match(/[\p{L}\p{M}\p{N}]+/gu) || [])];
    if (!terms.length || Buffer.byteLength(query) > 256) throw new Error('math_search_invalid_query');
    return { query, terms, exact: normalized.trim(), totalMatches: 0, matches: [] as Match[] };
  });
  if (!Number.isSafeInteger(limit) || limit < 1 || limit > INSTALLED_CORPUS_POLICY.maxResultLimit)
    throw new Error('math_search_invalid_limit');
  // All sources remain verified; only plausible matches need declaration parsing.
  verifyMathRetrievalCorpusWithVisitor(root, value, source => {
    const text = source.source.toLowerCase();
    const module = source.sourceModule.toLowerCase();
    const candidates = parsed.filter(({ terms }) => terms.every(term => text.includes(term) || module.includes(term)));
    if (!candidates.length) return;
    // Normalize each declaration once, and release this file's headers after all candidate queries.
    for (const declaration of indexedDeclarations(source, cache)) {
      const name = declaration.qualifiedName.toLowerCase();
      const header = declaration.declarationType.toLowerCase();
      const context = declaration.sourceContext.toLowerCase();
      const localName = declaration.name.toLowerCase();
      let goalScore: number | undefined;
      for (const candidate of candidates) {
        const { terms, exact, matches } = candidate;
        if (!terms.every(term => name.includes(term) || header.includes(term) || context.includes(term) || module.includes(term))) continue;
        candidate.totalMatches++;
        goalScore ??= rankGoal?.(declaration.declarationType.slice(declaration.name.length), declaration.sourceContext) ?? 0;
        const score = (name === exact || localName === exact ? 20 : 0) +
          terms.reduce((sum, term) => sum + (name.includes(term) ? 4 : header.includes(term) ? 2 : 1), 0) + goalScore;
        matches.push({ name: declaration.name, qualifiedName: declaration.qualifiedName,
          sourceLine: declaration.sourceLine, kind: declaration.kind, sourceHeader: declaration.declarationType.slice(0, 800),
          headerTruncated: declaration.declarationType.length > 800, sourceContext: declaration.sourceContext,
          contextTruncated: declaration.contextTruncated, sourceModule: source.sourceModule, sourceFile: source.sourceFile,
          packageName: source.packageName, score });
        if (matches.length === 2 * limit) { matches.sort(compareMatches); matches.length = limit; }
      }
    }
  });
  const budget = Math.floor((24_000 - 64) / queries.length);
  return { queries: parsed.map(({ query, totalMatches, matches }) => {
  const result = { query, totalMatches, truncated: false, results: [] as Match[] };
  matches.sort(compareMatches);
  for (const match of matches.slice(0, limit)) {
    result.results.push(match);
    const fits = () => Buffer.byteLength(JSON.stringify(result)) <= budget;
    // Keep the first declaration useful when multibyte context exceeds its query budget.
    if (result.results.length === 1) {
      while (!fits() && match.sourceContext.length) {
        match.sourceContext = match.sourceContext.slice(0, Math.floor(match.sourceContext.length / 2));
        match.contextTruncated = true;
      }
      while (!fits() && match.sourceHeader.length) {
        match.sourceHeader = match.sourceHeader.slice(0, Math.floor(match.sourceHeader.length / 2));
        match.headerTruncated = true;
      }
    }
    if (!fits()) {
      result.results.pop();
      break;
    }
  }
  result.truncated = result.results.length < totalMatches;
  return result;
  }) };
}
