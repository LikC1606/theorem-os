import { createHash } from 'node:crypto';
import { z } from 'zod';
import { bootstrapLeanTask, LEAN_TASK_SOURCE_MAX_BYTES, type LeanTaskReceipt } from './leanTask';
import { getLeanTaskEnvironment } from './leanTaskEnvironment';
import { inspectLeanDeclarationRegions, inspectScopedLeanDeclarations } from './leanSource';
import { maskLeanComments, maskLeanCommentsAndStrings } from './leanSyntax';
import { mathGitBytes, mathGitText } from './mathGit';
import { canonicalMathJson, mathDigest } from './mathRuntimeIo';

export const PUTNAM_BENCH_SOURCE_COMMIT = '13d042960189f55d748048317c24064a0e2215ea';
export const PUTNAM_BENCH_REPOSITORY_URL = 'https://github.com/trishullab/PutnamBench.git';
export const DEFAULT_PUTNAM_SAMPLE_SEED = 'theorem-os-putnam-pilot-v1';
const sampleAlgorithm = 'sha256-seed-nul-id-v1' as const;
const problemId = /^putnam_[0-9]{4}_[ab][1-6]$/u;
const keyword = (words: string) => new RegExp(`(?<![\\p{L}\\p{M}\\p{N}_'.])(?:${words})(?![\\p{L}\\p{M}\\p{N}_'.])`, 'gu');

export type PutnamBenchProblem = Readonly<{
  id: string; sourceRelativePath: string; sourceSha256: string; source: string; theoremNames: string[];
}>;
export type PutnamBenchCatalog = Readonly<{
  repositoryUrl: string; sourceCommit: string; toolchain: string; mathlibRevision: string; environmentDigest: string;
  problems: PutnamBenchProblem[];
  excluded: { id: string; sourceRelativePath: string; reason: string }[];
  excludedCounts: Record<string, number>;
}>;
export type PutnamBenchSelection = Readonly<{
  algorithm: typeof sampleAlgorithm; seed: string; count: number; poolDigest: string; eligibleCount: number;
  problems: PutnamBenchProblem[];
}>;
type TreeEntry = { mode: string; oid: string; path: string };
class IneligibleProblem extends Error {}

const gitOptions = { timeout: 30_000, maxBuffer: 1024 * 1024, errorMessage: 'putnam_bench_source_unavailable' };
function readTree(repository: string): Map<string, TreeEntry> {
  if (mathGitText(repository, ['--no-replace-objects', 'rev-parse', '--verify', `${PUTNAM_BENCH_SOURCE_COMMIT}^{commit}`], gitOptions)
      !== PUTNAM_BENCH_SOURCE_COMMIT) throw new Error('putnam_bench_source_commit_mismatch');
  const tree = mathGitBytes(repository, ['--no-replace-objects', 'ls-tree', '-r', '-z', PUTNAM_BENCH_SOURCE_COMMIT,
    '--', 'lean4/lean-toolchain', 'lean4/lake-manifest.json', 'lean4/lakefile.lean', 'lean4/src'], gitOptions);
  const entries = new Map<string, TreeEntry>();
  for (const line of new TextDecoder('utf-8', { fatal: true }).decode(tree).split('\0').filter(Boolean)) {
    const parsed = /^([0-9]{6}) (?:blob|commit) ([0-9a-f]{40})\t([^\n]+)$/u.exec(line);
    if (!parsed || entries.has(parsed[3])) throw new Error('putnam_bench_tree_invalid');
    entries.set(parsed[3], { mode: parsed[1], oid: parsed[2], path: parsed[3] });
  }
  return entries;
}

function readBlob(repository: string, entry: TreeEntry | undefined, limit = LEAN_TASK_SOURCE_MAX_BYTES): { source: string; sha256: string } {
  if (!entry || entry.mode !== '100644') throw new Error('putnam_bench_file_mode_invalid');
  const bytes = mathGitBytes(repository, ['--no-replace-objects', 'cat-file', 'blob',
    `${PUTNAM_BENCH_SOURCE_COMMIT}:${entry.path}`], { ...gitOptions, maxBuffer: limit + 1 });
  if (bytes.length > limit) throw new Error('putnam_bench_source_too_large');
  const oid = createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex');
  if (oid !== entry.oid) throw new Error('putnam_bench_blob_identity_mismatch');
  const source = new TextDecoder('utf-8', { fatal: true, ignoreBOM: true }).decode(bytes);
  if (!Buffer.from(source, 'utf8').equals(bytes)) throw new Error('putnam_bench_source_encoding_invalid');
  return { source, sha256: mathDigest(bytes) };
}

const revision = z.string().regex(/^[0-9a-f]{40}$/u);
const packageSchema = z.object({ name: z.string(), url: z.string(), type: z.literal('git'), subDir: z.null(),
  scope: z.string(), rev: revision, manifestFile: z.literal('lake-manifest.json'), inputRev: z.string(),
  inherited: z.boolean(), configFile: z.enum(['lakefile.lean', 'lakefile.toml']) }).strict();
const manifestSchema = z.object({ version: z.string(), packagesDir: z.string(), packages: z.array(packageSchema),
  name: z.string(), lakeDir: z.string(), fixedToolchain: z.boolean() }).strict();
const normalizeGitUrl = (url: string) => url.replace(/\.git$/u, '');

function readEnvironment(repository: string, tree: Map<string, TreeEntry>) {
  const environment = getLeanTaskEnvironment('mathlib');
  const toolchain = readBlob(repository, tree.get('lean4/lean-toolchain')).source.trim();
  if (toolchain !== environment.toolchain) throw new Error('putnam_bench_toolchain_mismatch');
  let manifest: z.infer<typeof manifestSchema>;
  try { manifest = manifestSchema.parse(JSON.parse(readBlob(repository, tree.get('lean4/lake-manifest.json')).source)); }
  catch (error) {
    if (error instanceof z.ZodError || error instanceof SyntaxError) throw new Error('putnam_bench_dependencies_invalid');
    throw error;
  }
  const expected = manifestSchema.parse(JSON.parse(environment.files['lake-manifest.json']));
  if (manifest.version !== expected.version || manifest.packagesDir !== expected.packagesDir || manifest.lakeDir !== expected.lakeDir ||
      manifest.packages.length !== expected.packages.length || new Set(manifest.packages.map(item => item.name)).size !== manifest.packages.length)
    throw new Error('putnam_bench_dependencies_mismatch');
  for (const item of manifest.packages) {
    const reference = expected.packages.find(value => value.name === item.name);
    if (!reference || item.rev !== reference.rev || normalizeGitUrl(item.url) !== normalizeGitUrl(reference.url) ||
        item.inherited !== reference.inherited || item.configFile !== reference.configFile ||
        item.name !== 'mathlib' && (item.scope !== reference.scope || item.inputRev !== reference.inputRev))
      throw new Error('putnam_bench_dependencies_mismatch');
  }
  const lakefile = readBlob(repository, tree.get('lean4/lakefile.lean')).source;
  const requirements = [...maskLeanComments(lakefile).matchAll(
    /^require[ \t]+([A-Za-z_][A-Za-z0-9_]*)[ \t]+from[ \t]+git[ \t]+"([^"\r\n]+)"[ \t]+@[ \t]+"([^"\r\n]+)"[ \t]*$/gmu)];
  const root = manifest.packages.find(item => item.name === 'mathlib');
  if (!root || root.rev !== environment.mathlibRevision || requirements.length !== 1 || requirements[0][1] !== 'mathlib' ||
      normalizeGitUrl(requirements[0][2]) !== normalizeGitUrl(root.url) || requirements[0][3] !== root.inputRev ||
      [...maskLeanCommentsAndStrings(lakefile).matchAll(keyword('require'))].length !== 1)
    throw new Error('putnam_bench_dependencies_mismatch');
  return { toolchain, mathlibRevision: environment.mathlibRevision!, environmentDigest: environment.dependencyDigest };
}

function inspectProblem(id: string, entry: TreeEntry, source: string, sha256: string): PutnamBenchProblem {
  if (/[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]/u.test(source)) throw new IneligibleProblem('unsupported_source_encoding');
  const cleaned = maskLeanCommentsAndStrings(source);
  if (keyword('axiom|constant|sorryAx|unsafe|initialize|builtin_initialize|macro|elab|syntax|example').test(cleaned))
    throw new IneligibleProblem('unsupported_declaration');
  const declarations = inspectScopedLeanDeclarations(source), targets = declarations.filter(item => item.kind === 'theorem');
  if (targets.length !== 1 || targets[0].qualifiedName !== id || !/^theorem\b/u.test(cleaned.slice(targets[0].startOffset)))
    throw new IneligibleProblem('single_named_theorem_required');
  const keywords = [...cleaned.matchAll(keyword('theorem|lemma'))];
  if (keywords.length !== 1 || keywords[0].index !== targets[0].startOffset)
    throw new IneligibleProblem('unsupported_declaration');
  const names = declarations.map(item => item.name.split('.').at(-1));
  if (new Set(names).size !== names.length || declarations.length > 256) throw new IneligibleProblem('ambiguous_declarations');
  const regions = inspectLeanDeclarationRegions(source), target = regions.find(item => item.startOffset === targets[0].startOffset);
  if (!target) throw new IneligibleProblem('unsupported_proof_region');
  const holes = [...cleaned.matchAll(keyword('sorry|admit'))];
  if (!holes.length) throw new IneligibleProblem('proof_placeholder_required');
  const belongsToTarget = (offset: number) => offset >= target.bodyOffset && offset < target.endOffset;
  const placeholders = [...cleaned.matchAll(/(?<![\p{L}\p{M}\p{N}_'.])_(?![\p{L}\p{M}\p{N}_'.])|\?/gu)];
  for (const hole of [...holes, ...placeholders]) {
    if (belongsToTarget(hole.index)) continue;
    const owner = regions.findLast(region => region.startOffset <= hole.index);
    if (owner && declarations.find(item => item.startOffset === owner.startOffset)?.kind !== 'theorem')
      throw new IneligibleProblem('answer_definition_placeholder');
    if (hole.index >= target.bodyOffset) throw new IneligibleProblem('proof_region_not_editable');
    throw new IneligibleProblem('placeholder_in_statement');
  }
  return { id, sourceRelativePath: entry.path, sourceSha256: sha256, source, theoremNames: [targets[0].qualifiedName] };
}

/** Read only immutable Git blobs; checkout edits and solution metadata are never task inputs. */
export function readPutnamBenchCatalog(repositoryRoot: string): PutnamBenchCatalog {
  const tree = readTree(repositoryRoot), environment = readEnvironment(repositoryRoot, tree);
  const problems: PutnamBenchProblem[] = [], excluded: PutnamBenchCatalog['excluded'] = [], excludedCounts: Record<string, number> = {};
  for (const entry of [...tree.values()].sort((a, b) => a.path.localeCompare(b.path))) {
    const match = /^lean4\/src\/([^/]+)\.lean$/u.exec(entry.path);
    if (!match) continue;
    const id = match[1];
    let reason: string | undefined;
    if (!problemId.test(id)) reason = 'unsupported_problem_id';
    else if (entry.mode !== '100644') reason = 'non_regular_source';
    else {
      const { source, sha256 } = readBlob(repositoryRoot, entry);
      try { problems.push(inspectProblem(id, entry, source, sha256)); }
      catch (error) { if (error instanceof IneligibleProblem) reason = error.message; else throw error; }
    }
    if (reason) { excluded.push({ id, sourceRelativePath: entry.path, reason }); excludedCounts[reason] = (excludedCounts[reason] ?? 0) + 1; }
  }
  return { repositoryUrl: PUTNAM_BENCH_REPOSITORY_URL, sourceCommit: PUTNAM_BENCH_SOURCE_COMMIT, ...environment,
    problems, excluded, excludedCounts };
}

export function readPutnamBenchProblem(repositoryRoot: string, id: string): PutnamBenchProblem {
  if (!problemId.test(id)) throw new Error('putnam_bench_problem_id_invalid');
  const tree = readTree(repositoryRoot);
  readEnvironment(repositoryRoot, tree);
  const entry = tree.get(`lean4/src/${id}.lean`);
  if (!entry) throw new Error(`putnam_bench_problem_not_found:${id}`);
  const { source, sha256 } = readBlob(repositoryRoot, entry);
  try { return inspectProblem(id, entry, source, sha256); }
  catch (error) {
    if (error instanceof IneligibleProblem) throw new Error(`putnam_bench_problem_ineligible:${error.message}`);
    throw error;
  }
}

export function samplePutnamBench(catalog: PutnamBenchCatalog, count = 3, seed = DEFAULT_PUTNAM_SAMPLE_SEED): PutnamBenchSelection {
  if (!Number.isSafeInteger(count) || count < 1 || count > catalog.problems.length) throw new Error('putnam_bench_sample_count_invalid');
  if (typeof seed !== 'string' || !seed.length || Buffer.byteLength(seed, 'utf8') > 1024 || seed.includes('\0') ||
      Buffer.from(seed, 'utf8').toString('utf8') !== seed) throw new Error('putnam_bench_sample_seed_invalid');
  const pool = [...catalog.problems].sort((a, b) => a.id.localeCompare(b.id));
  if (new Set(pool.map(problem => problem.id)).size !== pool.length || pool.some(problem =>
    !problemId.test(problem.id) || problem.sourceRelativePath !== `lean4/src/${problem.id}.lean` ||
    mathDigest(problem.source) !== problem.sourceSha256 || canonicalMathJson(problem.theoremNames) !== canonicalMathJson([problem.id])))
    throw new Error('putnam_bench_catalog_invalid');
  const poolDigest = mathDigest(canonicalMathJson({ sourceCommit: catalog.sourceCommit, environmentDigest: catalog.environmentDigest,
    problems: pool.map(({ id, sourceRelativePath, sourceSha256 }) => ({ id, sourceRelativePath, sourceSha256 })) }));
  const ranked = pool.map(problem => ({ problem, rank: mathDigest(`${seed}\0${problem.id}`) }))
    .sort((a, b) => a.rank.localeCompare(b.rank) || a.problem.id.localeCompare(b.problem.id));
  return { algorithm: sampleAlgorithm, seed, count, poolDigest, eligibleCount: pool.length,
    problems: ranked.slice(0, count).map(item => item.problem) };
}

export function bootstrapPutnamBenchProblem(input: { repositoryRoot: string; problemId: string; workspaceRoot: string }): LeanTaskReceipt {
  const problem = readPutnamBenchProblem(input.repositoryRoot, input.problemId);
  return bootstrapLeanTask(input.workspaceRoot, { source: problem.source, environment: 'mathlib',
    task: `Prove PutnamBench problem ${problem.id}.\nSource: ${PUTNAM_BENCH_REPOSITORY_URL.replace(/\.git$/u, '')}/blob/${PUTNAM_BENCH_SOURCE_COMMIT}/${problem.sourceRelativePath}\nPreserve the original statement and frozen definitions. Complete only the proof.` });
}
