/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import fs from 'node:fs';
import path from 'node:path';
import { mathGitText, mathGitResult } from './mathGit';
import { mathDigest as sha256, readMathText } from './mathRuntimeIo';
import { assertMathCanonicalPath, isMathPathWithin, repositoryRelativePath } from './paths';
import { parse as parseToml } from 'smol-toml';

export const LEAN_EVAL_BENCHMARK_COMMIT = '38361be884302c7edce1908c4aef8296eb2cb27e' as const;
export const LEAN_EVAL_REPOSITORY_URL = 'https://github.com/leanprover/lean-eval' as const;
export const LEAN_EVAL_LEADERBOARD_URL =
  'https://leanprover.github.io/lean-eval-leaderboard/site-data/v2/groups/formalization-evaluation.json' as const;
export const LEAN_EVAL_CATALOG_SCHEMA = 'deepscientist.mathematics.lean-eval-catalog.v1' as const;

type JsonRecord = Record<string, unknown>;

export type LeanEvalCatalogCredit = Readonly<{
  problemId: string;
  statementRevision: number;
  canonicalModelId?: string;
  submitter?: string;
  acceptedAt?: string;
  firstSolve?: boolean;
}>;

export type LeanEvalCatalogHole = Readonly<{
  name: string;
  basename: string;
  kind: 'theorem' | 'definition' | 'instance' | 'unknown';
}>;

export type LeanEvalCatalogProblem = Readonly<{
  id: string;
  title: string;
  group: string;
  status: string;
  visible: boolean;
  statementRevision: number;
  tags: readonly string[];
  module: string;
  holes: readonly LeanEvalCatalogHole[];
  generatedPath: string;
  submitter?: string;
  source?: string;
  notes?: string;
  informalSolution?: string;
  activeV1: boolean;
  acceptedCreditCount: number;
  acceptedModelIds: readonly string[];
  zeroCredit: boolean;
  eligible: boolean;
  eligibilityReasons: readonly string[];
  selectionEvidence?: Readonly<{
    libraryReview: 'unreviewed';
    publicGapNotes: readonly Readonly<{ file: string; line: number; text: string }>[];
    publicSourceDigest: string;
  }>;
  catalogEvidence: Readonly<{
    benchmarkCommit: string;
    sourceFiles: readonly string[];
    generatedAt: number;
  }>;
}>;

export type LeanEvalCatalog = Readonly<{
  schema: typeof LEAN_EVAL_CATALOG_SCHEMA;
  repositoryUrl: typeof LEAN_EVAL_REPOSITORY_URL;
  benchmarkCommit: string;
  setId: string;
  catalogHash: string;
  generatedAt: number;
  problems: readonly LeanEvalCatalogProblem[];
  credits: readonly LeanEvalCatalogCredit[];
}>;

export type LeanEvalCatalogReadOptions = Readonly<{
  repositoryRoot: string;
  benchmarkCommit?: string;
  setId?: string;
  credits?: readonly LeanEvalCatalogCredit[] | readonly JsonRecord[];
  generatedAt?: number;
  verifyGitCommit?: boolean;
}>;

type FetchLike = (input: string | URL | Request, init?: RequestInit) => Promise<Response>;
let leaderboardCache:
  | Readonly<{
      expiresAt: number;
      value: Readonly<{
        credits: readonly LeanEvalCatalogCredit[];
        generatedAt: number;
        sourceUrl: typeof LEAN_EVAL_LEADERBOARD_URL;
      }>;
    }>
  | undefined;

const text = (value: unknown): string | undefined =>
  typeof value === 'string' && value.trim() ? value.trim() : undefined;
const record = (value: unknown): JsonRecord | undefined =>
  value !== null && typeof value === 'object' && !Array.isArray(value) ? (value as JsonRecord) : undefined;
const stringList = (value: unknown): readonly string[] =>
  Array.isArray(value) ? Object.freeze(value.flatMap((item) => (text(item) ? [text(item)!] : []))) : Object.freeze([]);
/** `{ [key]: trimmed text }` when the value is non-blank text, otherwise no field. */
const optionalText = <Key extends string>(key: Key, value: unknown): { [K in Key]?: string } =>
  text(value) ? { [key]: text(value)! } as { [K in Key]: string } : {};
const positiveInt = (value: unknown, fallback = 1): number =>
  typeof value === 'number' && Number.isSafeInteger(value) && value > 0 ? value : fallback;
const safeRelativePath = (value: string, field: string): string => {
  const normalized = repositoryRelativePath(value.trim());
  if (!normalized) throw new Error(`LeanEval catalog ${field} must be repository-relative`);
  return normalized;
};

const assertNoSymlinkPath = (root: string, relativePath: string): void => {
  const resolvedRoot = path.resolve(root);
  const absolute = path.resolve(resolvedRoot, relativePath);
  if (!isMathPathWithin(resolvedRoot, absolute)) {
    throw new Error(`LeanEval catalog path escapes the repository: ${relativePath}`);
  }
  try { assertMathCanonicalPath(absolute); }
  catch { throw new Error(`LeanEval catalog path must not traverse a symbolic link: ${relativePath}`); }
};

const readFile = (root: string, relativePath: string): string => {
  assertNoSymlinkPath(root, relativePath);
  const absolute = path.join(root, relativePath);
  return readMathText(absolute, 16 * 1024 * 1024);
};

const gitText = (root: string, args: readonly string[]) => mathGitText(root, args, { maxBuffer: 2 * 1024 * 1024 });

const assertCatalogSourceIntegrity = (root: string, benchmarkCommit: string, files: readonly string[]): void => {
  const dirty = mathGitResult(root, ['diff', '--quiet', benchmarkCommit, '--', ...files], { maxBuffer: 2 * 1024 * 1024 });
  if (dirty.status !== 0) throw new Error('LeanEval catalog source files differ from the pinned benchmark commit.');
  for (const file of files) {
    assertNoSymlinkPath(root, file);
    const expected = gitText(root, ['rev-parse', `${benchmarkCommit}:${file}`]).toLowerCase();
    const actual = gitText(root, ['hash-object', '--no-filters', '--', file]).toLowerCase();
    if (expected !== actual) throw new Error(`LeanEval catalog source hash mismatch: ${file}`);
    const stat = fs.lstatSync(path.join(root, file));
    if (!stat.isFile() || stat.isSymbolicLink())
      throw new Error(`LeanEval catalog source must be a regular file: ${file}`);
  }
};

const parseJson = (contents: string, relativePath: string): unknown => {
  try {
    return JSON.parse(contents) as unknown;
  } catch (error) {
    throw new Error(`LeanEval catalog JSON is invalid: ${relativePath}`, { cause: error });
  }
};

const parseTomlFile = (contents: string, relativePath: string): JsonRecord => {
  try {
    const parsed = parseToml(contents);
    const value = record(parsed);
    if (!value) throw new Error('expected a TOML table');
    return value;
  } catch (error) {
    throw new Error(`LeanEval catalog TOML is invalid: ${relativePath}`, { cause: error });
  }
};

const normalizeCredit = (value: unknown): LeanEvalCatalogCredit | undefined => {
  const item = record(value);
  const problemId = text(item?.problem_id) ?? text(item?.problemId);
  const statementRevision = positiveInt(item?.statement_revision ?? item?.statementRevision, 0);
  if (!problemId || statementRevision < 1) return undefined;
  return Object.freeze({
    problemId,
    statementRevision,
    ...optionalText('canonicalModelId', item?.canonical_model_id ?? item?.canonicalModelId),
    ...optionalText('submitter', item?.submitter),
    ...optionalText('acceptedAt', item?.accepted_at ?? item?.acceptedAt),
    ...(typeof item?.first_solve === 'boolean' ? { firstSolve: item.first_solve }
      : typeof item?.firstSolve === 'boolean' ? { firstSolve: item.firstSolve } : {}),
  });
};

const readCredits = (credits: LeanEvalCatalogReadOptions['credits']): readonly LeanEvalCatalogCredit[] => {
  const seen = new Set<string>();
  const normalized = (credits ?? []).flatMap((value) => {
    const credit = normalizeCredit(value);
    if (!credit) return [];
    const key = [
      credit.problemId,
      credit.statementRevision,
      credit.canonicalModelId ?? '',
      credit.submitter ?? '',
      credit.acceptedAt ?? '',
    ].join('\0');
    if (seen.has(key)) return [];
    seen.add(key);
    return [credit];
  });
  return Object.freeze(
    normalized.toSorted(
      (left, right) =>
        left.problemId.localeCompare(right.problemId) ||
        left.statementRevision - right.statementRevision ||
        (left.acceptedAt ?? '').localeCompare(right.acceptedAt ?? '')
    )
  );
};

const isInstanceDeclaration = (body: string): boolean =>
  /(?:^|\n)\s*(?:noncomputable\s+)?instance\b/u.test(body) ||
  /(?:^|\n)\s*@\[[^\]\n]*\binstance\b[^\]\n]*\]/u.test(body);

export function parseLeanEvalLeaderboardCredits(payload: unknown): Readonly<{
  credits: readonly LeanEvalCatalogCredit[];
  generatedAt: number;
}> {
  const root = record(payload);
  if (!root || !Array.isArray(root.credits)) throw new TypeError('LeanEval leaderboard response is invalid');
  const schema = text(root.schema);
  if (schema && !/^.*leaderboard.*$/iu.test(schema)) {
    throw new TypeError('LeanEval leaderboard schema is unsupported');
  }
  const generatedAtText = text(root.generated_at ?? root.generatedAt);
  const generatedAt = generatedAtText ? Date.parse(generatedAtText) : Number.NaN;
  if (!Number.isFinite(generatedAt) || generatedAt <= 0)
    throw new TypeError('LeanEval leaderboard generated_at is invalid');
  const credits = readCredits(root.credits);
  return Object.freeze({ credits, generatedAt });
}

export async function fetchLeanEvalLeaderboardCredits(
  options: Readonly<{
    fetchImpl?: FetchLike;
    timeoutMs?: number;
    /** Bypass the five-minute browsing cache for an authority decision. */
    forceRefresh?: boolean;
  }> = {}
): Promise<
  Readonly<{
    credits: readonly LeanEvalCatalogCredit[];
    generatedAt: number;
    sourceUrl: typeof LEAN_EVAL_LEADERBOARD_URL;
  }>
> {
  if (!options.forceRefresh && !options.fetchImpl && leaderboardCache && leaderboardCache.expiresAt > Date.now())
    return leaderboardCache.value;
  const timeoutMs = Math.max(1_000, Math.min(options.timeoutMs ?? 10_000, 30_000));
  const fetcher = options.fetchImpl ?? globalThis.fetch;
  for (let attempt = 0; attempt < 2; attempt += 1) {
    const controller = new AbortController();
    const timeout = setTimeout(() => controller.abort(), timeoutMs);
    try {
      const response = await fetcher(LEAN_EVAL_LEADERBOARD_URL, {
        headers: { accept: 'application/json', 'user-agent': 'DeepScientist LeanEval catalog intake' },
        signal: controller.signal,
      });
      if (!response.ok) throw new Error(`LeanEval leaderboard HTTP ${response.status}`);
      const body = await response.text();
      if (Buffer.byteLength(body, 'utf8') > 8 * 1024 * 1024)
        throw new Error('LeanEval leaderboard response is too large');
      const parsed = parseLeanEvalLeaderboardCredits(parseJson(body, LEAN_EVAL_LEADERBOARD_URL));
      const value = Object.freeze({ ...parsed, sourceUrl: LEAN_EVAL_LEADERBOARD_URL });
      if (!options.fetchImpl) leaderboardCache = Object.freeze({ expiresAt: Date.now() + 5 * 60 * 1000, value });
      return value;
    } catch (error) {
      if (!(error instanceof Error && error.name === 'AbortError') || attempt === 1) throw error;
    } finally {
      clearTimeout(timeout);
    }
  }
  throw new Error('LeanEval leaderboard request exhausted retries');
}

const parseHoleMetadata = (root: string, generatedPath: string, problemId: string): readonly LeanEvalCatalogHole[] => {
  const relativePath = `${generatedPath}/holes.json`;
  const parsed = record(parseJson(readFile(root, relativePath), relativePath));
  if (!parsed || text(parsed.id) !== problemId || !Array.isArray(parsed.holes)) return Object.freeze([]);
  return Object.freeze(
    parsed.holes.flatMap((value): LeanEvalCatalogHole[] => {
      const hole = record(value);
      const name = text(hole?.name);
      const basename = text(hole?.basename) ?? name?.split('.').at(-1);
      if (!name || !basename) return [];
      const body = text(hole?.body);
      const rawKind = text(hole?.kind)?.toLowerCase();
      const kind =
        rawKind === 'instance' || (rawKind === 'def' && body && isInstanceDeclaration(body))
          ? 'instance'
          : rawKind === 'def' || rawKind === 'definition'
            ? 'definition'
            : rawKind === 'theorem'
              ? 'theorem'
              : 'unknown';
      return [Object.freeze({ name, basename, kind })];
    })
  );
};

const activeV1Ids = (root: string, setId: string): ReadonlyMap<string, number> => {
  const relativePath = `manifests/sets/${setId}.toml`;
  const parsed = parseTomlFile(readFile(root, relativePath), relativePath);
  const members = Array.isArray(parsed.members) ? parsed.members : [];
  const result = new Map<string, number>();
  for (const value of members) {
    const item = record(value);
    const id = text(item?.problem_id ?? item?.problemId);
    if (id) result.set(id, positiveInt(item?.statement_revision ?? item?.statementRevision));
  }
  return result;
};

const manifestFor = (root: string, id: string): { relativePath: string; manifest: JsonRecord } => {
  const relativePath = `manifests/problems/${id}.toml`;
  return { relativePath, manifest: parseTomlFile(readFile(root, relativePath), relativePath) };
};

const canonicalProblem = (problem: LeanEvalCatalogProblem): string =>
  JSON.stringify({
    id: problem.id,
    title: problem.title,
    group: problem.group,
    status: problem.status,
    visible: problem.visible,
    statementRevision: problem.statementRevision,
    tags: problem.tags,
    module: problem.module,
    holes: problem.holes,
    generatedPath: problem.generatedPath,
    activeV1: problem.activeV1,
    acceptedCreditCount: problem.acceptedCreditCount,
    acceptedModelIds: problem.acceptedModelIds,
    selectionEvidence: problem.selectionEvidence,
  });

/** Public authors' warnings are evidence to review, not a measured difficulty score. */
function selectionEvidence(root: string, generatedPath: string, notes?: string): NonNullable<LeanEvalCatalogProblem['selectionEvidence']> {
  const file = `${generatedPath}/ChallengeDeps.lean`;
  const source = fs.existsSync(path.join(root, file)) ? readFile(root, file) : '';
  const publicGapNotes: { file: string; line: number; text: string }[] = [];
  for (const [location, contents] of [[file, source], ['manifest.notes', notes ?? '']] as const) {
    const lines = contents.split('\n');
    for (let index = 0; index < lines.length; index++) {
      const plain = lines.slice(Math.max(0, index - 1), index + 3).join(' ').replaceAll('*', '');
      if (!/(?:open formalization target|not (?:yet )?(?:been )?formalized|(?:not|missing|lacks?).{0,50}(?:mathlib|formaliz)|mathlib.{0,80}(?:does not|not available|missing|lacks?))/iu.test(plain)) continue;
      if (publicGapNotes.some(note => note.file === location && index + 1 - note.line < 4)) continue;
      publicGapNotes.push({ file: location, line: index + 1, text: plain.trim().slice(0, 1500) });
    }
  }
  return Object.freeze({ libraryReview: 'unreviewed', publicGapNotes: Object.freeze(publicGapNotes),
    publicSourceDigest: sha256(JSON.stringify({ source, notes: notes ?? '' })) });
}

/** Read the official catalog without inspecting protected Solution.lean files. */
export function readLeanEvalCatalog(options: LeanEvalCatalogReadOptions): LeanEvalCatalog {
  const root = fs.realpathSync(path.resolve(options.repositoryRoot));
  const benchmarkCommit = (options.benchmarkCommit ?? LEAN_EVAL_BENCHMARK_COMMIT).trim().toLowerCase();
  if (!/^[0-9a-f]{40}$/u.test(benchmarkCommit))
    throw new TypeError('LeanEval benchmarkCommit must be a full commit hash');
  if (options.verifyGitCommit) {
    const result = mathGitResult(root, ['rev-parse', 'HEAD'], { maxBuffer: 2 * 1024 * 1024 });
    const actual = result.status === 0 ? result.stdout.toString('utf8').trim().toLowerCase() : '';
    if (actual !== benchmarkCommit)
      throw new Error(`LeanEval checkout must be at ${benchmarkCommit}; got ${actual || 'unknown'}.`);
  }
  const setId = (options.setId ?? 'v1').trim();
  if (!/^[A-Za-z0-9._-]{1,64}$/u.test(setId)) throw new TypeError('LeanEval setId is invalid');
  const indexRelativePath = 'generated/index.json';
  const parsedIndex = parseJson(readFile(root, indexRelativePath), indexRelativePath);
  if (!Array.isArray(parsedIndex)) throw new Error('LeanEval generated/index.json must contain an array');
  if (options.verifyGitCommit) {
    assertCatalogSourceIntegrity(root, benchmarkCommit, [indexRelativePath, `manifests/sets/${setId}.toml`]);
  }
  const v1 = activeV1Ids(root, setId);
  const credits = readCredits(options.credits);
  const creditByProblem = new Map<string, LeanEvalCatalogCredit[]>();
  for (const credit of credits) {
    const values = creditByProblem.get(credit.problemId) ?? [];
    values.push(credit);
    creditByProblem.set(credit.problemId, values);
  }
  const generatedAt = options.generatedAt ?? Date.now();
  if (!Number.isFinite(generatedAt) || generatedAt <= 0) throw new TypeError('generatedAt must be positive');
  const problems: LeanEvalCatalogProblem[] = [];
  for (const value of parsedIndex) {
    const indexEntry = record(value);
    const id = text(indexEntry?.id);
    const generatedPathValue = text(indexEntry?.generated_path ?? indexEntry?.generatedPath);
    const generatedPath = generatedPathValue ? safeRelativePath(generatedPathValue, 'generated_path') : undefined;
    if (!id || !generatedPath) continue;
    if (!/^[A-Za-z0-9_.-]+$/u.test(id)) throw new Error(`LeanEval catalog problem id is invalid: ${id}`);
    const { relativePath, manifest } = manifestFor(root, id);
    const statementRevision = positiveInt(manifest.statement_revision ?? indexEntry?.statement_revision);
    const activeV1 = v1.get(id) === statementRevision;
    const problemCredits = (creditByProblem.get(id) ?? []).filter(
      (credit) => credit.statementRevision === statementRevision
    );
    const acceptedModelIds = [
      ...new Set(problemCredits.flatMap((credit) => (credit.canonicalModelId ? [credit.canonicalModelId] : []))),
    ].toSorted();
    const eligibilityReasons: string[] = [];
    if (!activeV1) eligibilityReasons.push('not_in_v1');
    if (text(manifest.status ?? indexEntry?.status) !== 'active') eligibilityReasons.push('inactive');
    if (manifest.visible !== true && indexEntry?.visible !== true) eligibilityReasons.push('hidden');
    if (problemCredits.length > 0) eligibilityReasons.push('accepted_credit_exists');
    const holes = parseHoleMetadata(root, generatedPath, id);
    const sourceFiles = Object.freeze(
      [
        relativePath,
        `${generatedPath}/Challenge.lean`,
        `${generatedPath}/ChallengeDeps.lean`,
        `${generatedPath}/config.json`,
        `${generatedPath}/holes.json`,
        `${generatedPath}/lakefile.toml`,
        `${generatedPath}/lean-toolchain`,
        `${generatedPath}/README.md`,
        `${generatedPath}/WorkspaceTest.lean`,
      ].filter((file) => fs.existsSync(path.join(root, file)))
    );
    if (options.verifyGitCommit) assertCatalogSourceIntegrity(root, benchmarkCommit, sourceFiles);
    problems.push(
      Object.freeze({
        id,
        title: text(manifest.title ?? indexEntry?.title) ?? id,
        group: text(manifest.group ?? indexEntry?.group) ?? 'formalization-evaluation',
        status: text(manifest.status ?? indexEntry?.status) ?? 'unknown',
        visible: manifest.visible === true || indexEntry?.visible === true,
        statementRevision,
        tags: stringList(manifest.tags ?? indexEntry?.tags),
        module: text(manifest.module ?? indexEntry?.module) ?? '',
        holes,
        generatedPath,
        ...optionalText('submitter', manifest.submitter ?? indexEntry?.submitter),
        ...optionalText('source', manifest.source),
        ...optionalText('notes', manifest.notes),
        ...optionalText('informalSolution', manifest.informal_solution),
        activeV1,
        acceptedCreditCount: problemCredits.length,
        acceptedModelIds: Object.freeze(acceptedModelIds),
        zeroCredit: problemCredits.length === 0,
        eligible: eligibilityReasons.length === 0,
        eligibilityReasons: Object.freeze(eligibilityReasons),
        selectionEvidence: selectionEvidence(root, generatedPath, text(manifest.notes)),
        catalogEvidence: Object.freeze({ benchmarkCommit, sourceFiles, generatedAt }),
      })
    );
  }
  const orderedProblems = Object.freeze(problems.toSorted((left, right) => left.id.localeCompare(right.id)));
  const catalogPayload = JSON.stringify({
    schema: LEAN_EVAL_CATALOG_SCHEMA,
    repositoryUrl: LEAN_EVAL_REPOSITORY_URL,
    benchmarkCommit,
    setId,
    problems: orderedProblems.map(canonicalProblem),
    credits,
  });
  return Object.freeze({
    schema: LEAN_EVAL_CATALOG_SCHEMA,
    repositoryUrl: LEAN_EVAL_REPOSITORY_URL,
    benchmarkCommit,
    setId,
    catalogHash: sha256(catalogPayload),
    generatedAt,
    problems: orderedProblems,
    credits,
  });
}

export function findLeanEvalCatalogProblem(
  catalog: LeanEvalCatalog,
  problemId: string
): LeanEvalCatalogProblem | undefined {
  return catalog.problems.find((problem) => problem.id === problemId);
}
