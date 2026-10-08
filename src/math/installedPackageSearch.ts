/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import fs from 'node:fs';
import crypto from 'node:crypto';
import path from 'node:path';
import { parse as parseToml } from 'smol-toml';
import {
  symbolicMathTokens,
  type MathematicsInstalledPackagePremise,
  type MathematicsInstalledPackageSearchAttempt,
} from "../common/chat/mathematics";
import { inspectLeanDeclarations } from "./verifier";
import { runLeanEvalLeanProbe, type LeanEvalLeanProbeRequest } from "./leanEvalLeanProbe";
import {
  leanRepositoryIdentity,
  readLeanProjectPackageInventory,
  type LeanProjectPackageDependency,
} from "./upstreamPackageSearch";

const DEFAULT_RESULT_LIMIT = 48;
const MAX_RESULT_LIMIT = 64;
const MAX_SCOPES = 2;
export const MAX_INSTALLED_SOURCE_FILE_BYTES = 16 * 1024 * 1024;
const MAX_LAKEFILE_BYTES = 256 * 1024;
const EXCLUDED_PATH_SEGMENTS = new Set([
  '.git',
  '.lake',
  'bench',
  'benchmark',
  'benchmarks',
  'build',
  'challenge',
  'challenges',
  'comparator',
  'comparators',
  'example',
  'examples',
  'lakefile',
  'solution',
  'solutions',
  'submission',
  'submissions',
  'test',
  'tests',
  'workspacetest',
  'workspacetests',
]);

export const INSTALLED_CORPUS_POLICY = Object.freeze({
  maxScopes: MAX_SCOPES,
  version: 2,
  maxSourceFilesPerPackage: null,
  maxDiscoveredFilesPerPackage: null,
  maxFileBytes: MAX_INSTALLED_SOURCE_FILE_BYTES,
  maxBytesPerPackage: null,
  excludedPathSegments: [...EXCLUDED_PATH_SEGMENTS].toSorted(),
  selection: 'breadth-first-codepoint-then-relative-path',
  ranking: 'lexical-score-desc-name-module-path-codepoint',
  defaultResultLimit: 15,
  maxResultLimit: MAX_RESULT_LIMIT,
});

export type MathematicsInstalledPackageSearchResult = Readonly<{
  premises: readonly MathematicsInstalledPackagePremise[];
  attempts: readonly MathematicsInstalledPackageSearchAttempt[];
  coverage?: Readonly<{
    sourceFiles: number;
    complete: boolean;
    matchedDeclarations: number;
    nextOffset: number | null;
    semantics: 'lexical-declaration-headers';
  }>;
}>;

export type ScoredInstalledPremise = Readonly<{
  premise: Omit<MathematicsInstalledPackagePremise, 'providerRank'>;
  score: number;
}>;

const elaboratedHeaderCache = new Map<string, readonly MathematicsInstalledPackagePremise[]>();

async function headerDependencyIdentity(projectRoot: string): Promise<string | undefined> {
  try {
    const packages = await readLeanProjectPackageInventory(projectRoot);
    const digest = crypto.createHash('sha256');
    for (const file of [
      'lean-toolchain',
      'lake-manifest.json',
      'lakefile.lean',
      'lakefile.toml',
      '.lake/package-overrides.json',
    ]) {
      digest.update(file);
      const contents = await fs.promises
        .readFile(path.join(projectRoot, file))
        .catch((error: NodeJS.ErrnoException) => {
          if (error.code === 'ENOENT') return Buffer.from('missing');
          throw error;
        });
      digest.update(contents);
    }
    // Dependency sources, including non-result modules, invalidate elaborated section binders.
    for (let index = 0; index < packages.length; index += MAX_SCOPES) {
      const sources = await captureInstalledLeanSources(
        projectRoot,
        packages.slice(index, index + MAX_SCOPES).map((item) => item.name)
      );
      for (const source of sources) digest.update(source.sourceFile).update('\0').update(source.source).update('\0');
    }
    return digest.digest('hex');
  } catch {
    return undefined;
  }
}

type LeanTypeShape = Readonly<{
  head: string;
  skeleton: string;
  parameterTypes: ReadonlySet<string>;
}>;
const typeShapes = new Map<string, LeanTypeShape>();

/** Build a conservative surface shape for ranking; Lean still decides applicability. */
function leanTypeShape(text: string, declarationName?: string): LeanTypeShape {
  const identity = JSON.stringify([text, declarationName ?? null]);
  const cached = typeShapes.get(identity);
  if (cached) return cached;
  const leadingName = text.trimStart().match(/^[\p{L}_][\p{L}\p{N}_'.]*/u)?.[0];
  if (declarationName && leadingName && [declarationName, declarationName.split('.').at(-1)].includes(leadingName)) {
    text = text.trimStart().slice(leadingName.length).trimStart();
  }
  const bound = new Set<string>();
  const parameterTypes = new Set<string>();
  const tokens = (value: string): string[] =>
    value.match(/[\p{L}_][\p{L}\p{N}_'.]*|:=|->|<=|>=|[∀∃→≤≥≠↔∈∧∨¬]|[^\s]/gu) ?? [];
  const bind = (values: readonly string[]) => {
    const colon = values.indexOf(':');
    if (colon < 0) return;
    for (const name of values.slice(0, colon)) if (/^[\p{L}_]/u.test(name)) bound.add(name);
    for (const name of values.slice(colon + 1)) {
      if (/^[\p{Lu}]/u.test(name) && !['Type', 'Prop', 'Sort'].includes(name)) parameterTypes.add(name);
    }
  };
  const marker = text.lastIndexOf('⊢');
  if (marker >= 0) for (const line of text.slice(0, marker).split('\n')) bind(tokens(line));
  let result = tokens(marker >= 0 ? text.slice(marker + 1) : text);
  const closes: Record<string, string> = { '(': ')', '{': '}', '[': ']' };
  const groupEnd = (values: readonly string[]): number => {
    const stack: string[] = [];
    for (const [index, token] of values.entries()) {
      if (closes[token]) stack.push(closes[token]!);
      else if (token === stack.at(-1)) {
        stack.pop();
        if (!stack.length) return index;
      }
    }
    return -1;
  };
  while (closes[result[0]!]) {
    const end = groupEnd(result);
    if (end < 0) break;
    if (end === result.length - 1) {
      result = result.slice(1, -1);
      continue;
    }
    const binder = result.slice(1, end);
    if (!binder.includes(':') && result[0] !== '[') break;
    bind(binder);
    result = result.slice(end + 1);
  }
  if (result[0] === ':') result = result.slice(1);
  let exists = false;
  while (['∀', 'forall', '∃', 'Exists'].includes(result[0]!)) {
    exists ||= ['∃', 'Exists'].includes(result[0]!);
    result = result.slice(1);
    while (result.length) {
      if (closes[result[0]!]) {
        const end = groupEnd(result);
        if (end < 0) break;
        bind(result.slice(1, end));
        result = result.slice(end + 1);
      } else {
        const comma = result.indexOf(',');
        if (comma < 0) break;
        bind(result.slice(0, comma));
        result = result.slice(comma + 1);
        break;
      }
    }
  }
  let depth = 0;
  const outer: string[] = [];
  for (let index = 0; index < result.length; index++) {
    const token = result[index]!;
    if (closes[token]) depth++;
    else if (Object.values(closes).includes(token)) depth--;
    else if (depth === 0 && ['→', '->'].includes(token)) {
      result = result.slice(index + 1);
      index = -1;
      outer.length = 0;
    } else if (depth === 0) outer.push(token);
  }
  const relations: Record<string, string> = {
    '=': 'Eq',
    '≠': 'Ne',
    '≤': 'LE.le',
    '<=': 'LE.le',
    '≥': 'GE.ge',
    '>=': 'GE.ge',
    '<': 'LT.lt',
    '>': 'GT.gt',
    '∈': 'Membership.mem',
    '∧': 'And',
    '∨': 'Or',
    '↔': 'Iff',
    '¬': 'Not',
  };
  const relation = outer.find((token) => relations[token]);
  const head = exists
    ? 'Exists'
    : relation
      ? relations[relation]!
      : (outer.find((token) => /^[\p{L}_]/u.test(token) && !bound.has(token)) ?? '');
  const variables = new Map<string, string>();
  const skeleton = result
    .map((token) => {
      if (!bound.has(token)) return relations[token] ?? token;
      if (!variables.has(token)) variables.set(token, `$${variables.size}`);
      return variables.get(token)!;
    })
    .join(' ');
  const shape = Object.freeze({ head, skeleton, parameterTypes });
  if (typeShapes.size >= 32768) typeShapes.delete(typeShapes.keys().next().value!);
  typeShapes.set(identity, shape);
  return shape;
}

export function scoreInstalledPremiseForGoal(
  premise: Pick<MathematicsInstalledPackagePremise, 'declarationName' | 'declarationType'>,
  currentGoal: string | undefined
): number {
  if (!currentGoal) return 0;
  const tokens = symbolicMathTokens([currentGoal]);
  const goal = leanTypeShape(currentGoal);
  const candidate = leanTypeShape(premise.declarationType, premise.declarationName);
  const sameHead = Boolean(goal.head && goal.head === candidate.head);
  const structural = sameHead
    ? 18 +
      (goal.skeleton === candidate.skeleton ? 48 : 0) +
      8 * [...goal.parameterTypes].filter((type) => candidate.parameterTypes.has(type)).length
    : 0;
  return (
    structural + 4 * lexicalScore(tokens, [premise.declarationType]) + lexicalScore(tokens, [premise.declarationName])
  );
}

/** Ask Lean for elaborated declaration headers before presenting installed premises to a Worker. */
export async function validateInstalledLeanPremiseHeaders(
  projectRoot: string,
  premises: readonly MathematicsInstalledPackagePremise[],
  options: Pick<LeanEvalLeanProbeRequest, 'env' | 'signal' | 'timeoutMs' | 'lakePackagesPath' | 'projectRelative'> & {
    runProbe?: typeof runLeanEvalLeanProbe;
    currentGoal?: string;
    dependencyFingerprint?: string;
  } = {}
) {
  const namePattern = /^[\p{L}_][\p{L}\p{M}\p{N}_']*(?:\.[\p{L}_][\p{L}\p{M}\p{N}_']*)*$/u;
  if (!premises.length) return { premises, status: 'not_requested' as const, checkedNames: [] as string[] };
  if (
    premises.some(
      (premise) =>
        !namePattern.test(premise.declarationName) ||
        !namePattern.test(premise.sourceModule) ||
        !isAllowedInstalledLeanSource(`${premise.sourceModule.replaceAll('.', '/')}.lean`)
    )
  )
    throw new Error('installed_declaration_probe_invalid');
  const { runProbe = runLeanEvalLeanProbe, currentGoal, dependencyFingerprint, ...probeOptions } = options;
  const root = path.resolve(projectRoot, probeOptions.projectRelative ?? '.');
  const dependencyIdentity = dependencyFingerprint ?? (await headerDependencyIdentity(root));
  const cacheKey = dependencyIdentity
    ? JSON.stringify([
        root,
        dependencyIdentity,
        probeOptions.lakePackagesPath,
        premises.map((premise) => [premise.declarationName, premise.sourceModule, premise.sourceFile]),
      ])
    : undefined;
  const rankHeaders = (headers: readonly MathematicsInstalledPackagePremise[]) =>
    headers
      .toSorted(
        (a, b) =>
          scoreInstalledPremiseForGoal(b, currentGoal) - scoreInstalledPremiseForGoal(a, currentGoal) ||
          a.providerRank - b.providerRank
      )
      .map((premise, index) => ({ ...premise, providerRank: index + 1 }));
  const cached = cacheKey ? elaboratedHeaderCache.get(cacheKey) : undefined;
  if (cached && !options.signal?.aborted)
    return {
      premises: rankHeaders(cached),
      status: 'passed' as const,
      checkedNames: cached.map((premise) => premise.declarationName),
      cacheHit: true,
    };
  const probe = await runProbe({
    ...probeOptions,
    workspaceRoot: projectRoot,
    sourceFile: '.deepscientist/math/installed-header-probe.lean',
    mode: 'compile',
    sourceText:
      [
        ...[...new Set(premises.map((premise) => premise.sourceModule))].map((module) => `import ${module}`),
        ...premises.map((premise) => `#check ${premise.declarationName}`),
      ].join('\n') + '\n',
  });
  // Current probe transports expose diagnostics only. Keep compatibility with
  // older test/adapter transports that supplied elaborated information lines.
  const informationMessages = (probe as { informationMessages?: unknown }).informationMessages;
  const messages =
    probe.status === 'passed' && Array.isArray(informationMessages)
      ? informationMessages.filter((candidate): candidate is string => typeof candidate === 'string')
      : [];
  const checkedNames: string[] = [];
  const typed = premises.map((premise) => {
    const message = messages.find(
      (candidate) =>
        candidate.startsWith(premise.declarationName) &&
        /^(?:\s|\.\{)/u.test(candidate.slice(premise.declarationName.length))
    );
    if (!message) return premise;
    const declarationType = message
      .slice(premise.declarationName.length)
      .replace(/^\.\{[^}]*\}/u, '')
      .trim();
    if (!declarationType.includes(':')) return premise;
    checkedNames.push(premise.declarationName);
    return { ...premise, declarationType };
  });
  if (probe.status === 'passed' && messages.length === 0)
    checkedNames.push(...premises.map((premise) => premise.declarationName));
  if (cacheKey && probe.status === 'passed' && checkedNames.length === premises.length) {
    if (elaboratedHeaderCache.size >= 64) elaboratedHeaderCache.delete(elaboratedHeaderCache.keys().next().value!);
    elaboratedHeaderCache.set(cacheKey, typed);
  }
  return { premises: rankHeaders(typed), status: probe.status, checkedNames, cacheHit: false };
}

const canonicalPackageName = (value: string): string =>
  value
    .trim()
    .replace(/^«|»$/gu, '')
    .toLowerCase()
    .replace(/[^a-z0-9]/gu, '');

const packageForScope = (
  scope: string,
  packages: readonly LeanProjectPackageDependency[]
): LeanProjectPackageDependency | undefined => {
  const scopeName = canonicalPackageName(scope.split('/').at(-1) ?? scope);
  const repositoryIdentity = leanRepositoryIdentity(scope);
  return packages.find(
    (candidate) =>
      canonicalPackageName(candidate.name) === scopeName ||
      (repositoryIdentity && candidate.url && leanRepositoryIdentity(candidate.url) === repositoryIdentity)
  );
};

const isInside = (parent: string, child: string): boolean => {
  const relative = path.relative(parent, child);
  return Boolean(relative) && !relative.startsWith(`..${path.sep}`) && !path.isAbsolute(relative);
};

const packageSourceRoot = async (
  projectRoot: string,
  dependency: LeanProjectPackageDependency
): Promise<string | undefined> => {
  const packagesRoot = path.join(projectRoot, '.lake', 'packages');
  let rootStat: fs.Stats;
  try {
    rootStat = await fs.promises.lstat(packagesRoot);
  } catch {
    return undefined;
  }
  if (!rootStat.isDirectory() || rootStat.isSymbolicLink()) return undefined;
  const repositoryName = dependency.url ? leanRepositoryIdentity(dependency.url)?.split('/').at(-1) : undefined;
  const names = new Set([canonicalPackageName(dependency.name), canonicalPackageName(repositoryName ?? '')]);
  const entries = await fs.promises.readdir(packagesRoot, { withFileTypes: true });
  const entry = entries.find(
    (candidate) =>
      candidate.isDirectory() && !candidate.isSymbolicLink() && names.has(canonicalPackageName(candidate.name))
  );
  if (!entry) return undefined;
  let sourceRoot = path.join(packagesRoot, entry.name);
  if (dependency.subdirectory) {
    const subdirectory = path.normalize(dependency.subdirectory);
    if (path.isAbsolute(subdirectory) || subdirectory === '..' || subdirectory.startsWith(`..${path.sep}`)) {
      return undefined;
    }
    sourceRoot = path.resolve(sourceRoot, subdirectory);
  }
  const resolvedPackagesRoot = await fs.promises.realpath(packagesRoot);
  const resolvedSourceRoot = await fs.promises.realpath(sourceRoot).catch((): undefined => undefined);
  if (!resolvedSourceRoot || !isInside(resolvedPackagesRoot, resolvedSourceRoot)) return undefined;
  const sourceStat = await fs.promises.lstat(resolvedSourceRoot).catch((): undefined => undefined);
  return sourceStat?.isDirectory() && !sourceStat.isSymbolicLink() ? resolvedSourceRoot : undefined;
};

const excludedPath = (relativePath: string): boolean =>
  relativePath
    .split(path.sep)
    .some((segment) => EXCLUDED_PATH_SEGMENTS.has(segment.replace(/\.lean$/iu, '').toLowerCase()));

export const isAllowedInstalledLeanSource = (relativePath: string): boolean =>
  relativePath.endsWith('.lean') && !excludedPath(relativePath);

const compare = (a: string, b: string): number => (a < b ? -1 : a > b ? 1 : 0);

const leanSourceFiles = async (packageRoot: string): Promise<readonly string[]> => {
  const queue = [packageRoot];
  const files: string[] = [];
  const visit = async (): Promise<void> => {
    if (queue.length === 0) return;
    const directories = queue.splice(0, Math.min(queue.length, 16));
    const listings = await Promise.all(
      directories.map(async (directory) => ({
        directory,
        entries: await fs.promises.readdir(directory, { withFileTypes: true }),
      }))
    );
    for (const { directory, entries } of listings) {
      for (const entry of entries.toSorted((left, right) => compare(left.name, right.name))) {
        if (entry.isSymbolicLink()) continue;
        const absolute = path.join(directory, entry.name);
        const relative = path.relative(packageRoot, absolute);
        if (!relative || excludedPath(relative)) continue;
        if (entry.isDirectory()) queue.push(absolute);
        else if (entry.isFile() && entry.name.endsWith('.lean')) files.push(absolute);
      }
    }
    await visit();
  };
  await visit();
  return Object.freeze(files.toSorted(compare));
};

const lexicalScore = (queryTokens: ReadonlySet<string>, values: readonly string[]): number => {
  if (queryTokens.size === 0) return 0;
  const candidateTokens = symbolicMathTokens(values);
  let score = 0;
  for (const query of queryTokens) {
    for (const candidate of candidateTokens) {
      if (candidate === query) score += 3;
      else if (query.length >= 3 && candidate.length >= 3 && (candidate.includes(query) || query.includes(candidate))) {
        score += 1;
      }
    }
  }
  return score;
};

export type InstalledLeanDeclarationIndex = Readonly<{
  declarations: readonly Omit<MathematicsInstalledPackagePremise, 'providerRank'>[];
  postings: ReadonlyMap<string, readonly number[]>;
  tokenTrigrams: ReadonlyMap<string, readonly string[]>;
  conclusionHeads: ReadonlyMap<string, readonly number[]>;
}>;

/** Index the immutable declaration surface once; subsequent queries visit matching postings only. */
export function createInstalledLeanDeclarationIndex(
  sources: readonly InstalledLeanSource[]
): InstalledLeanDeclarationIndex {
  const declarations: Omit<MathematicsInstalledPackagePremise, 'providerRank'>[] = [];
  const postings = new Map<string, number[]>();
  const conclusionHeads = new Map<string, number[]>();
  for (const item of sources) {
    for (const declaration of indexDeclarations(item.source)) {
      const index = declarations.length;
      declarations.push({
        packageName: item.packageName,
        packageRevision: item.packageRevision,
        ...declaration,
        sourceModule: item.sourceModule,
        sourceFile: item.sourceFile,
        localDependency: true,
        importRequired: true,
        targetValidationRequired: true,
      });
      const head = leanTypeShape(declaration.declarationType, declaration.declarationName).head;
      if (head) {
        const ids = conclusionHeads.get(head) ?? [];
        ids.push(index);
        conclusionHeads.set(head, ids);
      }
      for (const token of symbolicMathTokens([
        declaration.declarationName,
        declaration.declarationType,
        item.sourceModule,
      ])) {
        const values = postings.get(token);
        if (values) values.push(index);
        else postings.set(token, [index]);
      }
    }
  }
  const tokenTrigrams = new Map<string, string[]>();
  for (const token of postings.keys()) {
    for (const gram of new Set(
      Array.from({ length: Math.max(0, token.length - 2) }, (_, at) => token.slice(at, at + 3))
    )) {
      const tokens = tokenTrigrams.get(gram) ?? [];
      tokens.push(token);
      tokenTrigrams.set(gram, tokens);
    }
  }
  return { declarations, postings, conclusionHeads, tokenTrigrams };
}

export function searchInstalledLeanDeclarationIndex(
  index: InstalledLeanDeclarationIndex,
  queryTokens: ReadonlySet<string>,
  currentGoal?: string
): readonly ScoredInstalledPremise[] {
  const scores = new Map<number, number>();
  if (currentGoal)
    for (const declaration of index.conclusionHeads.get(leanTypeShape(currentGoal).head) ?? [])
      scores.set(declaration, 0);
  const combinedTokens = new Set([...queryTokens, ...symbolicMathTokens(currentGoal ? [currentGoal] : [])]);
  for (const query of combinedTokens) {
    const candidates = new Set<string>(index.postings.has(query) ? [query] : []);
    if (query.length >= 3) {
      // A contained token shares at least one trigram, including the reverse containment case.
      for (let at = 0; at <= query.length - 3; at++)
        for (const token of index.tokenTrigrams.get(query.slice(at, at + 3)) ?? [])
          if (token.includes(query) || query.includes(token)) candidates.add(token);
    }
    for (const candidate of candidates) {
      const score = candidate === query ? 3 : 1;
      for (const declaration of index.postings.get(candidate) ?? [])
        scores.set(declaration, (scores.get(declaration) ?? 0) + score);
    }
  }
  return [...scores].map(([declaration, score]) => ({
    premise: index.declarations[declaration]!,
    score: score + scoreInstalledPremiseForGoal(index.declarations[declaration]!, currentGoal),
  }));
}

const objectValue = (value: unknown): Record<string, unknown> | undefined =>
  value !== null && typeof value === 'object' && !Array.isArray(value) ? (value as Record<string, unknown>) : undefined;

const validSourceDirectory = (value: unknown): string | undefined => {
  if (typeof value !== 'string' || !value.trim()) return undefined;
  const normalized = path.normalize(value.trim());
  if (normalized === '.') return '';
  if (path.isAbsolute(normalized) || normalized === '..' || normalized.startsWith(`..${path.sep}`)) return undefined;
  return normalized;
};

const packageModuleSourceDirectories = async (packageRoot: string): Promise<readonly string[]> => {
  const lakefilePath = path.join(packageRoot, 'lakefile.toml');
  const contents = await fs.promises.readFile(lakefilePath, 'utf8').catch((): undefined => undefined);
  if (contents === undefined || Buffer.byteLength(contents, 'utf8') > MAX_LAKEFILE_BYTES) return Object.freeze([]);
  try {
    const parsed = objectValue(parseToml(contents));
    const libraries = Array.isArray(parsed?.lean_lib) ? parsed.lean_lib.map(objectValue).filter(Boolean) : [];
    return Object.freeze(
      [
        ...new Set(
          libraries.flatMap((library): string[] => {
            const directory = validSourceDirectory(library?.srcDir);
            return directory === undefined ? [] : [directory];
          })
        ),
      ].toSorted((left, right) => right.length - left.length || left.localeCompare(right))
    );
  } catch {
    return Object.freeze([]);
  }
};

const sourceModuleForFile = (
  packageRoot: string,
  file: string,
  configuredSourceDirectories: readonly string[]
): string => {
  const relative = path.relative(packageRoot, file).replaceAll(path.sep, '/');
  const configured = configuredSourceDirectories.find(
    (directory) =>
      !directory || relative === directory || relative.startsWith(`${directory.replaceAll(path.sep, '/')}/`)
  );
  let moduleFile = configured
    ? relative.slice(configured.replaceAll(path.sep, '/').length).replace(/^\//u, '')
    : relative;
  if (!configured && moduleFile.startsWith('src/')) moduleFile = moduleFile.slice('src/'.length);
  return moduleFile.replace(/\.lean$/u, '').replaceAll('/', '.');
};

const maskLeanCommentsAndStrings = (source: string): string => {
  let result = '';
  let lineComment = false;
  let blockDepth = 0;
  let inString = false;
  let escaped = false;
  for (let index = 0; index < source.length; index += 1) {
    const current = source[index];
    const next = source[index + 1];
    if (lineComment) {
      if (current === '\n') {
        lineComment = false;
        result += '\n';
      } else result += ' ';
      continue;
    }
    if (blockDepth > 0) {
      if (current === '/' && next === '-') {
        blockDepth += 1;
        result += '  ';
        index += 1;
      } else if (current === '-' && next === '/') {
        blockDepth -= 1;
        result += '  ';
        index += 1;
      } else result += current === '\n' ? '\n' : ' ';
      continue;
    }
    if (inString) {
      result += current === '\n' ? '\n' : ' ';
      if (escaped) escaped = false;
      else if (current === '\\') escaped = true;
      else if (current === '"') inString = false;
      continue;
    }
    if (current === '-' && next === '-') {
      lineComment = true;
      result += '  ';
      index += 1;
    } else if (current === '/' && next === '-') {
      blockDepth = 1;
      result += '  ';
      index += 1;
    } else if (current === '"') {
      inString = true;
      result += ' ';
    } else result += current;
  }
  return result;
};

type LeanScope = Readonly<{ kind: 'namespace' | 'section'; name?: string }>;

const qualifiedDeclarationNames = (source: string): ReadonlyMap<string, readonly string[]> => {
  const scopes: LeanScope[] = [];
  const names = new Map<string, string[]>();
  const leanName = `[\\p{L}\\p{M}\\p{N}_'.]+`;
  const namespacePattern = new RegExp(`^\\s*namespace\\s+(${leanName})\\s*$`, 'u');
  const sectionPattern = new RegExp(`^\\s*section(?:\\s+(${leanName}))?\\s*$`, 'u');
  const endPattern = new RegExp(`^\\s*end(?:\\s+(${leanName}))?\\s*$`, 'u');
  const declarationPattern = new RegExp(
    `^\\s*(?:@\\[[^\\]]*\\]\\s*)*(?:(?:private|protected|noncomputable|local|unsafe)\\s+)*(?:theorem|lemma|def|instance|opaque|abbrev)\\s+(${leanName})`,
    'u'
  );
  for (const line of maskLeanCommentsAndStrings(source).split('\n')) {
    const namespace = namespacePattern.exec(line)?.[1];
    if (namespace) {
      scopes.push(Object.freeze({ kind: 'namespace', name: namespace }));
      continue;
    }
    if (sectionPattern.test(line)) {
      scopes.push(Object.freeze({ kind: 'section' }));
      continue;
    }
    if (endPattern.test(line)) {
      scopes.pop();
      continue;
    }
    const localName = declarationPattern.exec(line)?.[1];
    if (!localName) continue;
    const namespacePrefix = scopes
      .flatMap((scope) => (scope.kind === 'namespace' && scope.name ? [scope.name] : []))
      .join('.');
    const rootName = localName.replace(/^_root_\./u, '');
    const qualifiedName =
      localName.startsWith('_root_.') || !namespacePrefix || rootName.startsWith(`${namespacePrefix}.`)
        ? rootName
        : `${namespacePrefix}.${rootName}`;
    const candidates = names.get(localName) ?? [];
    candidates.push(qualifiedName);
    names.set(localName, candidates);
  }
  return names;
};

export type InstalledLeanSource = Readonly<{
  packageName: string;
  packageRevision?: string;
  packageRoot?: string;
  sourceModule: string;
  sourceFile: string;
  source: string;
}>;

async function readInstalledSource(file: string): Promise<string> {
  if ((await fs.promises.realpath(file)) !== file) throw new TypeError('installed_corpus_source_invalid');
  const handle = await fs.promises.open(
    file,
    fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK
  );
  try {
    const before = await handle.stat({ bigint: true });
    if (!before.isFile() || before.size > BigInt(MAX_INSTALLED_SOURCE_FILE_BYTES))
      throw new TypeError('installed_corpus_source_invalid');
    const bytes = await handle.readFile();
    const after = await handle.stat({ bigint: true });
    const named = await fs.promises.lstat(file, { bigint: true });
    if (
      before.size !== after.size ||
      before.mtimeNs !== after.mtimeNs ||
      before.ctimeNs !== after.ctimeNs ||
      before.ino !== named.ino ||
      before.dev !== named.dev ||
      bytes.length > MAX_INSTALLED_SOURCE_FILE_BYTES ||
      (await fs.promises.realpath(file)) !== file
    )
      throw new TypeError('installed_corpus_source_changed');
    return new TextDecoder('utf-8', { fatal: true }).decode(bytes);
  } finally {
    await handle.close();
  }
}

/** Capture every permitted source. Read failures invalidate the search instead of hiding declarations. */
/* eslint-disable no-await-in-loop -- Bound concurrent descriptors while traversing large dependencies. */
export async function captureInstalledLeanSources(
  projectRoot: string,
  scopes: readonly string[]
): Promise<readonly InstalledLeanSource[]> {
  if (!scopes.length || scopes.length > MAX_SCOPES || new Set(scopes).size !== scopes.length) {
    throw new TypeError('installed_corpus_invalid_scopes');
  }
  const packages = await readLeanProjectPackageInventory(projectRoot);
  const sources: InstalledLeanSource[] = [];
  for (const scope of scopes) {
    const dependency = packageForScope(scope, packages);
    if (!dependency) throw new TypeError('installed_corpus_package_missing');
    const sourceRoot = await packageSourceRoot(projectRoot, dependency);
    if (!sourceRoot) throw new TypeError('installed_package_source_missing');
    const files = await leanSourceFiles(sourceRoot);
    const directories = await packageModuleSourceDirectories(sourceRoot);
    for (const file of files) {
      sources.push({
        packageName: dependency.name,
        packageRevision: dependency.revision,
        packageRoot: path.relative(projectRoot, sourceRoot).replaceAll(path.sep, '/'),
        sourceFile: path.relative(projectRoot, file).replaceAll(path.sep, '/'),
        sourceModule: sourceModuleForFile(sourceRoot, file, directories),
        source: await readInstalledSource(file),
      });
    }
  }
  return sources;
}
/* eslint-enable no-await-in-loop */

type IndexedDeclaration = Readonly<{ declarationName: string; declarationType: string }>;
const declarationCache = new Map<string, readonly IndexedDeclaration[]>();

function indexDeclarations(source: string): readonly IndexedDeclaration[] {
  const identity = crypto.createHash('sha256').update(source).digest('hex');
  const cached = declarationCache.get(identity);
  if (cached) return cached;
  const qualifiedNames = qualifiedDeclarationNames(source);
  const consumedNames = new Map<string, number>();
  const declarations = inspectLeanDeclarations(source).map((declaration) => {
    const index = consumedNames.get(declaration.name) ?? 0;
    consumedNames.set(declaration.name, index + 1);
    return {
      declarationName: qualifiedNames.get(declaration.name)?.[index] ?? declaration.name,
      declarationType: declaration.declarationType,
    };
  });
  // Eviction limits process memory only; it never limits search coverage.
  if (declarationCache.size >= 32768) declarationCache.delete(declarationCache.keys().next().value!);
  declarationCache.set(identity, declarations);
  return declarations;
}

export function rankInstalledLeanSources(
  sources: readonly InstalledLeanSource[],
  queryTokens: ReadonlySet<string>
): readonly ScoredInstalledPremise[] {
  const results: ScoredInstalledPremise[] = [];
  for (const { source, sourceModule, sourceFile, packageName, packageRevision } of sources) {
    for (const declaration of indexDeclarations(source)) {
      const { declarationName } = declaration;
      const score = lexicalScore(queryTokens, [declarationName, declaration.declarationType, sourceModule]);
      if (score <= 0) continue;
      results.push({
        premise: {
          packageName,
          packageRevision,
          declarationName,
          declarationType: declaration.declarationType,
          sourceModule,
          sourceFile,
          localDependency: true,
          importRequired: true,
          targetValidationRequired: true,
        },
        score,
      });
    }
  }
  return results;
}

const searchOneInstalledPackage = async (
  projectRoot: string,
  dependency: LeanProjectPackageDependency,
  queryTokens: ReadonlySet<string>
): Promise<Readonly<{ results: readonly ScoredInstalledPremise[]; sourceFiles: number }>> => {
  const sources = await captureInstalledLeanSources(projectRoot, [dependency.name]);
  return { results: rankInstalledLeanSources(sources, queryTokens), sourceFiles: sources.length };
};

const installedPackageErrorCode = (error: unknown): string => {
  if (error instanceof TypeError && /^[a-z]+_[a-z0-9_]+$/u.test(error.message)) return error.message;
  return 'installed_package_unavailable';
};

export async function searchInstalledLeanPackagePremises(
  projectRoot: string,
  scopes: readonly string[],
  query: readonly string[],
  options: Readonly<{ resultLimit?: number; offset?: number; currentGoal?: string }> = {}
): Promise<MathematicsInstalledPackageSearchResult> {
  const resultLimit = Math.max(1, Math.min(MAX_RESULT_LIMIT, options.resultLimit ?? DEFAULT_RESULT_LIMIT));
  const offset = options.offset ?? 0;
  if (!Number.isSafeInteger(resultLimit) || !Number.isSafeInteger(offset) || offset < 0)
    throw new TypeError('installed_package_invalid_page');
  const requestedScopes = scopes.map((value) => value.trim());
  if (
    !requestedScopes.length ||
    requestedScopes.length > MAX_SCOPES ||
    requestedScopes.some((scope) => !scope || scope.length > 128) ||
    new Set(requestedScopes).size !== requestedScopes.length
  )
    throw new TypeError('installed_corpus_invalid_scopes');
  const packages = await readLeanProjectPackageInventory(projectRoot);
  const queryTokens = symbolicMathTokens([...query, ...(options.currentGoal ? [options.currentGoal] : [])]);
  const outcomes = await Promise.all(
    requestedScopes.map(async (scope) => {
      const dependency = packageForScope(scope, packages);
      if (!dependency) {
        return {
          results: Object.freeze([]),
          attempt: Object.freeze({ scope, status: 'not_installed' as const, resultCount: 0 }),
        };
      }
      try {
        const { results, sourceFiles } = await searchOneInstalledPackage(projectRoot, dependency, queryTokens);
        return {
          results,
          sourceFiles,
          attempt: Object.freeze({ scope, status: 'ok' as const, resultCount: results.length }),
        };
      } catch (error) {
        return {
          results: Object.freeze([]),
          attempt: Object.freeze({
            scope,
            status: 'unavailable' as const,
            resultCount: 0,
            errorCode: installedPackageErrorCode(error),
          }),
        };
      }
    })
  );
  const seen = new Set<string>();
  const ranked = outcomes
    .flatMap(({ results }) => results)
    .toSorted(
      (left, right) =>
        right.score - left.score ||
        compare(left.premise.declarationName, right.premise.declarationName) ||
        compare(left.premise.sourceModule, right.premise.sourceModule) ||
        compare(left.premise.sourceFile, right.premise.sourceFile)
    )
    .flatMap(({ premise }) => {
      const key = `${premise.packageName}\0${premise.declarationName}\0${premise.sourceModule}`;
      if (seen.has(key)) return [];
      seen.add(key);
      return [premise];
    });
  const page = ranked
    .slice(offset, offset + resultLimit)
    .map((premise, index) => Object.freeze({ ...premise, providerRank: offset + index + 1 }));
  return Object.freeze({
    premises: Object.freeze(page),
    attempts: Object.freeze(outcomes.map(({ attempt }) => attempt)),
    ...(outcomes.some((outcome) => outcome.attempt.status === 'ok')
      ? {
          coverage: Object.freeze({
            sourceFiles: outcomes.reduce((sum, outcome) => sum + (outcome.sourceFiles ?? 0), 0),
            complete: outcomes.every((outcome) => outcome.attempt.status === 'ok'),
            matchedDeclarations: ranked.length,
            nextOffset: offset + page.length < ranked.length ? offset + page.length : null,
            semantics: 'lexical-declaration-headers' as const,
          }),
        }
      : {}),
  });
}
