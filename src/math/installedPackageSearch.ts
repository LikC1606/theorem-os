/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import fs from 'node:fs';
import path from 'node:path';
import { parse as parseToml } from 'smol-toml';
import { leanRepositoryIdentity, objectValue, readLeanProjectPackageInventory, type LeanProjectPackageDependency } from "./upstreamPackageSearch";
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
): Promise<{ sourceRoot: string; packageRoot: string } | undefined> => {
  let packagesRoot: string;
  let rootStat: fs.Stats;
  try {
    const lakeRoot = path.join(await fs.promises.realpath(projectRoot), '.lake');
    if (await fs.promises.realpath(lakeRoot) !== lakeRoot) return undefined;
    packagesRoot = await fs.promises.realpath(path.join(lakeRoot, 'packages'));
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
  if (!sourceStat?.isDirectory() || sourceStat.isSymbolicLink() || resolvedSourceRoot !== sourceRoot) return undefined;
  return { sourceRoot: resolvedSourceRoot,
    packageRoot: path.join('.lake', 'packages', path.relative(resolvedPackagesRoot, resolvedSourceRoot)).replaceAll(path.sep, '/') };
};

const excludedPath = (relativePath: string): boolean =>
  relativePath
    .split(path.sep)
    .some((segment) => EXCLUDED_PATH_SEGMENTS.has(segment.replace(/\.lean$/iu, '').toLowerCase()));

export const isAllowedInstalledLeanSource = (relativePath: string): boolean =>
  relativePath.endsWith('.lean') && !excludedPath(relativePath);

/** Locale-independent UTF-16 code-unit order, so frozen corpora sort identically on every host. */
export const compareCodeUnits = (a: string, b: string): number => (a < b ? -1 : a > b ? 1 : 0);

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
      for (const entry of entries.toSorted((left, right) => compareCodeUnits(left.name, right.name))) {
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
  return Object.freeze(files.toSorted(compareCodeUnits));
};

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
    const location = await packageSourceRoot(projectRoot, dependency);
    if (!location) throw new TypeError('installed_package_source_missing');
    const { sourceRoot, packageRoot } = location;
    const files = await leanSourceFiles(sourceRoot);
    const directories = await packageModuleSourceDirectories(sourceRoot);
    for (let offset = 0; offset < files.length; offset += 16) {
      // Preserve file order and finish closing the batch even when one read fails.
      const batch = await Promise.allSettled(files.slice(offset, offset + 16).map(async file => ({
        packageName: dependency.name,
        packageRevision: dependency.revision,
        packageRoot,
        sourceFile: `${packageRoot}/${path.relative(sourceRoot, file).replaceAll(path.sep, '/')}`,
        sourceModule: sourceModuleForFile(sourceRoot, file, directories),
        source: await readInstalledSource(file),
      })));
      for (const result of batch) {
        if (result.status === 'rejected') throw result.reason;
        sources.push(result.value);
      }
    }
  }
  return sources;
}
