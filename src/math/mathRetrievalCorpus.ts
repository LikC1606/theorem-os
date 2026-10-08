import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { z } from 'zod';
import { symbolicMathTokens } from "../common/chat/mathematics";
import {
  captureInstalledLeanSources,
  INSTALLED_CORPUS_POLICY,
  MAX_INSTALLED_SOURCE_FILE_BYTES,
  isAllowedInstalledLeanSource,
  rankInstalledLeanSources,
} from "./installedPackageSearch";
import { canonicalMathJson, mathDigest } from "./mathRuntimeIo";

export const MATH_RETRIEVAL_CORPUS_ENV = 'DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS';
export const MATH_RETRIEVAL_CORPUS_SHA_ENV = 'DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS_SHA256';
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

/** The runtime entry is a bundled program, so its identity covers transitive retrieval code. */
export function verifyMathRetrievalImplementation(
  file: string,
  expected: NonNullable<MathRetrievalCorpus['implementation']>
): void {
  if (!path.isAbsolute(file) || fs.realpathSync(file) !== file) throw new Error('math_corpus_implementation_changed');
  const fd = fs.openSync(file, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK);
  try {
    const before = fs.fstatSync(fd, { bigint: true });
    if (!before.isFile() || before.size !== BigInt(expected.bytes))
      throw new Error('math_corpus_implementation_changed');
    const hash = crypto.createHash('sha256');
    const buffer = Buffer.alloc(65536);
    let length = 0;
    while (length <= expected.bytes) {
      const count = fs.readSync(fd, buffer, 0, Math.min(buffer.length, expected.bytes + 1 - length), length);
      if (!count) break;
      hash.update(buffer.subarray(0, count));
      length += count;
    }
    const after = fs.fstatSync(fd, { bigint: true });
    const named = fs.lstatSync(file, { bigint: true });
    if (
      length !== expected.bytes ||
      hash.digest('hex') !== expected.sha256 ||
      before.mtimeNs !== after.mtimeNs ||
      before.ctimeNs !== after.ctimeNs ||
      before.size !== after.size ||
      before.dev !== named.dev ||
      before.ino !== named.ino ||
      fs.realpathSync(file) !== file
    ) {
      throw new Error('math_corpus_implementation_changed');
    }
  } finally {
    fs.closeSync(fd);
  }
}

function readSource(root: string, relative: string): Buffer {
  relativeFileSchema.parse(relative);
  const file = path.join(fs.realpathSync(root), relative);
  if (fs.realpathSync(file) !== file) throw new Error('math_corpus_symlink');
  const fd = fs.openSync(file, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK);
  try {
    const before = fs.fstatSync(fd, { bigint: true });
    if (!before.isFile() || before.size > BigInt(MAX_FILE_BYTES)) throw new Error('math_corpus_invalid_file');
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
      before.size !== after.size ||
      before.mtimeNs !== after.mtimeNs ||
      before.ctimeNs !== after.ctimeNs ||
      before.dev !== current.dev ||
      before.ino !== current.ino ||
      fs.realpathSync(file) !== file
    ) {
      throw new Error('math_corpus_file_changed');
    }
    return bytes;
  } finally {
    fs.closeSync(fd);
  }
}

const identity = (relative: string, bytes: Buffer) => ({
  path: relative,
  bytes: bytes.length,
  sha256: mathDigest(bytes),
});
const compare = (a: string, b: string): number => (a < b ? -1 : a > b ? 1 : 0);

function environmentIdentity(root: string, relative: string) {
  try {
    return identity(relative, readSource(root, relative));
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code === 'ENOENT') return null;
    throw error;
  }
}

const packagePrefix = '.lake/packages/';

function sourceLocation(projectRoot: string, corpus: MathRetrievalCorpus, relative: string) {
  if (!corpus.packageSourceRoot || !relative.startsWith(packagePrefix)) return { root: projectRoot, relative };
  if (fs.realpathSync(corpus.packageSourceRoot) !== corpus.packageSourceRoot)
    throw new Error('math_corpus_package_root_changed');
  return { root: corpus.packageSourceRoot, relative: relative.slice(packagePrefix.length) };
}

/** Bind an already verified dependency snapshot to a solver project using exact trusted Lake overrides. */
export function bindMathRetrievalCorpusToProject(
  sourceProjectRoot: string,
  targetProjectRoot: string,
  value: unknown
): MathRetrievalCorpus {
  const { corpus } = verifyMathRetrievalCorpus(sourceProjectRoot, value);
  if (corpus.projectSubdirectory || corpus.packageSourceRoot || corpus.implementation || corpus.originSha256)
    throw new Error('math_corpus_rebinding_requires_origin');
  const sourceRoot = fs.realpathSync(sourceProjectRoot);
  const targetRoot = fs.realpathSync(targetProjectRoot);
  const targetEnvironment = [
    'lean-toolchain',
    'lake-manifest.json',
    'lakefile.toml',
    'lakefile.lean',
    '.lake/package-overrides.json',
  ].map((file) => ({ path: file, identity: environmentIdentity(targetRoot, file) }));
  if (mathDigest(readSource(sourceRoot, 'lean-toolchain')) !== mathDigest(readSource(targetRoot, 'lean-toolchain')))
    throw new Error('math_corpus_toolchain_mismatch');
  const packageSourceRoot = path.join(sourceRoot, '.lake', 'packages');
  if (fs.realpathSync(packageSourceRoot) !== packageSourceRoot) throw new Error('math_corpus_package_root_changed');
  const manifestSchema = z.object({
    packages: z.array(z.object({ name: z.string(), rev: z.string().optional(), type: z.string() })),
  });
  const sourceManifest = manifestSchema.parse(
    JSON.parse(readSource(sourceRoot, 'lake-manifest.json').toString('utf8'))
  );
  const targetManifest = manifestSchema.parse(
    JSON.parse(readSource(targetRoot, 'lake-manifest.json').toString('utf8'))
  );
  const overrides = z
    .object({ packages: z.array(z.object({ name: z.string(), type: z.string(), dir: z.string().optional() })) })
    .parse(JSON.parse(readSource(targetRoot, '.lake/package-overrides.json').toString('utf8')));
  const canonicalName = (name: string) => name.replace(/^«|»$/gu, '').toLowerCase();
  for (const packageName of new Set(corpus.sources.map((source) => source.packageName))) {
    const matches = (entry: { name: string }) => canonicalName(entry.name) === canonicalName(packageName);
    const origins = sourceManifest.packages.filter(matches);
    const targets = targetManifest.packages.filter(matches);
    const paths = overrides.packages.filter(matches);
    if (
      origins.length !== 1 ||
      targets.length !== 1 ||
      paths.length !== 1 ||
      !origins[0]!.rev ||
      origins[0]!.type !== 'git' ||
      targets[0]!.type !== 'git' ||
      targets[0]!.rev !== origins[0]!.rev ||
      paths[0]!.type !== 'path' ||
      !paths[0]!.dir
    )
      throw new Error('math_corpus_package_revision_mismatch');
    const packageDirectories = new Set(
      corpus.sources
        .filter((source) => source.packageName === packageName)
        .map((source) => source.identity.path.slice(packagePrefix.length).split('/')[0]!)
    );
    if (packageDirectories.size !== 1) throw new Error('math_corpus_package_path_mismatch');
    const expectedRoot = path.join(packageSourceRoot, [...packageDirectories][0]!);
    if (
      corpus.sources.some((source) => source.packageName === packageName && source.packageRevision !== origins[0]!.rev)
    )
      throw new Error('math_corpus_package_revision_mismatch');
    if (paths[0]!.dir !== expectedRoot || fs.realpathSync(expectedRoot) !== expectedRoot)
      throw new Error('math_corpus_package_path_mismatch');
  }
  const bound = corpusSchema.parse({
    ...corpus,
    packageSourceRoot,
    environment: [
      ...corpus.environment.filter((entry) => entry.path.startsWith(packagePrefix)),
      ...targetEnvironment,
    ].toSorted((a, b) => compare(a.path, b.path)),
  });
  verifyMathRetrievalCorpus(targetRoot, bound);
  return bound;
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
      .map((file) => ({ path: file, identity: environmentIdentity(root, file) })),
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
  if (canonicalMathJson(await captureInstalledLeanSources(root, scopes)) !== canonicalMathJson(sources)) {
    throw new Error('math_corpus_capture_changed');
  }
  verifyMathRetrievalCorpus(root, corpus);
  return corpus;
}

/** Read and hash every selected source before exposing any declaration. No partial fallback. */
export function verifyMathRetrievalCorpus(root: string, value: unknown) {
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
  const sources = corpus.sources.map((entry) => {
    if (!entry.identity.path.startsWith('.lake/packages/')) throw new Error('math_corpus_source_outside_packages');
    if (!isAllowedInstalledLeanSource(entry.identity.path.slice('.lake/packages/'.length)))
      throw new Error('math_corpus_source_excluded');
    const location = sourceLocation(projectRoot, corpus, entry.identity.path);
    const bytes = readSource(location.root, location.relative);
    if (bytes.length !== entry.identity.bytes || mathDigest(bytes) !== entry.identity.sha256)
      throw new Error('math_corpus_source_changed');
    return {
      sourceFile: corpus.packageSourceRoot
        ? path.join(location.root, location.relative)
        : corpus.projectSubdirectory
          ? `${corpus.projectSubdirectory}/${entry.identity.path}`
          : entry.identity.path,
      sourceModule: entry.sourceModule,
      packageName: entry.packageName,
      packageRevision: entry.packageRevision,
      source: new TextDecoder('utf-8', { fatal: true }).decode(bytes),
    };
  });
  return { corpus, sources };
}

export function searchMathRetrievalCorpus(
  root: string,
  value: unknown,
  query: readonly string[],
  resultLimit = 15,
  offset = 0
) {
  if (!Number.isSafeInteger(resultLimit) || resultLimit < 1 || resultLimit > 64)
    throw new Error('math_corpus_invalid_limit');
  if (!Number.isSafeInteger(offset) || offset < 0) throw new Error('math_corpus_invalid_offset');
  const { corpus, sources } = verifyMathRetrievalCorpus(root, value);
  const ranked = rankInstalledLeanSources(sources, symbolicMathTokens(query)).toSorted(
    (a, b) =>
      b.score - a.score ||
      compare(a.premise.declarationName, b.premise.declarationName) ||
      compare(a.premise.sourceModule, b.premise.sourceModule) ||
      compare(a.premise.sourceFile, b.premise.sourceFile)
  );
  const premises = ranked
    .slice(offset, offset + resultLimit)
    .map(({ premise }, index) => ({ ...premise, providerRank: offset + index + 1 }));
  return {
    premises,
    attempts: [{ scope: 'frozen-corpus', status: 'ok' as const, resultCount: premises.length }],
    corpusDigest: mathDigest(canonicalMathJson(corpus)),
    coverage: {
      sourceFiles: sources.length,
      complete: true,
      matchedDeclarations: ranked.length,
      nextOffset: offset + premises.length < ranked.length ? offset + premises.length : null,
      semantics: 'lexical-declaration-headers' as const,
    },
  };
}

/** Only trusted process startup configuration selects a frozen corpus, never model tool arguments. */
export function readMathRetrievalCorpusEnvironment(
  env: NodeJS.ProcessEnv = process.env,
  runtimeEntry?: string
): MathRetrievalCorpus | undefined {
  const file = env[MATH_RETRIEVAL_CORPUS_ENV];
  const expected = env[MATH_RETRIEVAL_CORPUS_SHA_ENV];
  if (file === undefined && expected === undefined) return undefined;
  if (!file || !path.isAbsolute(file) || !expected || !digestSchema.safeParse(expected).success) {
    throw new Error('math_corpus_configuration_invalid');
  }
  const bytes = readSource(path.dirname(file), path.basename(file));
  if (mathDigest(bytes) !== expected) throw new Error('math_corpus_manifest_changed');
  const corpus = corpusSchema.parse(JSON.parse(new TextDecoder('utf-8', { fatal: true }).decode(bytes)));
  if (Boolean(corpus.implementation) !== Boolean(corpus.originSha256))
    throw new Error('math_corpus_implementation_missing');
  if (runtimeEntry && corpus.implementation) verifyMathRetrievalImplementation(runtimeEntry, corpus.implementation);
  return corpus;
}
