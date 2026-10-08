import fs from 'node:fs';
import path from 'node:path';
import { z } from 'zod';
import crypto from 'node:crypto';
import { assertMathCanonicalPath, isMathPathWithin } from "./mathRunBinding";
import { canonicalMathJson, readMathJson } from "./mathRuntimeIo";

const hash = z.string().regex(/^[a-f0-9]{64}$/u);
const fileSchema = z.object({ path: z.string(), bytes: z.number().int().nonnegative().safe(), sha256: hash }).strict();
const snapshotFileSchema = z
  .object({
    path: z.string(),
    kind: z.enum(['file', 'symlink', 'deleted']),
    bytes: z.number().int().nonnegative().safe(),
    sha256: hash,
    executable: z.boolean(),
  })
  .strict();
const snapshotSchema = z
  .object({ kind: z.literal('local_working_tree'), files: z.array(snapshotFileSchema), sha256: hash })
  .strict();
const sourceSchema = z
  .object({
    root: z.string(),
    commit: z.string().regex(/^[a-f0-9]{40}(?:[a-f0-9]{24})?$/u),
    submodules: z.array(z.object({ path: z.string(), commit: z.string() }).strict()),
    inputs: z.array(fileSchema),
    workingTreeSnapshot: snapshotSchema.optional(),
  })
  .strict();
const schema = z
  .object({
    schema: z.literal('deepscientist.math.build-manifest.v1'),
    buildId: z.string().uuid(),
    startedAt: z.string().datetime(),
    finishedAt: z.string().datetime(),
    source: sourceSchema,
    versions: z.object({ node: z.string(), bun: z.string(), rust: z.string(), cargo: z.string() }).strict(),
    environment: z.record(z.string(), z.string()),
    core: fileSchema,
    mcpRoot: z.string(),
    bundles: z.array(fileSchema).min(4),
  })
  .strict();
export type MathBuildManifest = Readonly<z.infer<typeof schema>>;
export const MATH_RUNTIME_BUNDLES = [
  'builtin-mcp-research-team.js',
  'builtin-mcp-science-artifact.js',
  'builtin-mcp-research-evidence.js',
  'math-evaluator-supervisor.js',
  'math-model-isolation.js',
  'math-conjecture-worker.js',
] as const;
export const MATH_BUILD_INPUTS = [
  'bun.lock', 'package.json', '.npmrc', 'tsconfig.json', 'extraction.json',
  'scripts/build.ts', 'scripts/startCore.ts', 'bin/math.ts',
] as const;

function hashDescriptor(fd: number): Readonly<{ bytes: number; sha256: string }> {
  const digest = crypto.createHash('sha256');
  const buffer = Buffer.alloc(65536);
  let bytes = 0;
  for (;;) {
    const count = fs.readSync(fd, buffer, 0, buffer.length, bytes);
    if (!count) break;
    digest.update(buffer.subarray(0, count));
    bytes += count;
  }
  return { bytes, sha256: digest.digest('hex') };
}

export function mathBuildFile(file: string): z.infer<typeof fileSchema> {
  assertMathCanonicalPath(file);
  const fd = fs.openSync(file, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK);
  try {
    const before = fs.fstatSync(fd, { bigint: true });
    if (!before.isFile() || before.nlink !== BigInt(1)) throw new Error('math_build_file_invalid');
    // Bundles and binaries may be large; hash without retaining the entire file.
    const digest = hashDescriptor(fd);
    const after = fs.fstatSync(fd, { bigint: true });
    const named = fs.lstatSync(file, { bigint: true });
    if (
      before.size !== after.size ||
      before.mtimeNs !== after.mtimeNs ||
      before.ctimeNs !== after.ctimeNs ||
      before.dev !== named.dev ||
      before.ino !== named.ino
    )
      throw new Error('math_build_file_changed');
    return { path: file, ...digest };
  } finally {
    fs.closeSync(fd);
  }
}

/** Freeze standalone sources directly; neither the parent checkout nor a Git commit is required. */
export function mathBuildSource(
  root: string,
  inputPaths: readonly string[] = MATH_BUILD_INPUTS,
  _options: Readonly<{ allowWorkingTreeSnapshot?: boolean }> = {}
): z.infer<typeof sourceSchema> {
  assertMathCanonicalPath(root);
  const provenance = z.object({
    schema: z.literal('deepscientist.math.extraction.v1'),
    sourceCommit: z.string().regex(/^[a-f0-9]{40}(?:[a-f0-9]{24})?$/u),
  }).parse(readMathJson(path.join(root, 'extraction.json')));
  const paths = new Set<string>(inputPaths);
  const collect = (directory: string): void => {
    const absolute = path.join(root, directory);
    assertMathCanonicalPath(absolute);
    for (const entry of fs.readdirSync(absolute, { withFileTypes: true })) {
      const relative = path.join(directory, entry.name);
      if (entry.isSymbolicLink()) throw new Error('math_build_source_symlink');
      if (entry.isDirectory()) collect(relative);
      else if (entry.isFile()) paths.add(relative);
      else throw new Error('math_build_source_invalid');
    }
  };
  for (const directory of ['src', 'scripts', 'bin', 'resources']) collect(directory);
  const inputs = [...paths].toSorted().map((relative) => {
    const file = path.resolve(root, relative);
    if (!isMathPathWithin(root, file) || file === root) throw new Error('math_build_input_invalid');
    return mathBuildFile(file);
  });
  return { root, commit: provenance.sourceCommit, submodules: [], inputs };
}

/** Explicit opt-in source descriptor for a local dirty checkout. */
export function mathBuildWorkingTreeSource(
  root: string,
  inputPaths: readonly string[] = MATH_BUILD_INPUTS
): z.infer<typeof sourceSchema> {
  return mathBuildSource(root, inputPaths, { allowWorkingTreeSnapshot: true });
}

export function readMathBuildManifest(file: string, root: string, mcpRoot: string): MathBuildManifest {
  assertMathCanonicalPath(file);
  if ((fs.lstatSync(file).mode & 0o222) !== 0) throw new Error('math_build_manifest_not_frozen');
  const parsed = schema.safeParse(readMathJson(file));
  if (!parsed.success) throw new Error('math_build_manifest_invalid');
  const manifest = parsed.data;
  if (
    manifest.source.root !== root ||
    manifest.mcpRoot !== mcpRoot ||
    new Set(manifest.bundles.map((entry) => entry.path)).size !== manifest.bundles.length ||
    !MATH_RUNTIME_BUNDLES.every((name) => manifest.bundles.some((item) => item.path === path.join(mcpRoot, name)))
  )
    throw new Error('math_build_manifest_identity');
  const sourceOptions = manifest.source.workingTreeSnapshot ? { allowWorkingTreeSnapshot: true } : {};
  if (canonicalMathJson(mathBuildSource(root, MATH_BUILD_INPUTS, sourceOptions)) !== canonicalMathJson(manifest.source))
    throw new Error('math_build_source_changed');
  for (const entry of [manifest.core, ...manifest.bundles]) {
    if (canonicalMathJson(mathBuildFile(entry.path)) !== canonicalMathJson(entry))
      throw new Error('math_build_artifact_changed');
  }
  return manifest;
}

/** The authenticated endpoint identifies the running process, not a caller-supplied binary path. */
export function verifyMathCoreProcess(manifest: MathBuildManifest, capabilities: unknown): void {
  const pid =
    capabilities && typeof capabilities === 'object' && !Array.isArray(capabilities)
      ? (capabilities as Record<string, unknown>).runtime_process_id
      : undefined;
  if (process.platform !== 'linux' || !Number.isSafeInteger(pid) || Number(pid) <= 0)
    throw new Error('math_core_build_identity_unavailable');
  const executable = `/proc/${pid}/exe`;
  try {
    if (fs.realpathSync(executable) !== manifest.core.path) throw new Error();
    // /proc/<pid>/exe is a kernel-owned link; hash its opened image rather than reopening the named binary.
    const fd = fs.openSync(executable, fs.constants.O_RDONLY | fs.constants.O_NONBLOCK);
    try {
      const before = fs.fstatSync(fd, { bigint: true });
      if (!before.isFile() || before.size !== BigInt(manifest.core.bytes)) throw new Error();
      const digest = hashDescriptor(fd);
      const after = fs.fstatSync(fd, { bigint: true });
      const named = fs.lstatSync(manifest.core.path, { bigint: true });
      const running = fs.statSync(executable, { bigint: true });
      if (
        digest.sha256 !== manifest.core.sha256 ||
        digest.bytes !== manifest.core.bytes ||
        before.dev !== named.dev ||
        before.ino !== named.ino ||
        before.dev !== running.dev ||
        before.ino !== running.ino ||
        before.size !== after.size ||
        before.mtimeNs !== after.mtimeNs ||
        before.ctimeNs !== after.ctimeNs ||
        fs.realpathSync(executable) !== manifest.core.path
      )
        throw new Error();
    } finally {
      fs.closeSync(fd);
    }
  } catch {
    throw new Error('math_core_build_identity_mismatch');
  }
}
