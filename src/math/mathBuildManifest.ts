import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { z } from 'zod';
import { assertMathCanonicalPath, isMathPathWithin } from './paths';
import { canonicalMathJson, readMathJson } from './mathRuntimeIo';

const hash = z.string().regex(/^[a-f0-9]{64}$/u);
const fileSchema = z.object({ path: z.string(), bytes: z.number().int().nonnegative(), sha256: hash }).strict();
const sourceSchema = z.object({
  root: z.string(), commit: z.string().regex(/^[a-f0-9]{40,64}$/u), submodules: z.array(z.object({ path: z.string(), commit: z.string() }).strict()),
  inputs: z.array(fileSchema),
}).strict();
const schema = z.object({
  schema: z.literal('deepscientist.math.build-manifest.v1'), buildId: z.string().uuid(),
  startedAt: z.string().datetime(), finishedAt: z.string().datetime(), source: sourceSchema,
  bundleRoot: z.string(), bundles: z.array(fileSchema).length(3),
}).strict();
export type MathBuildManifest = Readonly<z.infer<typeof schema>>;
export const MATH_RUNTIME_BUNDLES = ['math-solver.js', 'search-lean.js', 'check-lean.js'] as const;
export const MATH_BUILD_INPUTS = ['bun.lock', 'package.json', 'tsconfig.json', 'extraction.json', 'scripts/build.ts', 'bin/math.ts', 'scripts/mathematics/searchLean.ts'] as const;

export function mathBuildFile(file: string): z.infer<typeof fileSchema> {
  assertMathCanonicalPath(file);
  const fd = fs.openSync(file, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW);
  try {
    const stat = fs.fstatSync(fd, { bigint: true });
    if (!stat.isFile() || stat.nlink !== BigInt(1)) throw new Error('math_build_file_invalid');
    const digest = crypto.createHash('sha256');
    const buffer = Buffer.alloc(64 * 1024);
    let bytes = 0;
    for (;;) { const count = fs.readSync(fd, buffer, 0, buffer.length, bytes); if (!count) break; digest.update(buffer.subarray(0, count)); bytes += count; }
    const after = fs.fstatSync(fd, { bigint: true });
    const named = fs.lstatSync(file, { bigint: true });
    if (stat.size !== after.size || stat.mtimeNs !== after.mtimeNs || stat.ctimeNs !== after.ctimeNs ||
        stat.dev !== named.dev || stat.ino !== named.ino) throw new Error('math_build_file_changed');
    return { path: file, bytes, sha256: digest.digest('hex') };
  } finally { fs.closeSync(fd); }
}

export function mathBuildSource(root: string, inputPaths: readonly string[] = MATH_BUILD_INPUTS): z.infer<typeof sourceSchema> {
  assertMathCanonicalPath(root);
  const provenance = z.object({ schema: z.literal('deepscientist.math.extraction.v1'), sourceCommit: z.string().regex(/^[a-f0-9]{40,64}$/u) }).parse(readMathJson(path.join(root, 'extraction.json')));
  const paths = new Set(inputPaths);
  const collect = (directory: string): void => {
    const absolute = path.join(root, directory); assertMathCanonicalPath(absolute);
    for (const entry of fs.readdirSync(absolute, { withFileTypes: true })) {
      const relative = path.join(directory, entry.name);
      if (entry.isSymbolicLink()) throw new Error('math_build_source_symlink');
      if (entry.isDirectory()) collect(relative); else if (entry.isFile()) paths.add(relative); else throw new Error('math_build_source_invalid');
    }
  };
  for (const directory of ['src', 'scripts', 'bin', 'resources']) if (fs.existsSync(path.join(root, directory))) collect(directory);
  const inputs = [...paths].toSorted().map(relative => {
    const file = path.resolve(root, relative);
    if (!isMathPathWithin(root, file) || file === root) throw new Error('math_build_input_invalid');
    return mathBuildFile(file);
  });
  return { root, commit: provenance.sourceCommit, submodules: [], inputs };
}

export function readMathBuildManifest(file: string, root: string, bundleRoot: string): MathBuildManifest {
  assertMathCanonicalPath(file);
  if ((fs.lstatSync(file).mode & 0o222) !== 0) throw new Error('math_build_manifest_not_frozen');
  const parsed = schema.safeParse(readMathJson(file));
  if (!parsed.success) throw new Error('math_build_manifest_invalid');
  const manifest = parsed.data;
  if (manifest.source.root !== root || manifest.bundleRoot !== bundleRoot ||
      MATH_RUNTIME_BUNDLES.some(name => !manifest.bundles.some(item => item.path === path.join(bundleRoot, name)))) throw new Error('math_build_manifest_identity');
  if (canonicalMathJson(mathBuildSource(root)) !== canonicalMathJson(manifest.source)) throw new Error('math_build_source_changed');
  for (const entry of manifest.bundles) if (canonicalMathJson(mathBuildFile(entry.path)) !== canonicalMathJson(entry)) throw new Error('math_build_artifact_changed');
  return manifest;
}
