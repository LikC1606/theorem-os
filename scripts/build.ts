#!/usr/bin/env bun
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { fileURLToPath } from 'node:url';
import { build } from 'esbuild';
import { mathBuildFile, mathBuildSource, MATH_RUNTIME_BUNDLES } from '../src/math/mathBuildManifest';
import { canonicalMathJson, writeMathJsonDurable, syncMathDirectory } from '../src/math/mathRuntimeIo';
import { isMathPathWithin } from '../src/math/paths';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const args = process.argv.slice(2);
const option = (name: string): string | undefined => {
  const index = args.indexOf(name);
  if (index < 0) return undefined;
  const value = args[index + 1];
  if (!value || value.startsWith('--')) throw new Error(`Missing value for ${name}`);
  return value;
};
if (args.includes('--help') || args.includes('-h')) {
  console.log('Usage: bun run build [--state-root DIRECTORY]\nBuilds the isolated mathematics solver.');
} else {
  const startedAt = new Date().toISOString();
  const stateRoot = path.resolve(option('--state-root') || path.join(root, '..', '.deepscientist-math-standalone-state'));
  if (isMathPathWithin(root, stateRoot)) throw new Error('math_build_state_root_must_be_external');
  const source = mathBuildSource(root);
  const bundleRoot = path.join(root, 'out', 'main');
  fs.rmSync(bundleRoot, { recursive: true, force: true });
  // Reject any reintroduced desktop dependency instead of leaving a runtime stub.
  await build({
    entryPoints: {
      'math-solver': path.join(root, 'scripts/mathematics/runMathProof.ts'),
      'search-lean': path.join(root, 'scripts/mathematics/searchLean.ts'),
      'check-lean': path.join(root, 'scripts/mathematics/checkLean.ts'),
    },
    outdir: bundleRoot,
    bundle: true,
    platform: 'node',
    format: 'cjs',
    tsconfig: path.join(root, 'tsconfig.json'),
    metafile: true,
    logLevel: 'silent',
    plugins: [{ name: 'no-desktop-runtime', setup(build) {
      build.onResolve({ filter: /^(?:electron|react|react-dom|@office-ai\/platform)(?:\/|$)/ }, ({ path }) => {
        throw new Error(`Desktop dependency is forbidden: ${path}`);
      });
    } }],
  });
  if (canonicalMathJson(mathBuildSource(root)) !== canonicalMathJson(source)) throw new Error('math_runtime_build_inputs_changed');
  const buildId = crypto.randomUUID();
  const directory = path.join(stateRoot, 'builds', buildId);
  fs.mkdirSync(directory, { recursive: true, mode: 0o700 });
  const manifest = path.join(directory, 'manifest.json');
  writeMathJsonDurable(manifest, {
    schema: 'deepscientist.math.build-manifest.v1', buildId, startedAt, finishedAt: new Date().toISOString(), source,
    bundleRoot,
    bundles: MATH_RUNTIME_BUNDLES.map(name => mathBuildFile(path.join(bundleRoot, name))),
  });
  fs.chmodSync(manifest, 0o400);
  const fd = fs.openSync(manifest, 'r');
  try { fs.fsyncSync(fd); } finally { fs.closeSync(fd); }
  syncMathDirectory(directory);
  console.log(JSON.stringify({ buildId, buildManifestRef: manifest, bundleRoot, bundleCount: MATH_RUNTIME_BUNDLES.length }));
}
