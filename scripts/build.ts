#!/usr/bin/env bun
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { fileURLToPath } from 'node:url';
import { build } from 'esbuild';
import { mathBuildFile, mathBuildSource, MATH_RUNTIME_BUNDLES } from '../src/math/mathBuildManifest';
import { canonicalMathJson, writeMathJsonDurable, syncMathDirectory } from '../src/math/mathRuntimeIo';
import { isMathPathWithin } from '../src/math/mathRunBinding';

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
  console.log('Usage: bun run build [--state-root DIRECTORY]\nBuilds the mathematics runtime and headless MCP bundles using Bun.');
} else {
  const startedAt = new Date().toISOString();
  const core = fs.realpathSync(process.execPath);
  const stateRoot = path.resolve(option('--state-root') || path.join(root, '..', '.deepscientist-math-standalone-state'));
  if (isMathPathWithin(root, stateRoot)) throw new Error('math_build_state_root_must_be_external');
  const source = mathBuildSource(root);
  const targets = [
    ['builtin-mcp-research-team.js', 'src/team/researchTeamServer.ts'],
    ['builtin-mcp-science-artifact.js', 'src/mcp/scienceArtifactServer.ts'],
    ['builtin-mcp-research-evidence.js', 'src/mcp/researchEvidenceServer.ts'],
    ['math-evaluator-supervisor.js', 'src/math/mathEvaluatorSupervisor.ts'],
    ['math-model-isolation.js', 'src/math/mathModelIsolationLauncher.ts'],
    ['math-conjecture-worker.js', 'src/workers/mathConjectureWorker.ts'],
    ['math-runtime.js', 'scripts/startRuntime.ts'],
  ] as const;
  const mcpRoot = path.join(root, 'out', 'main');
  // Reject any reintroduced desktop dependency instead of leaving a runtime stub.
  const builds = await Promise.all(targets.map(([name, entry]) => build({
    entryPoints: [path.join(root, entry)],
    outfile: path.join(mcpRoot, name),
    bundle: true,
    platform: 'node',
    format: 'cjs',
    tsconfig: path.join(root, 'tsconfig.json'),
    metafile: true,
    logLevel: 'silent',
    define: { 'import.meta.url': JSON.stringify('file:///standalone-math-runtime') },
    plugins: [{ name: 'no-desktop-runtime', setup(build) {
      build.onResolve({ filter: /^(?:electron|react|react-dom|@office-ai\/platform)(?:\/|$)/ }, ({ path }) => {
        throw new Error(`Desktop dependency is forbidden: ${path}`);
      });
    } }],
  })));
  if (canonicalMathJson(mathBuildSource(root)) !== canonicalMathJson(source)) throw new Error('math_runtime_build_inputs_changed');
  const buildId = crypto.randomUUID();
  const directory = path.join(stateRoot, 'builds', buildId);
  fs.mkdirSync(directory, { recursive: true, mode: 0o700 });
  const manifest = path.join(directory, 'manifest.json');
  writeMathJsonDurable(manifest, {
    schema: 'deepscientist.math.build-manifest.v1', buildId, startedAt, finishedAt: new Date().toISOString(), source,
    versions: { node: process.version, bun: process.versions.bun ?? 'not_used', rust: 'not_used', cargo: 'not_used' },
    environment: { NODE_ENV: process.env.NODE_ENV ?? '', RUSTFLAGS: '', CARGO_PROFILE_RELEASE_LTO: '' },
    core: mathBuildFile(core), mcpRoot,
    bundles: MATH_RUNTIME_BUNDLES.map(name => mathBuildFile(path.join(mcpRoot, name))),
  });
  fs.chmodSync(manifest, 0o400);
  const fd = fs.openSync(manifest, 'r');
  try { fs.fsyncSync(fd); } finally { fs.closeSync(fd); }
  syncMathDirectory(directory);
  console.log(JSON.stringify({ buildId, buildManifestRef: manifest, mcpRoot, bundleCount: builds.length }));
}
