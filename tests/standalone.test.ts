import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import crypto from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { afterEach, describe, expect, it } from 'vitest';
import { mathBuildFile, mathBuildSource, readMathBuildManifest, MATH_BUILD_INPUTS, MATH_RUNTIME_BUNDLES } from '../src/math/mathBuildManifest';

const roots: string[] = [];
const temp = () => {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'standalone-math-'));
  roots.push(directory);
  return directory;
};
afterEach(() => { for (const directory of roots.splice(0)) fs.rmSync(directory, { recursive: true, force: true }); });

describe('standalone build identity', () => {
  function fixture() {
    const directory = temp();
    const root = path.join(directory, 'source');
    fs.mkdirSync(root);
    for (const relative of MATH_BUILD_INPUTS) {
      const file = path.join(root, relative);
      fs.mkdirSync(path.dirname(file), { recursive: true });
      fs.writeFileSync(file, 'fixture');
    }
    fs.writeFileSync(path.join(root, 'extraction.json'), JSON.stringify({ schema: 'deepscientist.math.extraction.v1', sourceCommit: 'a'.repeat(40) }));
    for (const name of ['src', 'resources']) fs.mkdirSync(path.join(root, name));
    const source = path.join(root, 'src', 'Proof.ts');
    fs.writeFileSync(source, 'export const originalTarget = true;');
    const mcpRoot = path.join(directory, 'bundles');
    fs.mkdirSync(mcpRoot);
    for (const name of MATH_RUNTIME_BUNDLES) fs.writeFileSync(path.join(mcpRoot, name), 'bundle');
    const binary = path.join(directory, 'core');
    fs.writeFileSync(binary, 'binary');
    const manifest = {
      schema: 'deepscientist.math.build-manifest.v1', buildId: crypto.randomUUID(),
      startedAt: new Date(100).toISOString(), finishedAt: new Date(200).toISOString(),
      source: mathBuildSource(root),
      versions: { node: 'node', bun: 'bun', rust: 'prebuilt_core', cargo: 'not_used' },
      environment: {}, core: mathBuildFile(binary), mcpRoot,
      bundles: MATH_RUNTIME_BUNDLES.map(name => mathBuildFile(path.join(mcpRoot, name))),
    };
    const file = path.join(directory, 'manifest.json');
    fs.writeFileSync(file, JSON.stringify(manifest));
    fs.chmodSync(file, 0o400);
    return { root, source, mcpRoot, file, manifest };
  }
  it('loads without a Git repository and rejects a changed mathematical source', () => {
    const f = fixture();
    expect(readMathBuildManifest(f.file, f.root, f.mcpRoot)).toEqual(f.manifest);
    fs.writeFileSync(f.source, 'export const originalTarget = false;');
    expect(() => readMathBuildManifest(f.file, f.root, f.mcpRoot)).toThrow('math_build_source_changed');
  });
  it('rejects changed runtime bundles', () => {
    const f = fixture();
    fs.writeFileSync(path.join(f.mcpRoot, MATH_RUNTIME_BUNDLES[0]), 'changed');
    expect(() => readMathBuildManifest(f.file, f.root, f.mcpRoot)).toThrow('math_build_artifact_changed');
  });
  it('rejects source links into an external checkout', () => {
    const f = fixture();
    fs.symlinkSync(f.source, path.join(f.root, 'src', 'external.ts'));
    expect(() => mathBuildSource(f.root)).toThrow('math_build_source_symlink');
  });
});

describe('standalone CLI process boundary', () => {
  const cli = path.resolve('bin/math.ts');
  it('starts the supplied Core on loopback and preserves arguments containing spaces', () => {
    const root = temp();
    const bundle = path.join(root, 'core bundle');
    fs.mkdirSync(path.join(bundle, 'managed-resources'), { recursive: true });
    const binary = path.join(bundle, 'deepscientist-core');
    fs.writeFileSync(binary, '#!/usr/bin/env node\nprocess.stdout.write(JSON.stringify(process.argv.slice(2)));\n');
    fs.chmodSync(binary, 0o700);
    const data = path.join(root, 'data with spaces');
    const result = spawnSync('bun', [cli, 'core', '--bundle', bundle, '--data-dir', data, '--port', '25821'], {
      cwd: root, encoding: 'utf8', timeout: 10_000, maxBuffer: 32_768,
      env: { ...process.env, CODEX_HOME: path.join(root, 'isolated-profile') },
    });
    expect(result.status).toBe(0);
    const args = JSON.parse(result.stdout);
    expect(args).toEqual(expect.arrayContaining(['127.0.0.1', '--local', data, '25821', '--managed-resources-mode', 'bundled']));
  });
  it('propagates a failing child exit code', () => {
    const root = temp();
    fs.mkdirSync(path.join(root, 'managed-resources'));
    const binary = path.join(root, 'deepscientist-core');
    fs.writeFileSync(binary, '#!/usr/bin/env node\nprocess.exit(7);\n');
    fs.chmodSync(binary, 0o700);
    const result = spawnSync('bun', [cli, 'core', '--bundle', root], { encoding: 'utf8', timeout: 10_000, maxBuffer: 32_768 });
    expect(result.status).toBe(7);
  });
});

describe('portable Core bundle import', () => {
  function fixture() {
    const root = temp();
    const source = path.join(root, 'supplied');
    fs.mkdirSync(path.join(source, 'managed-resources', 'node'), { recursive: true });
    fs.mkdirSync(path.join(source, 'managed-resources', 'acp'));
    fs.writeFileSync(path.join(source, 'manifest.json'), JSON.stringify({ platform: process.platform, arch: process.arch, version: 'v0.1.50' }));
    fs.writeFileSync(path.join(source, 'managed-resources', 'manifest.json'), '{}');
    fs.writeFileSync(path.join(source, 'deepscientist-core'), 'fixture binary');
    const script = path.join(root, 'standalone', 'scripts', 'importCore.ts');
    fs.mkdirSync(path.dirname(script), { recursive: true });
    fs.copyFileSync(path.resolve('scripts/importCore.ts'), script);
    return { root, source, script, target: path.join(root, 'standalone', 'runtime', `${process.platform}-${process.arch}`) };
  }
  it('rebinds historical absolute links to the corresponding bundled file', () => {
    const f = fixture();
    const file = path.join(f.source, 'managed-resources', 'node', 'npm-cli.js');
    fs.writeFileSync(file, 'fixture npm');
    fs.symlinkSync('/discarded-build/managed-resources/node/npm-cli.js', path.join(f.source, 'managed-resources', 'node', 'npm'));
    const result = spawnSync('bun', [f.script, '--bundle', f.source], { encoding: 'utf8', timeout: 10_000, maxBuffer: 32_768 });
    expect(result.status).toBe(0);
    const link = path.join(f.target, 'managed-resources', 'node', 'npm');
    expect(path.isAbsolute(fs.readlinkSync(link))).toBe(false);
    expect(fs.realpathSync(link)).toBe(path.join(f.target, 'managed-resources', 'node', 'npm-cli.js'));
  });
  it('rejects external links that have no shipped counterpart before copying', () => {
    const f = fixture();
    fs.symlinkSync('/external-private-file', path.join(f.source, 'managed-resources', 'node', 'npm'));
    const result = spawnSync('bun', [f.script, '--bundle', f.source], { encoding: 'utf8', timeout: 10_000, maxBuffer: 32_768 });
    expect(result.status).not.toBe(0);
    expect(fs.existsSync(f.target)).toBe(false);
  });
});
