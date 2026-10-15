import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import crypto from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { afterEach, describe, expect, it, vi } from 'vitest';
import { writeMathJsonDurable } from '../src/math/mathRuntimeIo';
import { mathBuildFile, mathBuildSource, readMathBuildManifest, MATH_BUILD_INPUTS, MATH_RUNTIME_BUNDLES } from '../src/math/mathBuildManifest';

const roots: string[] = [];
const temp = () => {
  const directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'standalone-math-')));
  roots.push(directory);
  return directory;
};
afterEach(() => {
  vi.restoreAllMocks();
  for (const directory of roots.splice(0)) fs.rmSync(directory, { recursive: true, force: true });
});

describe('standalone build identity', () => {
  it('reuses unchanged file hashes and detects edits with restored modification times', () => {
    const root = temp(), file = path.join(root, 'input.txt');
    fs.writeFileSync(file, 'original');
    const before = mathBuildFile(file), stat = fs.statSync(file);
    const read = vi.spyOn(fs, 'readSync');
    expect(mathBuildFile(file)).toEqual(before);
    expect(read).not.toHaveBeenCalled();
    fs.writeFileSync(file, 'modified');
    fs.utimesSync(file, stat.atime, stat.mtime);
    expect(mathBuildFile(file).sha256).not.toBe(before.sha256);
    expect(read).toHaveBeenCalled();
    fs.writeFileSync(file + '.new', 'replacement');
    fs.renameSync(file + '.new', file);
    expect(mathBuildFile(file).sha256).toBe(crypto.createHash('sha256').update('replacement').digest('hex'));
  });

  it('avoids identical durable writes while repairing modified or missing outputs', () => {
    const root = temp(), file = path.join(root, 'state.json'), value = { turns: 1 };
    writeMathJsonDurable(file, value);
    const rename = vi.spyOn(fs, 'renameSync');
    writeMathJsonDurable(file, value);
    expect(rename).not.toHaveBeenCalled();
    fs.writeFileSync(file, 'changed');
    writeMathJsonDurable(file, value);
    expect(JSON.parse(fs.readFileSync(file, 'utf8'))).toEqual(value);
    fs.unlinkSync(file);
    writeMathJsonDurable(file, value);
    expect(JSON.parse(fs.readFileSync(file, 'utf8'))).toEqual(value);
    expect(rename).toHaveBeenCalledTimes(2);
  });

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
    const source = path.join(root, 'src', 'Proof.ts');
    fs.mkdirSync(path.dirname(source));
    fs.writeFileSync(source, 'export const originalTarget = true;');
    const bundleRoot = path.join(directory, 'bundles');
    fs.mkdirSync(bundleRoot);
    for (const name of MATH_RUNTIME_BUNDLES) fs.writeFileSync(path.join(bundleRoot, name), 'bundle');
    const manifest = {
      schema: 'deepscientist.math.build-manifest.v1', buildId: crypto.randomUUID(),
      startedAt: new Date(100).toISOString(), finishedAt: new Date(200).toISOString(),
      source: mathBuildSource(root), bundleRoot,
      bundles: MATH_RUNTIME_BUNDLES.map(name => mathBuildFile(path.join(bundleRoot, name))),
    };
    const file = path.join(directory, 'manifest.json');
    fs.writeFileSync(file, JSON.stringify(manifest));
    fs.chmodSync(file, 0o400);
    return { root, source, bundleRoot, file, manifest };
  }
  it('loads without a Git repository and rejects a changed mathematical source', () => {
    const f = fixture();
    expect(readMathBuildManifest(f.file, f.root, f.bundleRoot)).toEqual(f.manifest);
    fs.writeFileSync(f.source, 'export const originalTarget = false;');
    expect(() => readMathBuildManifest(f.file, f.root, f.bundleRoot)).toThrow('math_build_source_changed');
  });
  it('rejects changed solver bundles', () => {
    const f = fixture();
    fs.writeFileSync(path.join(f.bundleRoot, MATH_RUNTIME_BUNDLES[0]), 'changed');
    expect(() => readMathBuildManifest(f.file, f.root, f.bundleRoot)).toThrow('math_build_artifact_changed');
  });
  it('rejects source links into an external checkout', () => {
    const f = fixture();
    fs.symlinkSync(f.source, path.join(f.root, 'src', 'external.ts'));
    expect(() => mathBuildSource(f.root)).toThrow('math_build_source_symlink');
  });
  it('rejects writable manifests and unexpected extra bundles', () => {
    const f = fixture();
    fs.chmodSync(f.file, 0o600);
    expect(() => readMathBuildManifest(f.file, f.root, f.bundleRoot)).toThrow('math_build_manifest_not_frozen');
    fs.writeFileSync(f.file, JSON.stringify({ ...f.manifest, bundles: [...f.manifest.bundles, f.manifest.bundles[0]] }));
    fs.chmodSync(f.file, 0o400);
    expect(() => readMathBuildManifest(f.file, f.root, f.bundleRoot)).toThrow('math_build_manifest_invalid');
  });
});

describe('standalone CLI', () => {
  const cli = path.resolve('bin/math.ts');
  it('supports the search subcommand in an isolated direct-script wrapper', () => {
    const result = spawnSync('bun', ['scripts/mathematics/searchLean.ts', 'search-lean', '--help'],
      { encoding: 'utf8', timeout: 10_000, maxBuffer: 16384 });
    expect(result.status).toBe(0);
    expect(result.stdout).toContain('Usage: theorem-os search-lean');
  });
  it('lists the mathematical commands and rejects the removed runtime command', () => {
    const help = spawnSync('bun', [cli, '--help'], { encoding: 'utf8', timeout: 10_000, maxBuffer: 16_384 });
    expect(help.status).toBe(0);
    expect(help.stdout).toContain('bootstrap-imo');
    for (const command of ['doctor', 'example', 'component']) {
      expect(help.stdout).toContain(command);
      const commandHelp = spawnSync('bun', [cli, command, '--help'], { encoding: 'utf8', timeout: 10_000, maxBuffer: 16_384 });
      expect(commandHelp.status, commandHelp.stderr).toBe(0);
      expect(commandHelp.stdout).toContain(`theorem-os ${command}`);
    }
    const runtime = spawnSync('bun', [cli, 'runtime'], { encoding: 'utf8', timeout: 10_000, maxBuffer: 16_384 });
    expect(runtime.status).toBe(1);
    expect(runtime.stderr).toContain('Unknown command: runtime');
  });
  it('rejects invalid solver arguments without starting a background service', () => {
    const output = path.join(temp(), 'run.json');
    const result = spawnSync('bun', ['scripts/mathematics/runMathProof.ts', '--output', output], { encoding: 'utf8', timeout: 10_000, maxBuffer: 16_384 });
    expect(result.status).toBe(1);
    expect(result.stderr).toContain('--workspace is required');
    expect(fs.existsSync(output + '.runtime')).toBe(false);
  });
});
