import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import crypto from 'node:crypto';
import { spawn, spawnSync, type ChildProcess } from 'node:child_process';
import { createInterface } from 'node:readline';
import { afterEach, describe, expect, it } from 'vitest';
import { mathBuildFile, mathBuildSource, readMathBuildManifest, verifyMathRuntimeProcess, MATH_BUILD_INPUTS, MATH_RUNTIME_BUNDLES } from '../src/math/mathBuildManifest';

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
  const project = path.resolve('.');
  const cli = path.join(project, 'bin/math.ts');
  const children: ChildProcess[] = [];
  afterEach(async () => {
    await Promise.all(children.splice(0).map(async child => {
      if (child.exitCode !== null) return;
      const closed = new Promise<void>(resolve => child.once('close', () => resolve()));
      child.kill('SIGTERM');
      await closed;
    }));
  });
  async function ready(args: string[]) {
    const child = spawn('bun', args, { stdio: ['ignore', 'pipe', 'pipe'] });
    children.push(child);
    let diagnostics = '';
    child.stderr!.on('data', data => { diagnostics = (diagnostics + data).slice(-4096); });
    const lines = createInterface({ input: child.stdout! });
    const value = await new Promise<any>((resolve, reject) => {
      const timer = setTimeout(() => reject(new Error('runtime readiness timeout')), 10_000);
      lines.once('line', line => { clearTimeout(timer); try { resolve(JSON.parse(line)); } catch (error) { reject(error); } });
      child.once('exit', () => { clearTimeout(timer); reject(new Error(diagnostics)); });
      child.once('error', reject);
    });
    lines.close();
    return { child, value };
  }
  async function stop(child: ChildProcess) {
    const closed = new Promise<number | null>(resolve => child.once('close', code => resolve(code)));
    child.kill('SIGTERM');
    expect(await closed).toBe(0);
  }
  it('starts the bundled Bun runtime on loopback, verifies its identity and forwards shutdown', async () => {
    const directory = path.join(temp(), 'data with spaces');
    const { child, value } = await ready([cli, 'runtime', '--data-dir', directory, '--port', '0']);
    expect(new URL(value.runtimeUrl).hostname).toBe('127.0.0.1');
    const response = await fetch(`${value.runtimeUrl}/api/conversations/runtime-capabilities`);
    const { data } = await response.json() as any;
    expect(data.math_run_inputs.supported_versions).toContain(2);
    const binary = fs.realpathSync(`/proc/${value.pid}/exe`);
    const mcpRoot = path.join(project, 'out/main');
    const manifest = { core: mathBuildFile(binary), mcpRoot,
      bundles: [mathBuildFile(path.join(mcpRoot, 'math-runtime.js'))] };
    expect(() => verifyMathRuntimeProcess(manifest as any, data)).not.toThrow();
    expect(() => verifyMathRuntimeProcess(manifest as any, { ...data, runtime_entry: {} })).toThrow();
    const ws = new WebSocket(value.runtimeUrl.replace('http:', 'ws:') + '/ws');
    const subscription = new Promise<any>((resolve, reject) => {
      ws.onopen = () => ws.send(JSON.stringify({ name: 'runtime.subscribe' }));
      ws.onmessage = message => resolve(JSON.parse(String(message.data)));
      ws.onerror = reject;
    });
    expect((await subscription).name).toBe('runtime.subscriptionReady');
    ws.close();
    await stop(child);
    expect(fs.existsSync(path.join(directory, 'math-runtime.lock'))).toBe(false);
    expect(() => process.kill(value.pid, 0)).toThrow();
  });
  it('reuses a private per-output endpoint and shuts down the owned host', async () => {
    const directory = temp();
    const output = path.join(directory, 'run with spaces.json');
    const driver = path.join(directory, 'launch.ts');
    fs.writeFileSync(driver, `import { launchMathRuntime } from ${JSON.stringify(path.join(project, 'src/runtime/launchRuntime.ts'))};
const runtime = await launchMathRuntime(${JSON.stringify(project)}, ${JSON.stringify(output)}, process.env);
console.log(JSON.stringify({ runtimeUrl: runtime.runtimeUrl }));
process.once('SIGTERM', async () => { await runtime.stop(); process.exit(0); });
`);
    const first = await ready([driver]);
    await stop(first.child);
    const second = await ready([driver]);
    expect(second.value.runtimeUrl).toBe(first.value.runtimeUrl);
    await stop(second.child);
    expect(fs.existsSync(`${output}.runtime/math-runtime.lock`)).toBe(false);
  });
  it('automatically stops the runtime when the proof runner rejects invalid arguments', () => {
    const output = path.join(temp(), 'run.json');
    const result = spawnSync('bun', [cli, 'run', '--output', output], { encoding: 'utf8', timeout: 10_000, maxBuffer: 16_384 });
    expect(result.status).toBe(1);
    expect(fs.existsSync(`${output}.runtime/endpoint.json`)).toBe(true);
    expect(fs.existsSync(`${output}.runtime/math-runtime.lock`)).toBe(false);
  });
});
