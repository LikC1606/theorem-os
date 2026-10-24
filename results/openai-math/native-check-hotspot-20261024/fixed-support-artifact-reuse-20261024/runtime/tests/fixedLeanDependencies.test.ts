import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { FixedLeanDependencyCache } from '../src/math/fixedLeanDependencies';
import { mathLocalModuleBuildOrder } from '../src/math/mathConstructionSources';
import { mathDigest } from '../src/math/mathRuntimeIo';

vi.mock('../src/math/mathProofEnvironment', () => ({ resolveMathProofEnvironment: (_root: string, env: NodeJS.ProcessEnv) =>
  env.FIXTURE_PACKAGES ? { identity: env.FIXTURE_PACKAGES } : undefined }));

describe('host-owned fixed Lean dependency artifacts', () => {
  let root: string, cache: FixedLeanDependencyCache, tools: string;
  const write = (project: string, file: string, bytes: string) => {
    const output = path.join(project, file); fs.mkdirSync(path.dirname(output), { recursive: true }); fs.writeFileSync(output, bytes);
  };
  const artifact = (project: string, suffix = '') => path.join(project, `.lake/build/lib/lean/Support.olean${suffix}`);
  const input = () => ({ projectRoot: root, modules: mathLocalModuleBuildOrder(root, 'Support.lean'),
    trustedFiles: Object.fromEntries(['Base.lean', 'Support.lean'].map(file => [file, mathDigest(fs.readFileSync(path.join(root, file)))])),
    env: { PATH: '/fixture/tools', FIXTURE_PACKAGES: 'sealed-v1' } as NodeJS.ProcessEnv,
    toolIdentity: (_project: string): string | undefined => tools });
  const compile = vi.fn(async (project: string) => {
    expect(fs.existsSync(path.join(project, 'Submission.lean'))).toBe(false);
    expect(mathLocalModuleBuildOrder(project, 'Support.lean').map(module => module.file)).toEqual(['Base.lean', 'Support.lean']);
    for (const name of ['Base', 'Support']) {
      write(project, `.lake/build/lib/lean/${name}.olean`, `kernel-${name}`);
      write(project, `.lake/build/lib/lean/${name}.olean.private`, `private-${name}`);
    }
    return { started: true, exitCode: 0, timedOut: false, stdout: '', stderr: 'support warning\n', durationMs: 19 };
  });
  beforeEach(() => {
    root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'fixed-lean-dependencies-')));
    cache = new FixedLeanDependencyCache(); tools = 'tools-v1'; compile.mockClear();
    write(root, 'lean-toolchain', 'fixture:v1\n'); write(root, 'lakefile.toml', 'name = "fixed_fixture"\n');
    write(root, 'lake-manifest.json', '{"packages":[]}\n');
    write(root, 'Base.lean', 'def base : Nat := 1\n'); write(root, 'Support.lean', 'import Base\ndef fixedValue : Nat := base\n');
    write(root, 'Submission.lean', 'import Support\ntheorem result : fixedValue = 1 := rfl\n');
  });
  afterEach(() => { vi.restoreAllMocks(); cache.dispose(); fs.rmSync(root, { recursive: true, force: true }); });

  it('builds only fixed supports, restores copies across target changes, and preserves companions and warnings', async () => {
    expect(await cache.prepare(input(), compile)).toMatchObject({ kind: 'ready', hit: false, durationMs: 19 });
    write(root, 'Submission.lean', 'import Support\ntheorem result : True := True.intro\n');
    fs.writeFileSync(artifact(root), 'worker corruption');
    fs.rmSync(artifact(root, '.private'));
    write(root, '.lake/build/lib/lean/Support.ir', 'stale worker companion');
    expect(await cache.prepare(input(), compile)).toMatchObject({ kind: 'ready', hit: true, durationMs: 0, stderr: 'support warning\n' });
    expect(compile).toHaveBeenCalledOnce();
    expect(fs.readFileSync(artifact(root), 'utf8')).toBe('kernel-Support');
    expect(fs.readFileSync(artifact(root, '.private'), 'utf8')).toBe('private-Support');
    expect(fs.existsSync(path.join(root, '.lake/build/lib/lean/Support.ir'))).toBe(false);
    const entry = [...(cache as any).entries.values()][0];
    expect(fs.statSync(artifact(root)).ino).not.toBe(fs.statSync(artifact(entry.directory)).ino);
    expect(fs.existsSync(path.join(entry.directory, 'project'))).toBe(false);
  });

  it.each(['source', 'configuration', 'toolchain', 'packages', 'environment', 'locale'] as const)('misses on changed %s identity', async change => {
    await cache.prepare(input(), compile);
    if (change === 'source') write(root, 'Base.lean', 'def base : Nat := 2\n');
    if (change === 'configuration') fs.appendFileSync(path.join(root, 'lakefile.toml'), '# exact configuration changed\n');
    if (change === 'toolchain') tools = 'tools-v2';
    const next = input();
    if (change === 'packages') next.env.FIXTURE_PACKAGES = 'sealed-v2';
    if (change === 'environment') next.env.PATH = '/other/tools';
    if (change === 'locale') next.env.LC_ALL = 'C';
    expect(await cache.prepare(next, compile)).toMatchObject({ kind: 'ready', hit: false });
    expect(compile).toHaveBeenCalledTimes(2);
  });

  it.each(['untrusted', 'incomplete-closure', 'solver-dependency', 'unsealed', 'unknown-tools', 'LEAN_PATH', 'LEAN_SYSROOT', 'lake-script'] as const)
  ('falls back without compiling or publishing for %s inputs', async change => {
    const next = input();
    if (change === 'untrusted') next.trustedFiles['Base.lean'] = '0'.repeat(64);
    if (change === 'incomplete-closure') next.modules = next.modules.slice(-1);
    if (change === 'solver-dependency') {
      write(root, 'Owned.lean', 'def owned : Nat := 1\n');
      write(root, 'Base.lean', 'import Owned\ndef base : Nat := owned\n');
      next.modules = mathLocalModuleBuildOrder(root, 'Support.lean');
      next.trustedFiles['Base.lean'] = mathDigest(fs.readFileSync(path.join(root, 'Base.lean')));
    }
    if (change === 'unsealed') next.env.FIXTURE_PACKAGES = '';
    if (change === 'unknown-tools') next.toolIdentity = () => undefined;
    if (change === 'LEAN_PATH' || change === 'LEAN_SYSROOT') (next.env as NodeJS.ProcessEnv)[change] = '/mutable';
    if (change === 'lake-script') write(root, 'lakefile.lean', 'import Lake\n');
    expect(await cache.prepare(next, compile)).toBeUndefined();
    expect(compile).not.toHaveBeenCalled();
  });

  it('rebuilds corrupted host artifacts and never accepts a missing mandatory olean', async () => {
    await cache.prepare(input(), compile);
    let entry = [...(cache as any).entries.values()][0];
    fs.chmodSync(artifact(entry.directory, '.private'), 0o600);
    fs.writeFileSync(artifact(entry.directory, '.private'), 'corrupted-private');
    expect(await cache.prepare(input(), compile)).toMatchObject({ kind: 'ready', hit: false });
    entry = [...(cache as any).entries.values()][0]; fs.rmSync(artifact(entry.directory));
    expect(await cache.prepare(input(), compile)).toMatchObject({ kind: 'ready', hit: false });
    expect(compile).toHaveBeenCalledTimes(3);
  });

  it('preserves an actual failed compile and publishes nothing until a later successful compile', async () => {
    const failed = { started: true, exitCode: 1, timedOut: false, stdout: 'Lean rejection', stderr: '', durationMs: 3 };
    expect(await cache.prepare(input(), async () => failed)).toEqual({ kind: 'failed', result: failed });
    expect(await cache.prepare(input(), compile)).toMatchObject({ kind: 'ready', hit: false });
  });

  it.each(['compile', 'artifact', 'builder-toolchain', 'builder-source'] as const)('falls back after optional cache %s failure', async failure => {
    const next = input();
    if (failure === 'builder-toolchain') next.toolIdentity = project => project === root ? tools : 'different-builder-tools';
    expect(await cache.prepare(next, async project => {
      if (failure === 'compile') throw new Error('fixture_builder_unavailable');
      const result = await compile(project);
      if (failure === 'artifact') fs.rmSync(artifact(project));
      if (failure === 'builder-source') write(project, 'Base.lean', 'def base : Nat := 4\n');
      return result;
    })).toBeUndefined();
    expect(fs.existsSync(artifact(root))).toBe(false);
    expect(await cache.prepare(input(), compile)).toMatchObject({ kind: 'ready', hit: false });
  });

  it('clears restored artifacts when source identity changes during a warm restore', async () => {
    await cache.prepare(input(), compile);
    const next = input(), save = fs.writeFileSync;
    let mutated = false;
    vi.spyOn(fs, 'writeFileSync').mockImplementation((file, bytes, options) => {
      save(file, bytes, options);
      if (String(file) === artifact(root) && !mutated) {
        mutated = true; save(path.join(root, 'Base.lean'), 'def base : Nat := 3\n');
      }
    });
    expect(await cache.prepare(next, compile)).toBeUndefined();
    expect(fs.existsSync(artifact(root))).toBe(false);
    expect(fs.existsSync(artifact(root, '.private'))).toBe(false);
  });

  it('does not retain artifacts above the process cache capacity', async () => {
    cache.dispose(); cache = new FixedLeanDependencyCache(1);
    expect(await cache.prepare(input(), compile)).toMatchObject({ kind: 'ready', hit: false });
    expect(await cache.prepare(input(), compile)).toMatchObject({ kind: 'ready', hit: false });
    expect(compile).toHaveBeenCalledTimes(2);
  });
});
