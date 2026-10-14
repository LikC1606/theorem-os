import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { prepareMathProofEnvironment, mathProofEnvironmentWorkerEnvironment,
  MATH_PROOF_ENVIRONMENT_ENV, MATH_PROOF_ENVIRONMENT_SANDBOX_ENV } from '../src/math/mathProofEnvironment';
import { projectMathematicsRuntimeEnvironment } from '../src/math/mathRuntimeEnvironment';
import { MATH_SEALED_ENVIRONMENT_HELPER } from '../src/math/mathSealedEnvironmentHelper';

describe.skipIf(process.platform !== 'linux')('proof environment tool preflight', () => {
  let directory: string;
  let tools: string;
  let project: string;
  let packages: string;
  beforeEach(() => {
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'proof-environment-tools-')));
    tools = path.join(directory, 'tools');
    project = path.join(directory, 'project');
    packages = path.join(directory, 'packages');
    for (const root of [tools, project, packages]) fs.mkdirSync(root);
    fs.writeFileSync(path.join(packages, 'Dependency.lean'), 'example : True := by trivial\n');
    for (const name of ['squashfuse', 'fusermount', 'mksquashfs']) {
      fs.writeFileSync(path.join(tools, name), '#!/bin/sh\nexit 99\n', { mode: 0o700 });
    }
  });
  afterEach(() => {
    vi.restoreAllMocks();
    fs.rmSync(directory, { recursive: true, force: true });
  });

  it.each(['squashfuse', 'fusermount', 'mksquashfs'])(
    'rejects missing %s before creating or copying a dependency snapshot', async name => {
      fs.unlinkSync(path.join(tools, name));
      const temporary = vi.spyOn(fs, 'mkdtempSync');
      const phases: string[] = [];
      await expect(prepareMathProofEnvironment(project, packages, {
        env: { PATH: tools }, onProgress: phase => phases.push(phase),
      })).rejects.toThrow('requires squashfuse, fusermount, and mksquashfs');
      expect(phases).toEqual(['enumerating_dependencies', 'cache_miss']);
      expect(temporary).not.toHaveBeenCalled();
    }
  );

  it('requires the compressor for a new image but allows mounting cached images without it', () => {
    fs.unlinkSync(path.join(tools, 'mksquashfs'));
    for (const mode of ['mount', 'build']) {
      const probe = spawnSync('/usr/bin/python3', ['-c', MATH_SEALED_ENVIRONMENT_HELPER, '--check-tools', mode], {
        env: { PATH: tools }, encoding: 'utf8', timeout: 5000, maxBuffer: 4096,
      });
      expect(probe.status).toBe(mode === 'mount' ? 0 : 1);
      expect(JSON.parse(probe.stdout).state).toBe(mode === 'mount' ? 'ready' : 'blocked');
    }
  });

  it('accepts snapfuse and fusermount3 without invoking any of the tools', () => {
    fs.renameSync(path.join(tools, 'squashfuse'), path.join(tools, 'snapfuse'));
    fs.renameSync(path.join(tools, 'fusermount'), path.join(tools, 'fusermount3'));
    const probe = spawnSync('/usr/bin/python3', ['-c', MATH_SEALED_ENVIRONMENT_HELPER, '--check-tools', 'build'], {
      env: { PATH: tools }, encoding: 'utf8', timeout: 5000, maxBuffer: 4096,
    });
    expect(probe.status).toBe(0);
    expect(JSON.parse(probe.stdout)).toEqual({ state: 'ready' });
  });
});

// Opt in on hosts with Codex, FUSE, squashfs tools and the pinned Lean toolchain.
it.skipIf(process.env.DEEPSCIENTIST_TEST_CODEX_SANDBOX !== '1')(
  'compiles saved Lean through a real Codex PID namespace using the same sealed dependencies', async () => {
    const directory = fs.realpathSync(fs.mkdtempSync(path.join('/var/tmp', 'proof-environment-codex-')));
    const project = path.join(directory, 'project'), packages = path.join(directory, 'packages');
    const profile = path.join(directory, 'codex-profile');
    for (const root of [project, packages, profile, path.join(project, '.lake')]) fs.mkdirSync(root, { recursive: true });
    fs.writeFileSync(path.join(project, 'lean-toolchain'), 'leanprover/lean4:v4.31.0\n');
    fs.writeFileSync(path.join(project, 'Probe.lean'), 'example : True := by trivial\n');
    fs.writeFileSync(path.join(packages, 'Dependency.lean'), 'example : True := by trivial\n');
    const environmentFile = path.join(project, '.lake', 'environment.json');
    let proof: Awaited<ReturnType<typeof prepareMathProofEnvironment>> | undefined;
    try {
      const env = { ...process.env, DEEPSCIENTIST_MATH_ENV_FILE: environmentFile };
      proof = await prepareMathProofEnvironment(project, packages, { env, deadlineAt: Date.now() + 15_000 });
      const host = { ...env, [MATH_PROOF_ENVIRONMENT_ENV]: proof.environmentValue };
      fs.writeFileSync(environmentFile, JSON.stringify(projectMathematicsRuntimeEnvironment(host)));
      const worker = mathProofEnvironmentWorkerEnvironment(project, host);
      expect(worker[MATH_PROOF_ENVIRONMENT_ENV]).toBe(host[MATH_PROOF_ENVIRONMENT_ENV]);
      expect(JSON.parse(worker[MATH_PROOF_ENVIRONMENT_SANDBOX_ENV]!).rootPath).not.toMatch(/^\/proc\//u);
      const command = ['sandbox', '--permission-profile', 'math',
        '-c', `permissions.math.filesystem={"/"="read",${JSON.stringify(project)}="write"}`,
        '-c', 'permissions.math.network.enabled=true', '-C', project, '--', process.execPath,
        path.resolve('out/main/check-lean.js'), '--workspace', project, '--file', 'Probe.lean', '--timeout-seconds', '15'];
      const check = (environment: NodeJS.ProcessEnv) => spawnSync('codex', command, {
        env: { ...environment, CODEX_HOME: profile }, encoding: 'utf8', timeout: 20_000, maxBuffer: 8192,
      });
      const before = check(host);
      expect(before.status).toBe(1);
      expect(before.stderr).toMatch(/ENOENT.*\/proc\/\d+\/stat/u);
      const after = check(worker);
      expect(after.error).toBeUndefined();
      expect(after.status, after.stderr).toBe(0);
      expect(JSON.parse(after.stdout)).toMatchObject({ exitCode: 0, timedOut: false,
        phases: [{ file: 'Probe.lean', cached: false, exitCode: 0 }] });
      expect(fs.readFileSync(path.join(packages, 'Dependency.lean'), 'utf8')).toBe('example : True := by trivial\n');
    } finally { await proof?.dispose(); fs.rmSync(directory, { recursive: true, force: true }); }
  }, 45_000,
);
