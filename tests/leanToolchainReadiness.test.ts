import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { checkResolvedLeanToolchainReadiness } from '../src/math/leanToolchainReadiness';

const { probe } = vi.hoisted(() => ({ probe: vi.fn() }));
vi.mock('node:child_process', () => ({ spawnSync: probe }));

describe('pinned Lean toolchain readiness', () => {
  let root: string;
  let env: NodeJS.ProcessEnv;
  beforeEach(() => {
    root = fs.mkdtempSync(path.join(os.tmpdir(), 'lean-toolchain-test-'));
    env = { PATH: root };
    for (const tool of ['lean', 'lake']) fs.writeFileSync(path.join(root, tool), '', { mode: 0o700 });
    fs.writeFileSync(path.join(root, 'lean-toolchain'), 'leanprover/lean4:v4.33.0\n');
    probe.mockReset().mockReturnValue({ status: 0, stdout: 'Lean (version 4.33.0, x86_64-unknown-linux-gnu, Release)\n', stderr: '' });
  });
  afterEach(() => fs.rmSync(root, { recursive: true, force: true }));

  it.each(['leanprover/lean4:v4.33.0', 'v4.33.0', 'leanprover/lean4:v4.33.0-rc1'])('accepts the exact pinned release %s', toolchain => {
    fs.writeFileSync(path.join(root, 'lean-toolchain'), toolchain);
    probe.mockReturnValue({ status: 0, stdout: `Lean (version ${toolchain.split(':').at(-1)!.slice(1)}, Release)`, stderr: '' });
    expect(checkResolvedLeanToolchainReadiness({ projectRoot: root, env }).status).toBe('ready');
    expect(probe).toHaveBeenCalledOnce();
  });

  it.each(['4.32.0', '4.33.0-rc1', 'not Lean'])('rejects a successful executable with the wrong compiler version %s', version => {
    probe.mockReturnValue({ status: 0, stdout: `Lean (version ${version}, Release)`, stderr: '' });
    expect(checkResolvedLeanToolchainReadiness({ projectRoot: root, env })).toMatchObject({
      status: 'invalid', diagnostics: expect.stringContaining('expected 4.33.0'),
    });
  });

  it('does not treat a nightly identifier as a release version', () => {
    fs.writeFileSync(path.join(root, 'lean-toolchain'), 'leanprover/lean4:nightly-2026-10-12');
    expect(checkResolvedLeanToolchainReadiness({ projectRoot: root, env }).status).toBe('ready');
  });

  it('preserves tool execution failures as infrastructure failures', () => {
    probe.mockReturnValue({ status: 1, stdout: '', stderr: 'toolchain is not installed' });
    expect(checkResolvedLeanToolchainReadiness({ projectRoot: root, env })).toMatchObject({
      status: 'unavailable', diagnostics: expect.stringContaining('toolchain is not installed'),
    });
  });
});
