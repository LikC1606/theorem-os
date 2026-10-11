import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { mathLocalModuleBuildOrder } from '../src/math/mathConstructionSources';
import { runMathematicsSandboxedCommand } from '../src/math/verifier';

describe('isolated local Lean dependencies', () => {
  let root: string;
  beforeEach(() => { root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'lean-local-deps-'))); });
  afterEach(() => { vi.restoreAllMocks(); fs.rmSync(root, { recursive: true, force: true }); });
  const write = (root: string, file: string, source: string) => {
    fs.mkdirSync(path.dirname(path.join(root, file)), { recursive: true });
    fs.writeFileSync(path.join(root, file), source, { mode: 0o700 });
  };

  it('orders transitive local imports once, leaving packages and unrelated drafts alone', () => {
    write(root, 'Submission.lean', 'import Mathlib\nimport Submission.A Submission.B\ntheorem result : True := by trivial');
    write(root, 'Submission/A.lean', 'import Submission.B\n');
    write(root, 'Submission/B.lean', '/- import Submission.Bad -/\nnamespace Submission.B\n');
    write(root, 'Submission/Bad.lean', 'sorry');
    write(root, '.lake/packages/mathlib/Mathlib.lean', 'sorry');
    expect(mathLocalModuleBuildOrder(root, 'Submission.lean').map(item => item.file)).toEqual([
      'Submission/B.lean', 'Submission/A.lean', 'Submission.lean',
    ]);
  });

  it('resolves configured source directories and quoted dependency names', () => {
    write(root, 'lakefile.toml', 'name = "proof"\n[[lean_lib]]\nname = "Submission"\nsrcDir = "Proof"\n');
    write(root, 'Proof/Submission.lean', 'module\npublic import Submission.«With.dot»\n');
    write(root, 'Proof/Submission/With.dot.lean', 'namespace Submission\n');
    expect(mathLocalModuleBuildOrder(root, 'Proof/Submission.lean')).toEqual([
      { file: 'Proof/Submission/With.dot.lean', sourceRoot: 'Proof', module: 'Submission.With.dot' },
      { file: 'Proof/Submission.lean', sourceRoot: 'Proof', module: 'Submission' },
    ]);
  });

  it('rejects local cycles and links instead of accepting stale outputs', () => {
    write(root, 'Submission.lean', 'import Submission.Helpers\n');
    write(root, 'Submission/Helpers.lean', 'import Submission\n');
    expect(() => mathLocalModuleBuildOrder(root, 'Submission.lean')).toThrow('math_local_module_import_cycle');
    fs.unlinkSync(path.join(root, 'Submission/Helpers.lean'));
    fs.symlinkSync('../Submission.lean', path.join(root, 'Submission/Helpers.lean'));
    expect(() => mathLocalModuleBuildOrder(root, 'Submission.lean')).toThrow('math_local_module_source_invalid');
  });

  it.runIf(process.platform === 'linux').each([10_000, Infinity])('mounts the pinned toolchain with timeout %s when Elan links outside its home', async timeoutMs => {
    const project = path.join(root, 'project');
    const elan = path.join(root, 'elan');
    const toolchain = path.join(root, 'external-lean');
    const tools = path.join(root, 'tools');
    const evalTools = path.join(root, 'eval-tools');
    write(evalTools, 'bin/comparator', '#!/bin/sh\nexit 0\n');
    fs.mkdirSync(project);
    write(elan, 'bin/elan', `#!/bin/sh\nprintf '%s\\n' '${toolchain}/bin/lean'\n`);
    write(elan, 'bin/lean', '#!/bin/sh\nexit 0\n');
    for (const name of ['lean', 'lake']) write(toolchain, `bin/${name}`, '#!/bin/sh\nexit 0\n');
    fs.mkdirSync(path.join(toolchain, 'lib/lean'), { recursive: true });
    fs.mkdirSync(path.join(elan, 'toolchains'));
    fs.symlinkSync(toolchain, path.join(elan, 'toolchains/pinned'));
    // A capturing backend tests the mount arguments without invoking a compiler.
    write(tools, 'bwrap', '#!/bin/sh\nsleep 0.05\nprintf "%s\\n" "$@"\n');
    const timers = vi.spyOn(globalThis, 'setTimeout');
    const result = await runMathematicsSandboxedCommand({ checkoutRoot: project, command: 'lean', args: ['--version'],
      timeoutMs, env: { PATH: `${tools}:${elan}/bin:/usr/bin:/bin`, ELAN_HOME: elan,
        DEEPSCIENTIST_MATH_ENV_FILE: path.join(root, 'absent.env'), DEEPSCIENTIST_MATH_SANDBOX_BACKEND: 'bwrap',
        DEEPSCIENTIST_LEAN_EVAL_TOOLS_ROOT: evalTools } });
    expect(result.exitCode).toBe(0);
    expect(result.timedOut).toBe(false);
    expect(timers.mock.calls.some(([, ms]) => ms === Infinity)).toBe(false);
    expect(result.stdout).toContain(`--ro-bind\n${toolchain}\n/toolchains/elan\n`);
    expect(result.stdout).toContain('/toolchains/elan/bin');
    expect(result.stdout).not.toContain('/toolchains/elan/../');
    expect(result.stdout).toContain(`--ro-bind\n${evalTools}\n/runtime/node\n`);
    expect(result.stdout).toContain('/runtime/node/bin:');
  });
});
