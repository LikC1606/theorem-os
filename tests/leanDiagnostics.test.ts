import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { bindLeanPackages, prepareLeanDiagnosticOverrides, runLeanDiagnostics } from '../src/math/leanDiagnostics';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { parseLeanReferences } from '../src/math/leanReferences';

const { run, lease, readiness, environment } = vi.hoisted(() => ({ run: vi.fn(), lease: vi.fn(), readiness: vi.fn(), environment: vi.fn() }));
vi.mock('../src/math/verifier', () => ({ runMathematicsSandboxedCommand: run,
  formalVerificationToolIdentity: () => 'a'.repeat(64) }));
vi.mock('../src/math/mathProofEnvironment', () => ({
  MATH_PROOF_ENVIRONMENT_SANDBOX_ENV: 'DEEPSCIENTIST_MATH_PROOF_ENVIRONMENT_SANDBOX',
  acquireMathProofEnvironmentLease: lease,
  resolveMathProofEnvironment: environment,
}));
vi.mock('../src/math/leanToolchainReadiness', () => ({ checkResolvedLeanToolchainReadiness: readiness }));

describe('bounded local Lean diagnostics', () => {
  let root: string;
  beforeEach(() => {
    root = fs.mkdtempSync(path.join(os.tmpdir(), 'lean-diagnostics-'));
    fs.writeFileSync(path.join(root, 'Submission.lean'), 'import ChallengeDeps\ntheorem result : True := by trivial\n');
    fs.writeFileSync(path.join(root, 'ChallengeDeps.lean'), 'def fixed : Nat := 2\n');
    run.mockReset().mockImplementation(async input => {
      const output = input.args.at(-1).match(/-o '([^']+)'/)[1];
      fs.mkdirSync(path.dirname(path.join(root, output)), { recursive: true });
      fs.writeFileSync(path.join(root, output), 'compiled');
      return { started: true, exitCode: 0, timedOut: false, aborted: false, durationMs: 1, stdout: '#check output', stderr: '' };
    });
    lease.mockReset(); readiness.mockReset(); environment.mockReset();
  });
  afterEach(() => fs.rmSync(root, { recursive: true, force: true }));

  it('prepares imports, reuses unchanged artifacts, and rebuilds changed dependencies', async () => {
    const input = { projectRoot: root, files: ['Submission.lean'], timeoutMs: 1000 };
    const prepared = await runLeanDiagnostics({ ...input, dependenciesOnly: true });
    expect(prepared.phases.map(phase => phase.file)).toEqual(['ChallengeDeps.lean']);
    expect(run).toHaveBeenCalledTimes(1);
    const checked = await runLeanDiagnostics(input);
    expect(checked.phases[0].cached).toBe(true);
    expect(checked.stdout).toContain('#check output');
    expect(run).toHaveBeenCalledTimes(2);
    fs.writeFileSync(path.join(root, 'ChallengeDeps.lean'), 'def fixed : Nat := 3\n');
    await runLeanDiagnostics(input);
    expect(run).toHaveBeenCalledTimes(4);
    fs.writeFileSync(path.join(root, '.lake/build/lib/lean/ChallengeDeps.olean'), 'tampered');
    const repaired = await runLeanDiagnostics(input);
    expect(repaired.phases.map(phase => phase.cached)).toEqual([false, true]);
    expect(fs.readFileSync(path.join(root, '.lake/build/lib/lean/ChallengeDeps.olean'), 'utf8')).toBe('compiled');
    expect(run).toHaveBeenCalledTimes(5);
  });

  it('reuses an unchanged requested proof, but checks changes to source, environment and artifacts', async () => {
    environment.mockReturnValue({ identity: 'fixed-frozen-packages' });
    const input = { projectRoot: root, files: ['Submission.lean'], timeoutMs: 1000 };
    const first = await runLeanDiagnostics(input);
    const repeat = await runLeanDiagnostics(input);
    expect(run).toHaveBeenCalledTimes(2);
    expect(repeat.phases.every(phase => phase.cached)).toBe(true);
    expect(repeat.stdout).toBe(first.stdout);
    fs.appendFileSync(path.join(root, 'Submission.lean'), '\n-- relevant source change\n');
    await runLeanDiagnostics(input);
    expect(run).toHaveBeenCalledTimes(3);
    fs.writeFileSync(path.join(root, '.lake/build/lib/lean/Submission.olean'), 'tampered');
    await runLeanDiagnostics(input);
    expect(run).toHaveBeenCalledTimes(4);
    await runLeanDiagnostics({ ...input, env: { ELAN_HOME: '/different/toolchain' } });
    expect(run).toHaveBeenCalledTimes(6);
  });

  it.each([
    { cached: [false, false], prepare: 'none' },
    { cached: [true, false], prepare: 'dependency' },
    { cached: [true, true], prepare: 'all' },
    { cached: [false, true], prepare: 'rebuild-dependency' },
  ])('separates phase messages for $prepare cache reuse', async ({ cached, prepare }) => {
    const warning = 'Note: This linter can be disabled with `set_option linter.unusedVariables false`';
    const message = { caption: '', data: 'KNOWLEDGE_REFERENCES_0:[[],[]]', severity: 'information' };
    const json = JSON.stringify(message), compile = run.getMockImplementation()!;
    run.mockImplementation(async input => {
      const result = await compile(input);
      const dependency = input.args.at(-1).includes("-o '.lake/build/lib/lean/ChallengeDeps.olean'");
      const output = dependency ? warning : json;
      return { ...result, stdout: output, stderr: output };
    });
    const input = { projectRoot: root, files: ['Submission.lean'], timeoutMs: Infinity };
    if (prepare !== 'none') await runLeanDiagnostics({ ...input, dependenciesOnly: prepare === 'dependency' });
    if (prepare === 'rebuild-dependency') fs.writeFileSync(path.join(root, '.lake/build/lib/lean/ChallengeDeps.olean'), 'tampered');
    run.mockClear();
    const result = await runLeanDiagnostics(input);
    expect(result.phases.map(phase => phase.cached)).toEqual(cached);
    expect(run).toHaveBeenCalledTimes(cached.filter(value => !value).length);
    for (const output of [result.stdout, result.stderr]) {
      expect(output).toBe(warning + '\n' + json);
      expect(JSON.parse(output.split('\n').at(-1)!)).toEqual(message);
      expect(parseLeanReferences(output, 'KNOWLEDGE_REFERENCES_0:', ['ChallengeDeps.lean', 'Submission.lean']))
        .toEqual({ statement: [], proof: [] });
    }
    expect(JSON.parse(fs.readFileSync(path.join(root, result.diagnosticArtifacts[0].path), 'utf8')).stdout).toBe(warning);
    expect(JSON.parse(fs.readFileSync(path.join(root, result.diagnosticArtifacts[1].path), 'utf8')).stdout).toBe(json);
  });

  it.each([
    { first: '', next: 'second', expected: 'second' },
    { first: 'first\n', next: 'second', expected: 'first\nsecond' },
    { first: 'first', next: '', expected: 'first' },
    { first: '', next: '', expected: '' },
  ])('preserves existing line and empty boundaries ($first, $next)', async ({ first, next, expected }) => {
    const compile = run.getMockImplementation()!;
    run.mockImplementation(async input => {
      const result = await compile(input);
      const dependency = input.args.at(-1).includes("-o '.lake/build/lib/lean/ChallengeDeps.olean'");
      return { ...result, stdout: dependency ? first : next, stderr: dependency ? first : next };
    });
    const input = { projectRoot: root, files: ['Submission.lean'], timeoutMs: Infinity };
    const fresh = await runLeanDiagnostics(input), cached = await runLeanDiagnostics(input);
    expect(cached.phases.every(phase => phase.cached)).toBe(true);
    for (const result of [fresh, cached]) {
      expect(result.stdout).toBe(expected);
      expect(result.stderr).toBe(expected);
    }
  });

  it('publishes the complete latest input manifest on successful and fully cached checks', async () => {
    const input = { projectRoot: root, files: ['Submission.lean'], timeoutMs: Infinity };
    const first = await runLeanDiagnostics(input);
    const latest = () => JSON.parse(fs.readFileSync(path.join(root, '.lake/lean-diagnostics-latest.json'), 'utf8'));
    expect(latest()).toMatchObject({ schema: 'theoremos.lean-diagnostics-latest.v1', authority: 'advisory-lean-process',
      requestedFiles: ['Submission.lean'], sourceDigest: first.sourceDigest, environmentDigest: first.environmentDigest,
      toolIdentity: 'a'.repeat(64), exitCode: 0, timedOut: false, aborted: false,
      sourceFiles: ['ChallengeDeps.lean', 'Submission.lean'].map(file => ({ file, digest: mathDigest(fs.readFileSync(path.join(root, file))) })),
      diagnosticArtifacts: first.diagnosticArtifacts });
    expect(latest().configuration).toHaveLength(5);
    const repeat = await runLeanDiagnostics(input);
    expect(repeat.phases.every(phase => phase.cached)).toBe(true);
    expect(latest().diagnosticArtifacts).toEqual(first.diagnosticArtifacts);
    expect(run).toHaveBeenCalledTimes(2);
  });

  it('replaces a prior successful manifest when an aborted check never starts the compiler', async () => {
    const input = { projectRoot: root, files: ['Submission.lean'], timeoutMs: Infinity };
    await runLeanDiagnostics(input);
    const controller = new AbortController(); controller.abort();
    await expect(runLeanDiagnostics({ ...input, signal: controller.signal })).rejects.toThrow();
    expect(JSON.parse(fs.readFileSync(path.join(root, '.lake/lean-diagnostics-latest.json'), 'utf8')))
      .toMatchObject({ exitCode: null, timedOut: false, aborted: true, diagnosticArtifacts: [] });
    expect(run).toHaveBeenCalledTimes(2);
  });

  it('preserves the original compiler exception if latest metadata cannot be written', async () => {
    run.mockRejectedValueOnce(new Error('original compiler exception'));
    const mkdir = vi.spyOn(fs, 'mkdirSync').mockImplementation(() => { throw new Error('metadata write failed'); });
    try {
      await expect(runLeanDiagnostics({ projectRoot: root, files: ['Submission.lean'], timeoutMs: Infinity }))
        .rejects.toThrow('original compiler exception');
    } finally { mkdir.mockRestore(); }
  });

  it('rechecks dependants when rebuilding an imported artifact produces different bytes', async () => {
    const input = { projectRoot: root, files: ['Submission.lean'], timeoutMs: 1000 };
    await runLeanDiagnostics(input);
    fs.writeFileSync(path.join(root, '.lake/build/lib/lean/ChallengeDeps.olean'), 'tampered');
    run.mockImplementationOnce(async () => {
      fs.writeFileSync(path.join(root, '.lake/build/lib/lean/ChallengeDeps.olean'), 'different rebuilt artifact');
      return { started: true, exitCode: 0, timedOut: false, aborted: false, durationMs: 1, stdout: '', stderr: '' };
    });
    const rebuilt = await runLeanDiagnostics(input);
    expect(rebuilt.phases.map(phase => phase.cached)).toEqual([false, false]);
    expect(run).toHaveBeenCalledTimes(4);
  });

  it.each(['.private', '.server', '.ir', '.ir.sig'])('rebuilds missing Lean companion artifacts (%s)', async suffix => {
    const companionPath = (output: string) => suffix.startsWith('.ir') ? output.replace(/\.olean$/u, suffix) : output + suffix;
    const compile = run.getMockImplementation()!;
    run.mockImplementation(async input => {
      const result = await compile(input);
      const output = input.args.at(-1).match(/-o '([^']+)'/)[1];
      fs.writeFileSync(path.join(root, companionPath(output)), 'companion');
      return result;
    });
    const input = { projectRoot: root, files: ['Submission.lean'], timeoutMs: 1000 };
    await runLeanDiagnostics(input);
    const companion = path.join(root, companionPath('.lake/build/lib/lean/ChallengeDeps.olean'));
    fs.unlinkSync(companion);
    const repaired = await runLeanDiagnostics(input);
    expect(repaired.phases.map(phase => phase.cached)).toEqual([false, true]);
    expect(fs.readFileSync(companion, 'utf8')).toBe('companion');
    expect(run).toHaveBeenCalledTimes(3);
  });

  it('includes worker lease and toolchain readiness in the diagnostic deadline', async () => {
    fs.writeFileSync(path.join(root, 'Submission.lean'), 'theorem result : True := by trivial\n');
    const compiler = path.join(root, 'lean'), marker = path.join(root, 'compiler-started');
    fs.writeFileSync(compiler, `#!${process.execPath}\nrequire('node:fs').writeFileSync(${JSON.stringify(marker)}, 'started');\n`);
    fs.chmodSync(compiler, 0o700);
    const packages = path.join(root, 'packages'); fs.mkdirSync(packages);
    const release = vi.fn();
    lease.mockImplementation(async () => {
      await new Promise(resolve => setTimeout(resolve, 60));
      return { packagesRoot: packages, release };
    });
    readiness.mockImplementation(() => {
      Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 60);
      return { status: 'ready', leanPath: compiler };
    });
    const result = await runLeanDiagnostics({ projectRoot: root, files: ['Submission.lean'], timeoutMs: 100,
      env: { DEEPSCIENTIST_MATH_PROOF_ENVIRONMENT_SANDBOX: 'host-bound-mapping' } });
    expect(result.timedOut).toBe(true);
    expect(fs.existsSync(marker)).toBe(false);
    expect(release).toHaveBeenCalledOnce();
  });

  it.each(['timeout', 'abort'])('stops the worker compiler and its children on %s', async reason => {
    fs.writeFileSync(path.join(root, 'Submission.lean'), 'theorem result : True := by trivial\n');
    const compiler = path.join(root, 'lean'), marker = path.join(root, 'compiler-pids.json');
    fs.writeFileSync(compiler, `#!${process.execPath}\nconst child = require('node:child_process').spawn(process.execPath,
['-e', 'setInterval(() => {}, 1000)'], { stdio: 'ignore' });
require('node:fs').writeFileSync(${JSON.stringify(marker)}, JSON.stringify([process.pid, child.pid]));
setInterval(() => {}, 1000);\n`);
    fs.chmodSync(compiler, 0o700);
    const packages = path.join(root, 'packages'); fs.mkdirSync(packages);
    const release = vi.fn(); lease.mockResolvedValue({ packagesRoot: packages, release });
    readiness.mockReturnValue({ status: 'ready', leanPath: compiler });
    const controller = new AbortController();
    const pending = runLeanDiagnostics({ projectRoot: root, files: ['Submission.lean'],
      timeoutMs: reason === 'timeout' ? 1000 : Infinity, signal: controller.signal,
      env: { DEEPSCIENTIST_MATH_PROOF_ENVIRONMENT_SANDBOX: 'host-bound-mapping' } });
    await vi.waitFor(() => expect(fs.existsSync(marker)).toBe(true));
    if (reason === 'abort') controller.abort();
    const result = await pending;
    expect(result).toMatchObject({ timedOut: reason === 'timeout', aborted: reason === 'abort' });
    expect(JSON.parse(fs.readFileSync(path.join(root, '.lake/lean-diagnostics-latest.json'), 'utf8')))
      .toMatchObject({ exitCode: result.exitCode, timedOut: reason === 'timeout', aborted: reason === 'abort' });
    expect(release).toHaveBeenCalledOnce();
    for (const pid of JSON.parse(fs.readFileSync(marker, 'utf8'))) {
      await vi.waitFor(() => {
        try { expect(fs.readFileSync(`/proc/${pid}/stat`, 'utf8')).toMatch(/\) Z /u); }
        catch (error) { if ((error as NodeJS.ErrnoException).code !== 'ENOENT') throw error; }
      });
    }
    expect(fs.existsSync(path.join(root, '.lake/lean-diagnostics.json'))).toBe(false);
  });

  it.each([{ exitCode: 1, timedOut: false }, { exitCode: null, timedOut: true }])
    ('preserves errors/timeouts and stops before checking dependants (%j)', async failure => {
      run.mockResolvedValueOnce({ started: true, aborted: false, durationMs: 50,
        stdout: 'error: unsolved goals\n' + 'x'.repeat(20000), stderr: '', ...failure });
      const result = await runLeanDiagnostics({ projectRoot: root, files: ['Submission.lean'], timeoutMs: 1000 });
      expect(result).toMatchObject(failure);
      expect(result.stdout).toContain('error: unsolved goals');
      expect(JSON.parse(fs.readFileSync(path.join(root, '.lake/lean-diagnostics-latest.json'), 'utf8')))
        .toMatchObject({ ...failure, diagnosticArtifacts: result.diagnosticArtifacts });
      expect(Buffer.byteLength(result.stdout)).toBeLessThanOrEqual(8000);
      expect(run).toHaveBeenCalledTimes(1);
    });

  it('retains late projection errors with an explicit larger window without changing ordinary prompt bounds', async () => {
    const diagnostics = 'warning: declaration uses sorry\n'.repeat(400) + 'Submission.lean:500:1: error: unexpected theorem';
    run.mockResolvedValue({ started: true, exitCode: 1, aborted: false, timedOut: false,
      durationMs: 1, stdout: diagnostics, stderr: '' });
    const input = { projectRoot: root, files: ['Submission.lean'], timeoutMs: 1000 };
    const ordinary = await runLeanDiagnostics(input);
    expect(Buffer.byteLength(ordinary.stdout)).toBeLessThanOrEqual(8000);
    const projection = await runLeanDiagnostics({ ...input, outputLimit: 1_000_000 });
    expect(projection.stdout).toBe(diagnostics);
    expect(run.mock.calls[1][0].outputLimit).toBe(4_000_000);
    expect(projection.phases).toHaveLength(1);
  });

  it('retains structured Lean messages and complete source-bound diagnostics beyond the prompt preview', async () => {
    const warning = JSON.stringify({ severity: 'warning', data: 'long warning '.repeat(1000), fileName: 'ChallengeDeps.lean', pos: { line: 2, column: 0 } });
    const error = JSON.stringify({ severity: 'error', data: 'unsolved goals\nn : Nat\nh : n > 0\n\u22a2 n > 1',
      fileName: 'ChallengeDeps.lean', pos: { line: 40, column: 3 }, endPos: { line: 41, column: 4 }, kind: 'Tactic.unsolvedGoals' });
    const stdout = `${warning}\n${error}\n`;
    run.mockResolvedValueOnce({ started: true, exitCode: 1, aborted: false, timedOut: false, durationMs: 1,
      stdout, stderr: '', stdoutSha256: mathDigest(stdout), stderrSha256: mathDigest('') });
    const result = await runLeanDiagnostics({ projectRoot: root, files: ['Submission.lean'], timeoutMs: 1000 });
    expect(result.firstBlocking).toMatchObject({ format: 'lean-json', file: 'ChallengeDeps.lean', line: 40, column: 3,
      code: 'Tactic.unsolvedGoals', goalText: 'n : Nat\nh : n > 0\n\u22a2 n > 1' });
    expect(result.previewTruncated).toBe(true);
    expect(result.stdout).toContain('[truncated;');
    const reference = result.diagnosticArtifacts[0], artifact = fs.readFileSync(path.join(root, reference.path), 'utf8');
    expect(reference).toMatchObject({ sourceDigest: result.sourceDigest, environmentDigest: result.environmentDigest, captureComplete: true });
    expect(mathDigest(artifact)).toBe(reference.digest);
    expect(JSON.parse(artifact)).toMatchObject({ stdout, captureComplete: true, sourceCurrent: true,
      messages: [{ severity: 'warning' }, { severity: 'error', line: 40 }] });
    expect(run.mock.calls[0][0].args.at(-1)).toContain('lean --json');
  });

  it('marks incomplete captured JSON explicitly and preserves malformed output as raw fallback', async () => {
    const stdout = '{"severity":"error","data":"incomplete';
    run.mockResolvedValueOnce({ started: true, exitCode: 1, aborted: false, timedOut: false, durationMs: 1,
      stdout, stderr: '', stdoutSha256: mathDigest(stdout + ' missing"}'), stderrSha256: mathDigest('') });
    const result = await runLeanDiagnostics({ projectRoot: root, files: ['Submission.lean'], timeoutMs: 1000 });
    expect(result.diagnosticArtifacts[0].captureComplete).toBe(false);
    expect(result.stdout).toBe(stdout);
    expect(result.firstBlocking).toBeUndefined();
  });

  it('rebuilds cached diagnostics when their bound artifact changes or disappears', async () => {
    const input = { projectRoot: root, files: ['Submission.lean'], timeoutMs: 1000 };
    const result = await runLeanDiagnostics(input);
    expect(run).toHaveBeenCalledTimes(2);
    fs.writeFileSync(path.join(root, result.diagnosticArtifacts[0].path), '{}');
    const repaired = await runLeanDiagnostics(input);
    expect(repaired.phases.map(phase => phase.cached)).toEqual([false, true]);
    expect(run).toHaveBeenCalledTimes(3);
  });

  it('reuses full cached output when the requested preview bound increases', async () => {
    const original = run.getMockImplementation()!;
    run.mockImplementation(async input => ({ ...await original(input), stdout: 'warning text\n'.repeat(1000) }));
    const input = { projectRoot: root, files: ['Submission.lean'], timeoutMs: 1000 };
    const ordinary = await runLeanDiagnostics(input);
    expect(ordinary.stdout).toContain('[truncated;');
    const larger = await runLeanDiagnostics({ ...input, outputLimit: 100_000 });
    expect(larger.phases.every(phase => phase.cached)).toBe(true);
    expect(larger.stdout).not.toContain('[truncated;');
    expect(run).toHaveBeenCalledTimes(2);
  });

  it('rejects protected imports before invoking Lean', async () => {
    fs.writeFileSync(path.join(root, 'Submission.lean'), 'import Solution\n');
    await expect(runLeanDiagnostics({ projectRoot: root, files: ['Submission.lean'], timeoutMs: 1000 }))
      .rejects.toThrow('math_construction_import_excluded');
    expect(run).not.toHaveBeenCalled();
  });

  it('rejects a diagnostic result if the saved sources changed during compilation', async () => {
    run.mockImplementationOnce(async () => {
      fs.appendFileSync(path.join(root, 'Submission.lean'), '\nnoncomputable section\n');
      return { started: true, exitCode: 0, timedOut: false, aborted: false, durationMs: 1, stdout: '', stderr: '' };
    });
    const result = await runLeanDiagnostics({ projectRoot: root, files: ['Submission.lean'], timeoutMs: 1000 });
    expect(result.exitCode).toBe(1);
    expect(result.stderr).toContain('math_diagnostics_source_changed');
    expect(run).toHaveBeenCalledTimes(1);
    expect(fs.existsSync(path.join(root, '.lake/lean-diagnostics.json'))).toBe(false);
  });

  it('checks the saved file inside an authenticated worker without creating a nested sandbox', async () => {
    const compiler = path.join(root, 'lean');
    fs.writeFileSync(compiler, `#!${process.execPath}\nconst fs = require('node:fs');
const args = process.argv.slice(2), file = args.at(-1), source = fs.readFileSync(file, 'utf8');
if (file === 'Submission.lean' && source !== ${JSON.stringify(fs.readFileSync(path.join(root, 'Submission.lean'), 'utf8'))}) process.exit(9);
fs.writeFileSync(args[args.indexOf('-o') + 1], source); console.log(file);
`);
    fs.chmodSync(compiler, 0o700);
    const packages = path.join(root, 'packages'); fs.mkdirSync(packages);
    const release = vi.fn(); lease.mockResolvedValue({ packagesRoot: packages, release });
    readiness.mockReturnValue({ status: 'ready', leanPath: compiler });
    const result = await runLeanDiagnostics({ projectRoot: root, files: ['Submission.lean'], timeoutMs: Infinity,
      env: { DEEPSCIENTIST_MATH_PROOF_ENVIRONMENT_SANDBOX: 'host-bound-mapping' } });
    expect(result.exitCode).toBe(0);
    expect(result.stdout).toContain('Submission.lean');
    expect(run).not.toHaveBeenCalled();
    expect(release).toHaveBeenCalledTimes(2);
    expect(fs.readFileSync(path.join(root, '.lake/build/lib/lean/Submission.olean'), 'utf8'))
      .toBe(fs.readFileSync(path.join(root, 'Submission.lean'), 'utf8'));
  });

  it('refuses worker diagnostics when the frozen environment lease cannot be verified', async () => {
    lease.mockRejectedValue(new Error('Sealed proof environment binding changed.'));
    await expect(runLeanDiagnostics({ projectRoot: root, files: ['Submission.lean'], timeoutMs: 1000,
      env: { DEEPSCIENTIST_MATH_PROOF_ENVIRONMENT_SANDBOX: 'invalid-mapping' } }))
      .rejects.toThrow('binding changed');
    expect(run).not.toHaveBeenCalled();
    expect(readiness).not.toHaveBeenCalled();
    expect(JSON.parse(fs.readFileSync(path.join(root, '.lake/lean-diagnostics-latest.json'), 'utf8')))
      .toMatchObject({ exitCode: null, timedOut: false, aborted: false, diagnosticArtifacts: [] });
  });

  it.each(['missing', 'dangling', 'obsolete', 'correct'])('binds the pinned package cache when the link is %s', state => {
    const pinned = path.join(root, 'pinned');
    const packages = path.join(root, '.lake', 'packages');
    fs.mkdirSync(pinned); fs.mkdirSync(path.dirname(packages));
    if (state === 'obsolete') fs.mkdirSync(path.join(root, 'obsolete'));
    if (state !== 'missing') fs.symlinkSync(state === 'correct' ? pinned : path.join(root, state), packages, 'dir');
    bindLeanPackages(root, pinned);
    expect(fs.realpathSync(packages)).toBe(pinned);
    bindLeanPackages(root, pinned);
    expect(fs.realpathSync(packages)).toBe(pinned);
  });

  it('preserves real package directories and rejects unavailable caches before changing links', () => {
    const pinned = path.join(root, 'pinned');
    const packages = path.join(root, '.lake', 'packages');
    fs.mkdirSync(pinned); fs.mkdirSync(packages, { recursive: true });
    fs.writeFileSync(path.join(packages, 'owned'), 'keep');
    bindLeanPackages(root, pinned);
    expect(fs.readFileSync(path.join(packages, 'owned'), 'utf8')).toBe('keep');
    fs.rmSync(packages, { recursive: true });
    fs.symlinkSync(pinned, packages, 'dir');
    expect(() => bindLeanPackages(root, path.join(root, 'missing-cache'))).toThrow();
    expect(fs.readlinkSync(packages)).toBe(pinned);
  });

  it('writes valid path overrides without changing the frozen manifest', () => {
    const manifest = JSON.stringify({ packages: [{ name: 'mathlib', type: 'git', rev: 'pinned' }] });
    fs.writeFileSync(path.join(root, 'lake-manifest.json'), manifest);
    prepareLeanDiagnosticOverrides(root);
    const override = JSON.parse(fs.readFileSync(path.join(root, '.lake/package-overrides.json'), 'utf8'));
    expect(override).toMatchObject({ schemaVersion: '1.2.0', packages: [{ type: 'path', rev: 'pinned',
      dir: path.join(root, '.lake/packages/mathlib') }] });
    expect(fs.readFileSync(path.join(root, 'lake-manifest.json'), 'utf8')).toBe(manifest);
  });
});
