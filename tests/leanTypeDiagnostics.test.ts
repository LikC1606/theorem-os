import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { checkLeanType, leanTypeDiagnosticCommands } from '../src/math/leanTypeDiagnostics';
import { runLeanProcess } from '../src/math/mathProcess';
import { mathDigest } from '../src/math/mathRuntimeIo';

const { run } = vi.hoisted(() => ({ run: vi.fn() }));
vi.mock('../src/math/verifier', () => ({ runMathematicsSandboxedCommand: run }));
const toolchains = path.join(os.homedir(), '.elan', 'toolchains');
const lean = fs.existsSync(toolchains) ? fs.readdirSync(toolchains).toSorted().reverse()
  .map(name => path.join(toolchains, name, 'bin', 'lean')).find(file => fs.existsSync(file)) : undefined;

describe('type query payloads', () => {
  it('passes the requested type only as a string to Lean term parsing', () => {
    const payload = 'Nat\nrun_cmd IO.FS.writeFile "marker" "bad"';
    const commands = leanTypeDiagnosticCommands(payload, '.lake/result.json');
    expect(commands).toContain(`(Lean.Name.mkSimple "term") ${JSON.stringify(payload)}`);
    expect(commands.split('\n').some(line => line.startsWith('run_cmd IO.FS'))).toBe(false);
  });
});

describe.skipIf(!lean)('local Lean closed-type preflight', () => {
  let root: string;
  beforeEach(() => {
    root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'lean-type-preflight-')));
    fs.writeFileSync(path.join(root, 'Dependency.lean'), 'namespace Terms\nstructure Box where\n  value : Nat\nend Terms\n');
    fs.writeFileSync(path.join(root, 'Submission.lean'), 'import Dependency\nnamespace Geometry\nopen Terms\n' +
      'theorem original : True := by\n  exact nonexistent_proof\nend Geometry\n');
    run.mockReset().mockImplementation(input => {
      const code = input.args.at(-1);
      return runLeanProcess('/bin/sh', ['-ceu', code], { cwd: input.checkoutRoot, timeoutMs: input.timeoutMs,
        signal: input.signal, outputLimit: input.outputLimit, outputCapture: input.outputCapture,
        env: { ...process.env, PATH: `${path.dirname(lean!)}:${process.env.PATH}`,
          LEAN_PATH: path.join(input.checkoutRoot, '.lake', 'build', 'lib', 'lean') } });
    });
  });
  afterEach(() => fs.rmSync(root, { recursive: true, force: true }));
  const check = (type: string) => checkLeanType({ projectRoot: root, file: 'Submission.lean', context: 'Geometry.original', type, timeoutMs: 30_000 });

  it('prepares missing local dependencies, restores open scopes, and preserves active source and proof artifacts', async () => {
    const before = fs.readFileSync(path.join(root, 'Submission.lean'));
    const result = await check('Box \u2192 Nat');
    expect(result.status, result.stdout + result.stderr).toBe('elaborated');
    expect(result).toMatchObject({ status: 'elaborated', exitCode: 0, type: 'Terms.Box \u2192 Nat', proofAcceptance: 'not-assessed' });
    expect(fs.readFileSync(path.join(root, 'Submission.lean'))).toEqual(before);
    expect(fs.existsSync(path.join(root, '.lake', 'build', 'lib', 'lean', 'Submission.olean'))).toBe(false);
    const text = fs.readFileSync(path.join(root, result.artifact.path), 'utf8');
    expect(mathDigest(text)).toBe(result.artifact.digest);
    const artifact = JSON.parse(text);
    expect(artifact).toMatchObject({ authority: 'advisory-type-elaboration', proofAcceptance: 'not-assessed',
      sourceDigest: result.sourceSnapshotDigest });
    expect(artifact.files.find(file => file.file === 'Submission.lean').digest).toBe(mathDigest(before));
    expect(result.diagnosticArtifacts.length).toBeGreaterThan(0);
    expect(result.diagnosticArtifacts.every(reference => fs.existsSync(path.join(root, reference.path)))).toBe(true);
  });

  it('accepts explicit Nat binders and reports ambiguous or incorrect types before proof work', async () => {
    const explicit = await check('\u2200 (a : Nat \u2192 Nat) (n : Nat), a (n + 1) = a (n + 1)');
    expect(explicit.status, explicit.stdout + explicit.stderr).toBe('elaborated');
    const mismatch = await check('\u2200 (a : Nat \u2192 Nat) (n : Int), a (n + 1) = a n');
    expect(mismatch).toMatchObject({ status: 'failed', exitCode: 1, proofAcceptance: 'not-assessed',
      firstBlocking: { severity: 'error', format: 'lean-json' } });
    expect(mismatch.stdout).toContain('Type mismatch');
    expect((await check('\u2200 n, n = n')).status).toBe('failed');
    expect((await check('undeclaredType')).status).toBe('failed');
  });

  it('rejects command injection as a term and leaves the original file untouched', async () => {
    const result = await check('Nat\nrun_cmd IO.FS.writeFile "marker" "bad"');
    expect(result.status).toBe('failed');
    expect(fs.existsSync(path.join(root, 'marker'))).toBe(false);
    const clone = path.join(root, path.dirname(result.artifact.path), 'project');
    expect(fs.existsSync(path.join(clone, 'marker'))).toBe(false);
  });

  it('reports an unavailable or invalid dependency instead of treating the type as elaborated', async () => {
    fs.writeFileSync(path.join(root, 'Dependency.lean'), 'def invalidDependency : Nat := "wrong type"\n');
    const result = await check('Nat');
    expect(result).toMatchObject({ status: 'failed', proofAcceptance: 'not-assessed', firstBlocking: { file: 'Dependency.lean' } });
    expect(result.phases).toHaveLength(1);
    expect(fs.existsSync(path.join(root, '.lake', 'build'))).toBe(false);
  });
});
