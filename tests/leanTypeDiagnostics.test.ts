import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { checkLeanType, leanTypeDiagnosticCommands, leanTypeDiagnosticProjection } from '../src/math/leanTypeDiagnostics';
import { mathLocalModuleBuildOrder } from '../src/math/mathConstructionSources';
import { runLeanProcess } from '../src/math/mathProcess';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { TaskTypePreflightCache } from '../src/solver/taskTypePreflight';
import type { SolverProblem } from '../src/solver/problem';
import type { CooperativeTask } from '../src/solver/tasks';

const { run } = vi.hoisted(() => ({ run: vi.fn() }));
vi.mock('../src/math/verifier', () => ({ runMathematicsSandboxedCommand: run,
  formalVerificationToolIdentity: () => 'a'.repeat(64) }));
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

describe('type query projection identity', () => {
  const source = 'namespace Geometry\nopen Nat\ndef value : Nat := 0\ntheorem original : True := by sorry\nend Geometry\n';
  const input = () => ({ files: [{ file: 'Dependency.lean', source: 'theorem dependency : True := by sorry\n' },
    { file: 'Submission.lean', source }, { file: 'lakefile.lean', source: 'theorem configuration : True := by sorry\n' }],
    modules: [{ file: 'Dependency.lean', sourceRoot: '.', module: 'Dependency' },
      { file: 'Submission.lean', sourceRoot: '.', module: 'Submission' }],
    file: 'Submission.lean', context: 'Geometry.original', type: 'True' });

  it('uses identical bytes and queries after erasing different local proof bodies', () => {
    const original = input(), changed = structuredClone(original);
    for (const file of changed.files) if (file.file !== 'lakefile.lean')
      file.source = file.source.replace('by sorry', 'by\n  -- proof-only comment\n  trivial');
    const first = leanTypeDiagnosticProjection(original), next = leanTypeDiagnosticProjection(changed);
    expect(next.digest).toBe(first.digest); expect(next.files).toEqual(first.files); expect(next.commands).toBe(first.commands);
    expect(original.files[0].source).toContain('by sorry'); expect(changed.files[0].source).toContain('trivial');
  });

  it.each(['definition', 'theorem-type', 'external-comment', 'configuration', 'scope', 'query-type', 'module-order', 'module-mapping'] as const)
  ('keeps %s differences in the exact projection identity', change => {
    const original = input(), changed = structuredClone(original);
    if (change === 'definition') changed.files[1].source = source.replace('value : Nat := 0', 'value : Nat := 1');
    if (change === 'theorem-type') changed.files[1].source = source.replace('original : True', 'original : False');
    if (change === 'external-comment') changed.files[1].source = '-- line-sensitive input\n' + source;
    if (change === 'configuration') changed.files[2].source = changed.files[2].source.replace('by sorry', 'by trivial');
    if (change === 'scope') changed.files[1].source = source.replace('open Nat', 'open Int');
    if (change === 'query-type') changed.type = 'False';
    if (change === 'module-order') changed.modules.reverse();
    if (change === 'module-mapping') changed.modules[1].sourceRoot = 'src';
    expect(leanTypeDiagnosticProjection(changed).digest).not.toBe(leanTypeDiagnosticProjection(original).digest);
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
    const modules = mathLocalModuleBuildOrder(root, 'Submission.lean');
    const expected = leanTypeDiagnosticProjection({ modules,
      files: modules.map(module => ({ file: module.file, source: fs.readFileSync(path.join(root, module.file), 'utf8') })),
      file: 'Submission.lean', context: 'Geometry.original', type: 'Box \u2192 Nat' });
    const result = await check('Box \u2192 Nat');
    expect(result.status, result.stdout + result.stderr).toBe('elaborated');
    expect(result).toMatchObject({ status: 'elaborated', exitCode: 0, type: 'Terms.Box \u2192 Nat', proofAcceptance: 'not-assessed' });
    expect(fs.readFileSync(path.join(root, 'Submission.lean'))).toEqual(before);
    expect(fs.existsSync(path.join(root, '.lake', 'build', 'lib', 'lean', 'Submission.olean'))).toBe(false);
    const text = fs.readFileSync(path.join(root, result.artifact.path), 'utf8');
    expect(mathDigest(text)).toBe(result.artifact.digest);
    const artifact = JSON.parse(text);
    expect(artifact).toMatchObject({ authority: 'advisory-type-elaboration', proofAcceptance: 'not-assessed',
      sourceDigest: result.sourceSnapshotDigest, projectionDigest: expected.digest, queryDigest: mathDigest(expected.commands) });
    expect(result.projectionDigest).toBe(expected.digest);
    const clone = path.join(root, path.dirname(result.artifact.path), 'project');
    for (const file of expected.files) expect(fs.readFileSync(path.join(clone, file.file), 'utf8')).toBe(file.source);
    expect(fs.readFileSync(path.join(clone, expected.query), 'utf8')).toBe(expected.commands);
    expect(artifact.files.find(file => file.file === 'Submission.lean').digest).toBe(mathDigest(before));
    expect(result.diagnosticArtifacts.length).toBeGreaterThan(0);
    expect(result.diagnosticArtifacts.every(reference => fs.existsSync(path.join(root, reference.path)))).toBe(true);
  });

  it('reuses a real successful query after proof-only edits without starting another sandbox command', async () => {
    const task: CooperativeTask = { id: 'helper', kind: 'lemma', objective: 'Prove helper', dependsOn: [], revision: 0,
      theoremName: 'Geometry.helper', proofPath: 'Submission.lean', type: 'Box -> Nat' };
    const problem = { targets: [{ theoremName: 'Geometry.original', proofPath: 'Submission.lean' }] } as SolverProblem;
    const cache = new TaskTypePreflightCache(), input = { task, problem, dependencies: [], projectRoot: root,
      environmentDigest: 'test-environment', env: {}, timeoutMs: Infinity };
    const first = await cache.check(input), commands = run.mock.calls.length;
    expect(first.result.status, first.result.reason).toBe('elaborated'); expect(commands).toBeGreaterThan(0);
    const file = path.join(root, 'Submission.lean');
    fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('exact nonexistent_proof', '-- proof-only edit\n  exact True.intro'));
    const next = await cache.check(input);
    expect(run).toHaveBeenCalledTimes(commands); expect(first.current()).toBe(false); expect(next.current()).toBe(true);
    expect(next.result).toMatchObject({ status: 'elaborated', type: 'Terms.Box \u2192 Nat', artifact: first.result.artifact,
      proofAcceptance: 'not-assessed', projectionReuse: { originInputDigest: first.result.inputDigest } });
    expect(next.result.inputDigest).not.toBe(first.result.inputDigest);
    const manifest = JSON.parse(fs.readFileSync(path.join(root, first.result.artifact!.path), 'utf8'));
    expect(next.result.projectionReuse).toMatchObject({ originSourceDigest: manifest.sourceDigest, projectionDigest: manifest.projectionDigest });
    expect(next.result.projectionReuse!.sourceDigest).not.toBe(manifest.sourceDigest);
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

  it('checks only the selected closed expression and exports its actual references', async () => {
    const result = await checkLeanType({ projectRoot: root, file: 'Submission.lean', context: 'Geometry.original',
      type: '∀ n : Nat, n = n', expression: 'fun n => Eq.refl n', timeoutMs: 30_000 });
    expect(result.status, result.stdout + result.stderr).toBe('elaborated');
    expect(result.constants).toContain('Eq.refl');
    expect(result.evidence).toBe('advisory-application-elaboration');
    const manifest = JSON.parse(fs.readFileSync(path.join(root, result.artifact.path), 'utf8'));
    expect(manifest).toMatchObject({ requestedExpression: 'fun n => Eq.refl n', proofAcceptance: 'not-assessed',
      environment: result.environment });
    expect(leanTypeDiagnosticProjection({ files: [{ file: 'Submission.lean', source: fs.readFileSync(path.join(root, 'Submission.lean'), 'utf8') }],
      modules: [{ file: 'Submission.lean', sourceRoot: '.', module: 'Submission' }], file: 'Submission.lean', context: 'Geometry.original',
      type: 'True', expression: 'True.intro' }).digest).not.toBe(leanTypeDiagnosticProjection({
        files: [{ file: 'Submission.lean', source: fs.readFileSync(path.join(root, 'Submission.lean'), 'utf8') }],
        modules: [{ file: 'Submission.lean', sourceRoot: '.', module: 'Submission' }], file: 'Submission.lean',
        context: 'Geometry.original', type: 'True' }).digest);
  });

  it.each([
    ['True', '(0 : Nat)'], ['True', 'by sorry'], ['True', 'by exact ?_'],
    ['True', 'missing_hypothesis'], ['∀ n : Nat, n = n', 'Eq.refl 0'],
  ])('retains scoped failure for expected type %s and expression %s', async (type, expression) => {
    const result = await checkLeanType({ projectRoot: root, file: 'Submission.lean', context: 'Geometry.original',
      type, expression, timeoutMs: 30_000 });
    expect(result.status, result.stdout + result.stderr).toBe('failed');
    expect(result.proofAcceptance).toBe('not-assessed');
    expect(result.firstBlocking).toBeDefined();
  });

  it('detects original-source changes during the disposable application check', async () => {
    const previous = run.getMockImplementation()!;
    run.mockImplementation(async input => {
      const result = await previous(input);
      if (input.args.at(-1).includes('TypeDiagnostic.lean'))
        fs.appendFileSync(path.join(root, 'Submission.lean'), '\n-- concurrently changed input\n');
      return result;
    });
    await expect(checkLeanType({ projectRoot: root, file: 'Submission.lean', context: 'Geometry.original',
      type: 'True', expression: 'True.intro', timeoutMs: 30_000 })).rejects.toThrow('math_type_diagnostics_source_changed');
  });
});
