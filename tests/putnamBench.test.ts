import { createHash } from 'node:crypto';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, describe, expect, it, vi } from 'vitest';
import { getLeanTaskEnvironment } from '../src/math/leanTaskEnvironment';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { assertSolverProjectSources, readSolverProblem } from '../src/solver/problem';
import { bootstrapPutnamBenchProblem, DEFAULT_PUTNAM_SAMPLE_SEED, PUTNAM_BENCH_REPOSITORY_URL,
  PUTNAM_BENCH_SOURCE_COMMIT, readPutnamBenchCatalog, readPutnamBenchProblem, samplePutnamBench } from '../src/math/putnamBench';

const mocks = vi.hoisted(() => ({ repositories: new Map<string, {
  files: Map<string, Buffer>; modes: Map<string, string>; oids: Map<string, string>; commit?: string;
}>(), reads: [] as string[][] }));
vi.mock('../src/math/mathGit', async importOriginal => {
  const actual = await importOriginal<typeof import('../src/math/mathGit')>();
  const bytes = (root: string, args: readonly string[], options: any): Buffer => {
    const fixture = mocks.repositories.get(root);
    if (!fixture) return actual.mathGitBytes(root, args, options);
    mocks.reads.push([...args]);
    if (args.includes('ls-tree')) return Buffer.from([...fixture.files].sort(([a], [b]) => a.localeCompare(b)).map(([file, body]) => {
      const oid = fixture.oids.get(file) ?? createHash('sha1').update(`blob ${body.length}\0`).update(body).digest('hex');
      return `${fixture.modes.get(file) ?? '100644'} blob ${oid}\t${file}\0`;
    }).join(''));
    if (args.includes('cat-file')) {
      const file = args.at(-1)!.split(':').slice(1).join(':');
      const content = fixture.files.get(file);
      if (!content) throw new Error('fixture_blob_missing');
      return content;
    }
    throw new Error('fixture_unexpected_git_bytes');
  };
  return { ...actual, mathGitBytes: vi.fn(bytes), mathGitText: vi.fn((root: string, args: readonly string[], options: any) => {
    const fixture = mocks.repositories.get(root);
    if (!fixture) return actual.mathGitText(root, args, options);
    mocks.reads.push([...args]);
    if (args.includes('rev-parse')) return fixture.commit ?? '13d042960189f55d748048317c24064a0e2215ea';
    return bytes(root, args, options).toString('utf8').trim();
  }) };
});

const roots: string[] = [];
afterEach(() => {
  mocks.repositories.clear(); mocks.reads.length = 0;
  for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true });
});
const sourceFor = (id: string) => `import Mathlib\n\n/-- A frozen Putnam statement. -/\ntheorem ${id} (n : Nat) : n = n := by\n  sorry\n`;
function repository(sources: Record<string, string> = { putnam_1962_a1: sourceFor('putnam_1962_a1') }) {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'putnam-bench-fixture-')); roots.push(root);
  const environment = getLeanTaskEnvironment('mathlib');
  const manifest = JSON.parse(environment.files['lake-manifest.json']);
  manifest.name = 'putnam'; manifest.fixedToolchain = false;
  const mathlib = manifest.packages.find((item: any) => item.name === 'mathlib');
  mathlib.url = mathlib.url.replace(/\.git$/u, ''); mathlib.inputRev = 'v4.33.0'; mathlib.scope = '';
  const files = new Map<string, Buffer>([
    ['lean4/lean-toolchain', Buffer.from(`${environment.toolchain}\n`)],
    ['lean4/lake-manifest.json', Buffer.from(JSON.stringify(manifest))],
    ['lean4/lakefile.lean', Buffer.from('import Lake\nopen Lake DSL\npackage putnam\nrequire mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.33.0"\n')],
    ...Object.entries(sources).map(([id, source]) => [`lean4/src/${id}.lean`, Buffer.from(source)] as [string, Buffer]),
  ]);
  const fixture = { files, modes: new Map<string, string>(), oids: new Map<string, string>() };
  mocks.repositories.set(root, fixture);
  return { root, ...fixture, manifest };
}

describe('pinned PutnamBench proof tasks', () => {
  it('samples a stable pool by the documented seed, independent of listing order', () => {
    const ids = ['putnam_1962_a1', 'putnam_1962_a2', 'putnam_1962_a3', 'putnam_2025_b1', 'putnam_2025_b2'];
    const fixture = repository(Object.fromEntries(ids.map(id => [id, sourceFor(id)])));
    const catalog = readPutnamBenchCatalog(fixture.root), selected = samplePutnamBench(catalog);
    expect(catalog).toMatchObject({ sourceCommit: PUTNAM_BENCH_SOURCE_COMMIT, repositoryUrl: PUTNAM_BENCH_REPOSITORY_URL,
      toolchain: getLeanTaskEnvironment('mathlib').toolchain, mathlibRevision: getLeanTaskEnvironment('mathlib').mathlibRevision,
      environmentDigest: getLeanTaskEnvironment('mathlib').dependencyDigest, excluded: [], excludedCounts: {} });
    expect(selected).toMatchObject({ algorithm: 'sha256-seed-nul-id-v1', seed: DEFAULT_PUTNAM_SAMPLE_SEED,
      count: 3, eligibleCount: 5, poolDigest: expect.stringMatching(/^[a-f0-9]{64}$/u) });
    expect(selected.problems.map(problem => problem.id)).toEqual(['putnam_2025_b2', 'putnam_2025_b1', 'putnam_1962_a2']);
    expect(samplePutnamBench({ ...catalog, problems: [...catalog.problems].reverse() })).toEqual(selected);
    const changed = { ...catalog, problems: catalog.problems.map((problem, index) => index ? problem :
      { ...problem, source: problem.source + '\n', sourceSha256: mathDigest(problem.source + '\n') }) };
    expect(samplePutnamBench(changed).poolDigest).not.toBe(selected.poolDigest);
    for (const invalid of [0, -1, 1.5, 6]) expect(() => samplePutnamBench(catalog, invalid)).toThrow('putnam_bench_sample_count_invalid');
    for (const invalid of ['', 'bad\0seed', '\ud800']) expect(() => samplePutnamBench(catalog, 1, invalid)).toThrow('putnam_bench_sample_seed_invalid');
  });

  it('reads original bytes from pinned blobs even when the checkout is edited', () => {
    const fixture = repository(), file = 'lean4/src/putnam_1962_a1.lean';
    fs.mkdirSync(path.dirname(path.join(fixture.root, file)), { recursive: true });
    fs.writeFileSync(path.join(fixture.root, file), 'axiom replaced_checkout : False\n');
    fs.writeFileSync(path.join(fixture.root, 'informal_solution.json'), '{"answer":"do not read"}');
    const problem = readPutnamBenchProblem(fixture.root, 'putnam_1962_a1');
    expect(problem).toEqual({ id: 'putnam_1962_a1', sourceRelativePath: file,
      source: sourceFor('putnam_1962_a1'), sourceSha256: mathDigest(fixture.files.get(file)!), theoremNames: ['putnam_1962_a1'] });
    const blobs = mocks.reads.filter(args => args.includes('cat-file'));
    expect(blobs.every(args => args.includes('--no-replace-objects') && args.at(-1)!.startsWith(`${PUTNAM_BENCH_SOURCE_COMMIT}:`))).toBe(true);
    expect(blobs.some(args => args.at(-1)!.includes('informal_solution'))).toBe(false);
  });

  it('distinguishes answer holes from proof regions that existing source guards freeze', () => {
    const fixture = repository({
      putnam_1962_a1: 'import Mathlib\ndef answer : Nat := by\n  sorry\ntheorem putnam_1962_a1 : answer = 0 := by\n  sorry\n',
      putnam_1962_a2: 'import Mathlib\ndef answer : Nat := _\ntheorem putnam_1962_a2 : answer = 0 := by\n  sorry\n',
      putnam_1962_a3: 'import Mathlib\ntheorem putnam_1962_a3 : True :=\nsorry\n',
      putnam_1962_a4: sourceFor('putnam_1962_a4'),
    });
    const catalog = readPutnamBenchCatalog(fixture.root);
    expect(catalog.problems.map(problem => problem.id)).toEqual(['putnam_1962_a4']);
    expect(catalog.excludedCounts).toEqual({ answer_definition_placeholder: 2, proof_region_not_editable: 1 });
    expect(() => readPutnamBenchProblem(fixture.root, 'putnam_1962_a1')).toThrow('putnam_bench_problem_ineligible:answer_definition_placeholder');
  });

  it.each([
    ['axiom extra : True\n', 'unsupported_declaration'],
    ['constant extra : Nat\n', 'unsupported_declaration'],
    ['lemma extra : True := by\n  sorry\n', 'single_named_theorem_required'],
  ])('rejects unsupported source declarations: %s', (prefix, reason) => {
    const fixture = repository({ putnam_1962_a1: prefix + sourceFor('putnam_1962_a1') });
    expect(readPutnamBenchCatalog(fixture.root).excludedCounts).toEqual({ [reason]: 1 });
  });

  it('ignores tokens in nested comments and strings while retaining frozen definitions', () => {
    const source = 'import Mathlib\n/- sorry /- axiom fake : False -/ -/\ndef label : String := "sorry axiom"\ndef answer : Nat := 7\n' +
      'theorem putnam_1962_a1 : answer = 7 := by\n  sorry\n';
    const fixture = repository({ putnam_1962_a1: source });
    expect(readPutnamBenchCatalog(fixture.root).problems[0]?.source).toBe(source);
  });

  it('rejects invalid IDs, unknown problems, non-regular modes and mismatched blob bytes', () => {
    const fixture = repository();
    for (const id of ['../putnam_1962_a1', 'putnam_1962_a7', 'putnam_1962_a1\n'])
      expect(() => readPutnamBenchProblem(fixture.root, id)).toThrow('putnam_bench_problem_id_invalid');
    expect(() => readPutnamBenchProblem(fixture.root, 'putnam_1962_a2')).toThrow('putnam_bench_problem_not_found');
    const file = 'lean4/src/putnam_1962_a1.lean';
    fixture.modes.set(file, '120000');
    expect(readPutnamBenchCatalog(fixture.root).excludedCounts).toEqual({ non_regular_source: 1 });
    expect(() => readPutnamBenchProblem(fixture.root, 'putnam_1962_a1')).toThrow('putnam_bench_file_mode_invalid');
    fixture.modes.clear(); fixture.oids.set(file, '0'.repeat(40));
    expect(() => readPutnamBenchCatalog(fixture.root)).toThrow('putnam_bench_blob_identity_mismatch');
  });

  it('rejects toolchain, direct and transitive dependency mismatches', () => {
    const fixture = repository();
    fixture.files.set('lean4/lean-toolchain', Buffer.from('leanprover/lean4:v4.32.0\n'));
    expect(() => readPutnamBenchCatalog(fixture.root)).toThrow('putnam_bench_toolchain_mismatch');
    fixture.files.set('lean4/lean-toolchain', Buffer.from(getLeanTaskEnvironment('mathlib').toolchain));
    for (const dependency of ['mathlib', 'aesop']) {
      const manifest = structuredClone(fixture.manifest);
      manifest.packages.find((item: any) => item.name === dependency).rev = '0'.repeat(40);
      fixture.files.set('lean4/lake-manifest.json', Buffer.from(JSON.stringify(manifest)));
      expect(() => readPutnamBenchCatalog(fixture.root)).toThrow('putnam_bench_dependencies_mismatch');
    }
    fixture.files.set('lean4/lake-manifest.json', Buffer.from(JSON.stringify(fixture.manifest)));
    fixture.files.set('lean4/lakefile.lean', Buffer.from('require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "other"\n'));
    expect(() => readPutnamBenchCatalog(fixture.root)).toThrow('putnam_bench_dependencies_mismatch');
  });

  it('bootstraps an unchanged mathlib Lean task readable by solver guards, with frozen definitions', () => {
    const source = 'import Mathlib\n\ndef answer : Nat := 7\n\ntheorem putnam_1962_a1 : answer = 7 := by\n  sorry\n';
    const fixture = repository({ putnam_1962_a1: source }), workspace = path.join(fixture.root, 'run');
    const receipt = bootstrapPutnamBenchProblem({ repositoryRoot: fixture.root, problemId: 'putnam_1962_a1', workspaceRoot: workspace });
    expect(receipt).toMatchObject({ kind: 'lean-task', environment: 'mathlib',
      environmentDigest: getLeanTaskEnvironment('mathlib').dependencyDigest });
    expect(receipt.contract.formalStatement).toBe(source);
    expect(receipt.contract.informalStatement).toContain('putnam_1962_a1');
    expect(receipt.contract.informalStatement).toContain(PUTNAM_BENCH_SOURCE_COMMIT);
    expect(receipt.contract.informalStatement).not.toContain('informal_solution');
    expect(fs.readFileSync(path.join(receipt.projectRoot, 'Submission.lean'))).toEqual(Buffer.from(source));
    const problem = readSolverProblem(workspace, receipt.activeProblemPath);
    expect(problem.kind).toBe('lean-task');
    expect(problem.targets).toMatchObject([{ theoremName: 'putnam_1962_a1', proofPath: 'Submission.lean' }]);
    expect(() => assertSolverProjectSources(problem, receipt.projectRoot)).not.toThrow();
    fs.writeFileSync(path.join(receipt.projectRoot, 'Submission.lean'), source.replace(':= 7', ':= 8'));
    expect(() => assertSolverProjectSources(problem, receipt.projectRoot)).toThrow('math_original_declaration_changed');
  });
});
