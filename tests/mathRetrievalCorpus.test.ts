import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { createMathRetrievalCorpus, searchMathRetrievalCorpus, searchMathRetrievalCorpusBatch } from '../src/math/mathRetrievalCorpus';
import { mathDigest } from '../src/math/mathRuntimeIo';
import * as verifier from '../src/math/verifier';
import * as installedPackageSearch from '../src/math/installedPackageSearch';

describe('frozen Lean declaration lookup', () => {
  let root: string;
  let source: string;
  beforeEach(() => {
    root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'math-retrieval-')));
    source = path.join(root, '.lake/packages/mathlib/Mathlib/Algebra/Order/Archimedean.lean');
    fs.mkdirSync(path.dirname(source), { recursive: true });
    fs.writeFileSync(path.join(root, '.lake/packages/mathlib/lakefile.toml'), 'name = "mathlib"\n');
    fs.writeFileSync(path.join(root, 'lean-toolchain'), 'leanprover/lean4:v4.31.0');
    fs.writeFileSync(path.join(root, 'lake-manifest.json'), JSON.stringify({ packages: [
      { name: 'mathlib', rev: 'a'.repeat(40), url: 'https://github.com/leanprover-community/mathlib4' },
    ] }));
    fs.writeFileSync(source, 'namespace Order\n/- lemma exists_lt_nsmul_fake : True := by trivial -/\n' +
      'lemma exists_lt_nsmul (a b : Nat) : Exists (fun n : Nat => a < n * b) := by sorry\n' +
      'lemma helper (exists_lt_nsmul : True) : True := by sorry\nend Order\n');
    const excluded = path.join(root, '.lake/packages/mathlib/tests/Answer.lean');
    fs.mkdirSync(path.dirname(excluded));
    fs.writeFileSync(excluded, 'lemma exists_lt_nsmul_solution : True := by trivial');
  });
  afterEach(() => {
    vi.restoreAllMocks();
    fs.rmSync(root, { recursive: true, force: true });
    fs.rmSync(`${root}.cache`, { recursive: true, force: true });
  });

  it.each(['source text', 'package revision', 'file selection'])(
    'rejects changes to %s between corpus captures', async change => {
      const capture = installedPackageSearch.captureInstalledLeanSources;
      vi.spyOn(installedPackageSearch, 'captureInstalledLeanSources').mockImplementationOnce(async (...args) => {
        const sources = await capture(...args);
        if (change === 'source text') fs.appendFileSync(source, '\nlemma changed : True := by trivial');
        else if (change === 'package revision') {
          const manifest = path.join(root, 'lake-manifest.json');
          fs.writeFileSync(manifest, fs.readFileSync(manifest, 'utf8').replace('a'.repeat(40), 'b'.repeat(40)));
        } else fs.writeFileSync(path.join(path.dirname(source), 'Added.lean'), 'lemma added : True := by trivial');
        return sources;
      });
      await expect(createMathRetrievalCorpus(root, ['mathlib'])).rejects.toThrow('math_corpus_capture_changed');
    }
  );

  it.each([false, true])('bounds concurrent source reads and closes every handle (invalid UTF-8: %s)', async invalid => {
    for (let index = 0; index < 24; index++) {
      fs.writeFileSync(path.join(path.dirname(source), `Batch${String(index).padStart(2, '0')}.lean`),
        invalid && index === 0 ? Buffer.from([0xff]) : 'lemma batch_helper : True := by trivial');
    }
    const open = fs.promises.open.bind(fs.promises);
    let active = 0, peak = 0;
    vi.spyOn(fs.promises, 'open').mockImplementation(async (file, flags, mode) => {
      active++;
      peak = Math.max(peak, active);
      try {
        const handle = await open(file, flags, mode);
        const close = handle.close.bind(handle);
        vi.spyOn(handle, 'close').mockImplementation(async () => {
          try { await close(); } finally { active--; }
        });
        return handle;
      } catch (error) { active--; throw error; }
    });
    const captured = installedPackageSearch.captureInstalledLeanSources(root, ['mathlib']);
    if (invalid) await expect(captured).rejects.toThrow();
    else {
      const sources = await captured;
      expect(sources).toHaveLength(25);
      expect(sources.map(item => item.sourceFile)).toEqual(sources.map(item => item.sourceFile).toSorted());
    }
    expect(peak).toBeGreaterThan(1);
    expect(peak).toBeLessThanOrEqual(16);
    expect(active).toBe(0);
  });

  it('recognizes every declaration keyword while preserving Unicode boundaries and binder defaults', () => {
    const declarations = verifier.inspectLeanDeclarations([
      '/- theorem hidden : True := /- lemma nested : True := -/ trivial -/',
      'def αlemma : String := "theorem fake : Nat := 0"',
      'abbrev abbreviated : Nat := 0',
      'opaque hiddenValue : Nat := 0',
      'instance namedInstance : Inhabited Nat := ⟨0⟩',
      "theorem theorem' (n : Nat := 0) : n = n := by rfl",
      "lemma result' : True := by trivial",
      'def 𐐀def : Nat := 0',
    ].join('\n'));
    expect(declarations.map(({ name, kind }) => [name, kind])).toEqual([
      ['αlemma', 'definition'], ['abbreviated', 'definition'], ['hiddenValue', 'definition'],
      ['namedInstance', 'instance'], ["theorem'", 'theorem'], ["result'", 'theorem'], ['𐐀def', 'definition'],
    ]);
    expect(declarations[4].declarationType).toBe("theorem' (n : Nat := 0) : n = n");
  });

  it('ranks exact names above signature matches and excludes comments and solution/test paths', async () => {
    const corpus = await createMathRetrievalCorpus(root, ['mathlib']);
    const result = searchMathRetrievalCorpus(root, corpus, 'exists_lt_nsmul');
    expect(result.results.map(item => item.name)).toEqual(['exists_lt_nsmul', 'helper']);
    expect(result.results[0]).toMatchObject({ sourceModule: 'Mathlib.Algebra.Order.Archimedean',
      qualifiedName: 'Order.exists_lt_nsmul', sourceLine: 3,
      sourceHeader: 'exists_lt_nsmul (a b : Nat) : Exists (fun n : Nat => a < n * b)' });
    expect(result.results[0].sourceHeader).not.toContain('sorry');
    expect(searchMathRetrievalCorpus(root, corpus, 'Archimedean nsmul').results).toHaveLength(2);
    expect(searchMathRetrievalCorpus(root, corpus, 'not_found').results).toEqual([]);
  });

  it('finds qualified names even when their namespace is absent from the header and module', async () => {
    fs.writeFileSync(source, 'namespace Real\nlemma sqrt_nonneg (x : Nat) : 0 ≤ x := by sorry\nend Real\n');
    const corpus = await createMathRetrievalCorpus(root, ['mathlib']);
    const result = searchMathRetrievalCorpus(root, corpus, 'Real.sqrt_nonneg');
    expect(result.results).toHaveLength(1);
    expect(result.results[0]).toMatchObject({ name: 'sqrt_nonneg', qualifiedName: 'Real.sqrt_nonneg', sourceLine: 2 });
  });

  it('ranks by the goal conclusion and types independently of local variable names', async () => {
    fs.writeFileSync(source, [
      'lemma bound_a_nat (x y : Nat) (h : x ≤ y) : x ≤ y := by sorry',
      'lemma bound_b_eq (x y : Real) (h : x = y) : x = y := by sorry',
      'lemma bound_c_real (x y : Real) (h : x ≤ y) : x ≤ y := by sorry',
      'lemma bound_d_exists (x y : Real) : ∃ z : Real, z ≤ y := by sorry',
      'lemma bound_z_helper (x y : Real) (bound_b_eq : True) : x ≤ y := by sorry',
    ].join('\n'));
    const corpus = await createMathRetrievalCorpus(root, ['mathlib']);
    const goal = 'u v : ℝ\nh : u ≤ v\n⊢ u ≤ v';
    expect(searchMathRetrievalCorpus(root, corpus, 'bound').results[0].name).toBe('bound_a_nat');
    const ranked = searchMathRetrievalCorpus(root, corpus, 'bound', 15, goal);
    expect(ranked.results[0].name).toBe('bound_c_real');
    expect(searchMathRetrievalCorpus(root, corpus, 'bound', 15, 'left right : ℝ\nhyp : left ≤ right\n⊢ left ≤ right')).toEqual(ranked);
    expect(searchMathRetrievalCorpusBatch(root, corpus, ['bound', 'bound_b_eq'], 15, goal).queries[0]).toEqual(ranked);
    expect(searchMathRetrievalCorpus(root, corpus, 'bound_b_eq', 15, goal).results[0].name).toBe('bound_b_eq');
    for (const invalid of ['', ' ', 'x\0y', 'α'.repeat(8001)])
      expect(() => searchMathRetrievalCorpus(root, corpus, 'bound', 15, invalid)).toThrow('math_search_invalid_goal');
    fs.appendFileSync(source, '\n-- changed');
    expect(() => searchMathRetrievalCorpus(root, corpus, 'bound', 15, goal)).toThrow('math_corpus_source_changed');
  });

  it.each([
    'u v : ℝ\n⊢ u ≤ v',
    'u v : ℝ\n⊢ ((u ≤ v))',
    '⊢ ∀ (u v : ℝ), (u ≤ v)',
    'u v : ℝ\n⊢ True → (u ≤ v)',
  ])('ranks the conclusion independently of existential hypotheses and outer wrappers: %s', async goal => {
    fs.writeFileSync(source, [
      'variable (w : Real) (h : ∃ n : Nat, n = n)',
      'lemma compare_a_exists : ∃ n : Nat, n = n := by sorry',
      'lemma compare_b_order (x y : Real) : ((x ≤ y)) := by sorry',
      'lemma compare_c_eq (x y : Real) : x = y := by sorry',
    ].join('\n'));
    const corpus = await createMathRetrievalCorpus(root, ['mathlib']);
    expect(searchMathRetrievalCorpus(root, corpus, 'compare', 15, goal).results[0].name).toBe('compare_b_order');
  });

  it.each([
    ['∃ witness : Nat, witness = witness → witness = witness', 'choice_b_exists'],
    ['∀ (witness : Nat), witness = witness', 'choice_a_eq'],
    ['¬ (u = v)', 'choice_c_not'],
    ['u = v ↔ u ≤ v', 'choice_d_iff'],
  ])('recognizes a wrapped quantified or logical conclusion: %s', async (target, expected) => {
    fs.writeFileSync(source, [
      'lemma choice_a_eq (x y : Nat) : x = y := by sorry',
      'lemma choice_b_exists : (∃ n : Nat, n = n → n = n) := by sorry',
      'lemma choice_c_not (x y : Nat) : (¬ (x = y)) := by sorry',
      'lemma choice_d_iff (x y : Nat) : (x = y ↔ x ≤ y) := by sorry',
    ].join('\n'));
    const corpus = await createMathRetrievalCorpus(root, ['mathlib']);
    expect(searchMathRetrievalCorpus(root, corpus, 'choice', 15, `u v : Nat\n⊢ (${target})`).results[0].name).toBe(expected);
  });

  it('tracks nested namespaces, sections and root names while ignoring scope commands in comments and strings', async () => {
    const lines = [
      'namespace A.B -- comment',
      'section Local',
      'noncomputable section',
      'public section',
      '/- namespace Hidden\n/- nested -/ end Hidden -/',
      'namespace Ξ',
      'def message : String := "namespace Fake\nend Ξ"',
      'lemma step : True := by trivial',
      'lemma _root_.Global.step : True := by trivial',
      'end Ξ',
      'end',
      'end',
      'end Local',
      'lemma step : True := by trivial',
      'end A.B',
      'namespace Other',
      'lemma step : True := by trivial',
      'end Other',
      'lemma top : True := by trivial',
    ];
    const contents = lines.join('\r\n');
    fs.writeFileSync(source, contents);
    const corpus = await createMathRetrievalCorpus(root, ['mathlib']);
    const nested = searchMathRetrievalCorpus(root, corpus, 'A.B.Ξ.step');
    expect(nested.results).toHaveLength(1);
    expect(nested.results[0].sourceLine).toBe(contents.slice(0, contents.indexOf('lemma step')).split('\n').length);
    for (const name of ['A.B.step', 'Global.step', 'Other.step', 'top']) {
      const result = searchMathRetrievalCorpus(root, corpus, name);
      expect(result.results[0].qualifiedName).toBe(name);
    }
    expect(searchMathRetrievalCorpus(root, corpus, 'Fake.step').results).toEqual([]);
    expect(searchMathRetrievalCorpus(root, corpus, 'Hidden.step').results).toEqual([]);
  });

  it('fails closed when any frozen source changes, even an unrelated declaration', async () => {
    const other = path.join(path.dirname(source), 'Other.lean');
    fs.writeFileSync(other, 'lemma unrelated : True := by trivial');
    const corpus = await createMathRetrievalCorpus(root, ['mathlib']);
    fs.appendFileSync(other, '\n-- changed');
    expect(() => searchMathRetrievalCorpus(root, corpus, 'exists_lt_nsmul')).toThrow('math_corpus_source_changed');
  });

  it('skips parsing unrelated sources while still verifying their frozen content', async () => {
    const unrelated = 'lemma unrelated : True := by trivial';
    const other = path.join(path.dirname(source), 'Other.lean');
    fs.writeFileSync(other, unrelated);
    const corpus = await createMathRetrievalCorpus(root, ['mathlib']);
    const inspect = vi.spyOn(verifier, 'inspectLeanDeclarations');
    const reads = vi.spyOn(fs, 'openSync');
    expect(searchMathRetrievalCorpus(root, corpus, 'Order.exists_lt_nsmul').results[0].qualifiedName)
      .toBe('Order.exists_lt_nsmul');
    expect(inspect).toHaveBeenCalledTimes(1);
    expect(inspect).not.toHaveBeenCalledWith(unrelated);
    expect(reads.mock.calls.some(call => call[0] === other)).toBe(true);
    fs.appendFileSync(other, '\n-- changed');
    expect(() => searchMathRetrievalCorpus(root, corpus, 'Order.exists_lt_nsmul')).toThrow('math_corpus_source_changed');
  });

  it('returns active variable and open context, excluding ended sections and comments', async () => {
    fs.writeFileSync(source, 'open scoped BigOperators\nnamespace Finset\nvariable {α : Type*}\nsection Local\n' +
      'variable [OrderedAddCommMonoid α]\nvariable (f :\n  α → α)\n' +
      '/- variable (fake : False) -/\nlemma sum_bound : True := by trivial\nend Local\n' +
      'lemma outside : True := by trivial\nend Finset\nlemma global : True := by trivial\n');
    const corpus = await createMathRetrievalCorpus(root, ['mathlib']);
    const local = searchMathRetrievalCorpus(root, corpus, 'Finset.sum_bound').results[0];
    expect(local.sourceContext).toContain('open scoped BigOperators');
    expect(local.sourceContext).toContain('variable {α : Type*}');
    expect(local.sourceContext).toContain('variable [OrderedAddCommMonoid α]');
    expect(local.sourceContext).toContain('α → α)');
    expect(local.sourceContext).not.toContain('fake');
    const outside = searchMathRetrievalCorpus(root, corpus, 'Finset.outside').results[0];
    expect(outside.sourceContext).toContain('variable {α : Type*}');
    expect(outside.sourceContext).not.toContain('OrderedAddCommMonoid');
    expect(searchMathRetrievalCorpus(root, corpus, 'global').results[0].sourceContext).toBe('open scoped BigOperators');
  });

  it('finds inherited section assumptions and ranks explicit header matches first', async () => {
    fs.writeFileSync(source, [
      'namespace Bounds',
      'section Ordered',
      'variable {α : Type*}',
      'variable [LinearOrderedRing α]',
      'lemma inherited_bound (x y : α) : x ≤ y → x ≤ y := by sorry',
      'end Ordered',
      'lemma explicit_bound {α : Type*} [LinearOrderedRing α] (x y : α) : x ≤ y → x ≤ y := by sorry',
      '/- variable [LinearOrderedRing Fake] -/',
      'lemma outside_bound : True := by trivial',
      'lemma body_bound : True := by',
      '  -- LinearOrderedRing appears only in the proof',
      '  trivial',
      'end Bounds',
    ].join('\n'));
    const corpus = await createMathRetrievalCorpus(root, ['mathlib']);
    const queries = ['LinearOrderedRing bound', 'LinearOrderedRing inherited_bound'];
    const batch = searchMathRetrievalCorpusBatch(root, corpus, queries);
    expect(batch.queries[0].results.map(item => item.name)).toEqual(['explicit_bound', 'inherited_bound']);
    expect(batch.queries[1].results[0]).toMatchObject({ qualifiedName: 'Bounds.inherited_bound',
      sourceContext: 'variable {α : Type*}\nvariable [LinearOrderedRing α]' });
    expect(batch.queries).toEqual(queries.map(query => searchMathRetrievalCorpus(root, corpus, query)));
    expect(searchMathRetrievalCorpus(root, corpus, 'LinearOrderedRing bound', 15, 'u v : Real\n⊢ u ≤ v').totalMatches).toBe(2);
  });

  it('finds scoped notation context without leaking ended scopes into later declarations', async () => {
    fs.writeFileSync(source, [
      'section Sums',
      'open scoped BigOperators',
      'lemma inside_sum : True := by trivial',
      'end Sums',
      'lemma outside_sum : True := by trivial',
    ].join('\n'));
    const corpus = await createMathRetrievalCorpus(root, ['mathlib']);
    expect(searchMathRetrievalCorpus(root, corpus, 'BigOperators sum').results.map(item => item.name)).toEqual(['inside_sum']);
  });

  it('shares source verification across queries while keeping single-query results and bounds', async () => {
    const corpus = await createMathRetrievalCorpus(root, ['mathlib']);
    const queries = ['exists_lt_nsmul', 'Order.helper', 'not_found', '  ORDER.EXISTS_LT_NSMUL  ', 'exists_lt_nsmul'];
    const expected = queries.map(query => searchMathRetrievalCorpus(root, corpus, query));
    const reads = vi.spyOn(fs, 'openSync');
    const result = searchMathRetrievalCorpusBatch(root, corpus, queries);
    expect(result.queries).toEqual(expected);
    expect(result.queries[0].results[0]).not.toBe(result.queries[4].results[0]);
    expect(reads.mock.calls.filter(call => call[0] === source)).toHaveLength(1);
    for (const queries of [[], Array(9).fill('helper')])
      expect(() => searchMathRetrievalCorpusBatch(root, corpus, queries)).toThrow('math_search_invalid_queries');
    expect(() => searchMathRetrievalCorpusBatch(root, corpus, ['helper', '---'])).toThrow('math_search_invalid_query');
  });

  it('caps the entire batch in bytes and marks shortened variable context', async () => {
    fs.writeFileSync(source, `variable (${Array(1000).fill('α').join(' ')} : Type)\n` +
      Array.from({ length: 50 }, (_, index) => `lemma bounded_${index} : True := by sorry`).join('\n'));
    const corpus = await createMathRetrievalCorpus(root, ['mathlib']);
    const batch = searchMathRetrievalCorpusBatch(root, corpus, Array(8).fill('bounded'), 64);
    expect(batch.queries.every(query => query.truncated && query.totalMatches === 50)).toBe(true);
    expect(batch.queries[0].results[0].contextTruncated).toBe(true);
    expect(Buffer.byteLength(JSON.stringify(batch))).toBeLessThanOrEqual(24_000);
  });

  it('keeps late exact matches and lexical order across large candidate pools', async () => {
    const names = Array.from({ length: 160 }, (_, index) => `needle_${String(index).padStart(3, '0')}`);
    fs.writeFileSync(source, names.toReversed().map(name => `lemma ${name} : True := by trivial`).join('\n'));
    fs.writeFileSync(path.join(path.dirname(source), 'ZLast.lean'),
      'lemma needle : True := by trivial\nlemma helper (needle : True) : True := by trivial');
    const corpus = await createMathRetrievalCorpus(root, ['mathlib']);
    const expected = ['needle', ...names, 'helper'];
    for (const limit of [1, 15, 64]) {
      for (const goal of [undefined, '⊢ True']) {
        const result = searchMathRetrievalCorpus(root, corpus, 'needle', limit, goal);
        expect(result.totalMatches).toBe(expected.length);
        expect(result.results.map(item => item.name)).toEqual(expected.slice(0, result.results.length));
        expect(result.results.length).toBeGreaterThan(0);
        expect(result.results.length).toBeLessThanOrEqual(limit);
        expect(result.truncated).toBe(true);
      }
    }
    const batch = searchMathRetrievalCorpusBatch(root, corpus, Array(8).fill('needle'), 64);
    for (const result of batch.queries) {
      expect(result.totalMatches).toBe(expected.length);
      expect(result.results.map(item => item.name)).toEqual(expected.slice(0, result.results.length));
    }
    expect(Buffer.byteLength(JSON.stringify(batch))).toBeLessThanOrEqual(24_000);
  });

  it('preserves module ordering and the earliest declarations when ranking keys tie', async () => {
    const names = Array.from({ length: 100 }, (_, index) => `Scope_${index}`);
    fs.writeFileSync(source, names.map(name =>
      `namespace ${name}\nlemma shared : True := by trivial\nend ${name}`).join('\n'));
    fs.writeFileSync(path.join(path.dirname(source), 'AFirst.lean'),
      'namespace First\nlemma shared : True := by trivial\nend First');
    const corpus = await createMathRetrievalCorpus(root, ['mathlib']);
    const expected = ['First.shared', ...names.map(name => `${name}.shared`)];
    for (const limit of [1, 15, 64]) {
      const result = searchMathRetrievalCorpus(root, corpus, 'shared', limit);
      expect(result.totalMatches).toBe(expected.length);
      expect(result.results.map(item => item.qualifiedName)).toEqual(expected.slice(0, result.results.length));
    }
  });

  it('preserves the frozen identity when packages move into a linked shared cache', async () => {
    const corpus = await createMathRetrievalCorpus(root, ['mathlib']);
    const packages = path.join(root, '.lake/packages');
    const cache = `${root}.cache`;
    fs.renameSync(packages, cache);
    fs.symlinkSync(cache, packages, 'dir');
    expect(await createMathRetrievalCorpus(root, ['mathlib'])).toEqual(corpus);
    const result = searchMathRetrievalCorpus(root, corpus, 'exists_lt_nsmul');
    expect(result.results[0].sourceFile).toBe('.lake/packages/mathlib/Mathlib/Algebra/Order/Archimedean.lean');
    fs.appendFileSync(path.join(cache, 'mathlib/Mathlib/Algebra/Order/Archimedean.lean'), '\n-- changed');
    expect(() => searchMathRetrievalCorpus(root, corpus, 'exists_lt_nsmul')).toThrow('math_corpus_source_changed');
  });

  it('still rejects links inside a package, even when the linked content has the same hash', async () => {
    const corpus = await createMathRetrievalCorpus(root, ['mathlib']);
    const external = path.join(root, 'external.lean');
    fs.renameSync(source, external);
    fs.symlinkSync(external, source);
    expect(() => searchMathRetrievalCorpus(root, corpus, 'exists_lt_nsmul')).toThrow('math_corpus_symlink');
  });

  it('bounds query, result count and serialized output while marking shortened headers', async () => {
    fs.writeFileSync(source, Array.from({ length: 50 }, (_, index) =>
      `lemma bounded_${index} (x : Nat) : ${'And True '.repeat(150)}True := by sorry`).join('\n'));
    const corpus = await createMathRetrievalCorpus(root, ['mathlib']);
    const result = searchMathRetrievalCorpus(root, corpus, 'bounded', 64);
    expect(result.totalMatches).toBe(50);
    expect(result.truncated).toBe(true);
    expect(result.results.length).toBeGreaterThan(0);
    expect(result.results[0].headerTruncated).toBe(true);
    expect(Buffer.byteLength(JSON.stringify(result))).toBeLessThanOrEqual(24_000);
    expect(searchMathRetrievalCorpus(root, corpus, 'bounded', 1).results).toHaveLength(1);
    for (const limit of [0, 65, 1.5]) expect(() => searchMathRetrievalCorpus(root, corpus, 'bounded', limit)).toThrow('math_search_invalid_limit');
    for (const query of ['', '---', 'a'.repeat(257)]) expect(() => searchMathRetrievalCorpus(root, corpus, query)).toThrow('math_search_invalid_query');
  });

  it('exposes lookup through the CLI and rejects a changed corpus identity', async () => {
    const corpus = path.join(root, 'corpus.json');
    fs.writeFileSync(corpus, JSON.stringify(await createMathRetrievalCorpus(root, ['mathlib'])));
    const args = [path.resolve('bin/math.ts'), 'search-lean', '--workspace', root, '--corpus', corpus,
      '--query', 'exists_lt_nsmul', '--sha256', mathDigest(fs.readFileSync(corpus))];
    const result = spawnSync('bun', args, { encoding: 'utf8', timeout: 10_000, maxBuffer: 32_000 });
    expect(result.status).toBe(0);
    expect(JSON.parse(result.stdout).results[0]).toMatchObject({ name: 'exists_lt_nsmul',
      qualifiedName: 'Order.exists_lt_nsmul', sourceLine: 3 });
    const batch = spawnSync('bun', [...args, '--query', 'Order.helper'], { encoding: 'utf8', timeout: 10_000, maxBuffer: 32_000 });
    expect(batch.status).toBe(0);
    expect(JSON.parse(batch.stdout).queries.map((query: { query: string }) => query.query)).toEqual(['exists_lt_nsmul', 'Order.helper']);
    const goal = 'a b : Nat\n⊢ ∃ n : Nat, a < n * b';
    const ranked = spawnSync('bun', [...args, '--goal', goal], { encoding: 'utf8', timeout: 10_000, maxBuffer: 32_000 });
    expect(ranked.status).toBe(0);
    expect(JSON.parse(ranked.stdout)).toEqual(searchMathRetrievalCorpus(root, JSON.parse(fs.readFileSync(corpus, 'utf8')), 'exists_lt_nsmul', 15, goal));
    fs.appendFileSync(corpus, '\n');
    const changed = spawnSync('bun', args, { encoding: 'utf8', timeout: 10_000, maxBuffer: 32_000 });
    expect(changed.status).toBe(1);
    expect(changed.stdout).toBe('');
    expect(changed.stderr).toContain('math_corpus_identity_changed');
  });
});
