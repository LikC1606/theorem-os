import { describe, expect, it } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import type { TheoremKnowledgeBase, TheoremKnowledgeEntry } from '../src/solver/theoremKnowledge';
import { knowledgeSearchGroup, knowledgeVersionSummary, searchTheoremKnowledge, searchTheoremKnowledgeBatch } from '../src/solver/theoremKnowledgeSearch';

const normType = '∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ‖χ.rootNumber‖ = 1';
const name = 'Submission.Helpers.paper_root_number_norm';
function entry(theoremName = name, type = normType, extra: Partial<TheoremKnowledgeEntry> = {}): TheoremKnowledgeEntry {
  return { id: mathDigest(theoremName + type), contextDigest: mathDigest('context'), name: theoremName,
    file: 'Submission/Helpers.lean', type, typeKind: 'closed-task-type', kind: 'lemma', description: '', premises: [],
    declaration: `theorem ${theoremName.split('.').at(-1)} : ${type} := by exact saved_proof\n`,
    dependencies: { statement: [], proof: [], tasks: [], coverage: 'unavailable' },
    provenance: [{ kind: 'solver-check', problemId: 'annals_dirichlet_weyl_bound', source: '/archive/state.json',
      sourceDigest: mathDigest('state'), receiptIds: ['historical-receipt'] }], ...extra };
}
const base = (...entries: TheoremKnowledgeEntry[]): Pick<TheoremKnowledgeBase, 'entries' | 'evidence'> =>
  ({ entries, evidence: 'recorded-not-replayed' });

describe('theorem knowledge retrieval', () => {
  it('finds an exact Lean goal without inventing primary keywords', () => {
    const desired = entry(), unrelated = entry('Submission.Helpers.primitive_parameter', '∀ n : ℕ, n = n');
    const result = searchTheoremKnowledge(base(unrelated, desired), '', { goal: normType });
    expect(result.hits[0]!.id).toBe(desired.id);
    expect(result).toMatchObject({ evidence: 'recorded-not-replayed', requiresFreshCheck: true,
      preferenceEvidence: 'recorded-metadata-not-applicability' });
  });

  it('treats unicode types and quantifiers as the corresponding Lean identifiers', () => {
    const desired = entry('Submission.Helpers.real_reflexivity', '∀ (x : ℝ), x = x');
    const distractor = entry('Submission.Helpers.complex_reflexivity', '∀ (z : ℂ), z = z');
    const result = searchTheoremKnowledge(base(distractor, desired), '', { goal: 'forall (x : Real), x = x' });
    expect(result.hits[0]!.id).toBe(desired.id);
    expect(searchTheoremKnowledge(base(distractor, desired), 'Real').hits.map(hit => hit.id)).toEqual([desired.id]);
  });

  it('keeps extended real notations distinct while matching their Lean type names', () => {
    const real = entry('Saved.real_equality', '∀ (x : Real), x = x'),
      nonnegative = entry('Saved.nonnegative_equality', '∀ (x : NNReal), x = x'),
      extended = entry('Saved.extended_equality', '∀ (x : ENNReal), x = x');
    const catalog = base(real, nonnegative, extended);
    for (const [notation, desired] of [['ℝ', real], ['ℝ≥0', nonnegative], ['ℝ≥0∞', extended]] as const)
      expect(searchTheoremKnowledge(catalog, '', { goal: `∀ (x : ${notation}), x = x` }).hits[0]!.id).toBe(desired.id);
  });

  it('ignores nested comments and string literals in search keywords', () => {
    const catalog = base(entry(), entry('Saved.unrelated_token', 'True'));
    expect(searchTheoremKnowledge(catalog, 'root /- unrelated /- token -/ -/ "unrelated token" norm -- unrelated token'))
      .toEqual(searchTheoremKnowledge(catalog, 'root norm'));
  });

  it('does not admit archive boilerplate as evidence for a natural-language request', () => {
    const desired = entry('Saved.pushforward_volume', 'InverseJacobianDensity'),
      unrelated = entry('Saved.unrelated', 'True', { description: 'Historical sources retain their recorded result and its receipt.' });
    const result = searchTheoremKnowledge(base(unrelated, desired), 'I need the pushforward volume formula for its inverse');
    expect(result.hits.map(hit => hit.id)).toEqual([desired.id]);
  });

  it('still locates explicit identifiers that also happen to be prose function words', () => {
    const desired = entry('Saved.its', 'True');
    expect(searchTheoremKnowledge(base(desired), 'its').hits[0]!.id).toBe(desired.id);
    expect(searchTheoremKnowledge(base(desired), 'Saved.its').hits[0]!.id).toBe(desired.id);
  });

  it('keeps negation and numeric constraints as keyword evidence', () => {
    const desired = entry('Saved.no_two_orthogonal_vectors', 'True'), positive = entry('Saved.two_orthogonal_vectors', 'True');
    const result = searchTheoremKnowledge(base(positive, desired), 'no two orthogonal vectors');
    expect(result.hits[0]!.id).toBe(desired.id);
    expect(result.hits[0]!.matched).toContain('no');
    expect(searchTheoremKnowledge(base(entry('Saved.norm_two', 'Norm = 2')), 'norm 2').hits[0]!.matched).toContain('2');
  });

  it('finds Lean partial derivatives from their natural-language terminology', () => {
    const desired = entry('Saved.pderiv_commute', 'MvPolynomial.pderiv i (MvPolynomial.pderiv j f) = MvPolynomial.pderiv j (MvPolynomial.pderiv i f)'),
      ordinary = entry('Saved.derivative_bound', 'DerivativeBound');
    const catalog = base(ordinary, desired);
    for (const query of ['partial derivative commute', 'mixed partial derivatives commute']) {
      const result = searchTheoremKnowledge(catalog, query);
      expect(result.hits[0]).toMatchObject({ id: desired.id, typePreview: desired.type });
      expect(result).toMatchObject({ evidence: 'recorded-not-replayed', requiresFreshCheck: true });
    }
    expect(searchTheoremKnowledge(base(entry('Saved.constructor', 'True')), 'constructor').hits[0]!.name).toBe('Saved.constructor');
  });

  it('does not replace an explicitly missing keyword with a matching goal', () => {
    expect(searchTheoremKnowledge(base(entry()), 'unavailableproofkeyword', { goal: normType }).hits).toEqual([]);
  });

  it('does not admit a goal-only hit from an unrelated local context', () => {
    const unrelated = entry('Submission.Helpers.natural_reflexivity', '∀ n : Nat, n = n');
    expect(searchTheoremKnowledge(base(unrelated), '', { goal: 'n : Nat\n⊢ UnavailableTarget n' }).hits).toEqual([]);
  });

  it('requires exact shape when the target has no meaningful lexical terms', () => {
    const desired = entry('Submission.Helpers.equality', 'a = b'), other = entry('Submission.Helpers.other_equality', 'a = a');
    const result = searchTheoremKnowledge(base(other, desired), '', { goal: 'n : Nat\n⊢ a = b' });
    expect(result.hits.map(hit => hit.id)).toEqual([desired.id]);
  });

  it('admits a supported renamed goal even when the bound variables were its only lexical terms', () => {
    const desired = entry('Submission.Helpers.proposition_reflexivity', '∀ (P : Prop), P = P'),
      opposite = entry('Submission.Helpers.proposition_negation', '∀ (P : Prop), ¬ P = P');
    expect(searchTheoremKnowledge(base(opposite, desired), '', { goal: '∀ (Q : Prop), Q = Q' }).hits.map(hit => hit.id))
      .toEqual([desired.id]);
    expect(searchTheoremKnowledge(base(desired), '', { goal: 'unrelated : Nat\n⊢ free = free' }).total).toBe(0);
  });

  it.each([name, 'paper_root_number_norm', 'Helpers.paper_root_number_norm', `_root_.${name}`])
  ('ranks the exact full or tail identifier %s ahead of namespace noise', query => {
    const desired = entry(), distractor = entry('Submission.Helpers.unrelated_result', 'True');
    const result = searchTheoremKnowledge(base(distractor, desired), query);
    expect(result.hits[0]!.id).toBe(desired.id); expect(result.total).toBe(1);
  });

  it('does not expose every declaration for a common namespace alone', () => {
    expect(searchTheoremKnowledge(base(entry(), entry('Submission.Helpers.other', 'True')), 'Submission.Helpers').hits).toEqual([]);
  });

  it('uses phrase coverage and actual declaration fields over repeated descriptive words', () => {
    const desired = entry('Submission.Helpers.variance_recoloring', 'MeanSquareAssumption → Recoloring');
    const distractor = entry('Submission.Helpers.mean_only', 'True',
      { description: 'mean square recoloring variance '.repeat(100) });
    const descriptionOnly = entry('Submission.Helpers.unrelated', 'True', { description: 'mean square recoloring variance' });
    expect(searchTheoremKnowledge(base(distractor, descriptionOnly, desired), 'mean square recoloring variance').hits[0]!.id).toBe(desired.id);
  });

  it('recognizes the exact character sum goal instead of a nearby norm bound', () => {
    const sum = '∀ (p : ℕ) [Fact p.Prime] (χ ψ : DirichletCharacter ℂ (p ^ 2)), ' +
      'χ.IsPrimitive → ¬ ψ.IsPrimitive → (∑ t : ZMod (p ^ 2), χ t * ψ t) = 0';
    const desired = entry('Submission.Helpers.g_prime_square_eq_zero_of_imprimitive', sum);
    const bound = entry('Submission.Helpers.g_prime_square_bound', sum.replace('¬ ψ.IsPrimitive', 'ψ.IsPrimitive').replace('= 0', '≤ 1'));
    const result = searchTheoremKnowledge(base(bound, desired), 'DirichletCharacter', { goal: sum });
    expect(result.hits[0]!.id).toBe(desired.id);
  });

  it('uses renamed typed binders as a ranking hint while preserving opposite propositions', () => {
    const original = '∀ (p : ℕ) [Fact p.Prime] (χ ψ : DirichletCharacter ℂ (p ^ 2)), ' +
      'χ.IsPrimitive → ¬ ψ.IsPrimitive → (∑ t : ZMod (p ^ 2), ∑ u : ZMod (p ^ 2), χ t * ψ u) = 0';
    const renamed = original.replace(/[\p{L}_][\p{L}\p{M}\p{N}_']*/gu, word =>
      ({ p: 'primeModulus', χ: 'firstCharacter', ψ: 'secondCharacter', t: 'outerIndex', u: 'innerIndex' })[word] ?? word);
    const desired = entry('Submission.Helpers.character_sum_zero', original),
      opposite = entry('Submission.Helpers.character_sum_primitive', original.replace('¬ ψ.IsPrimitive', 'ψ.IsPrimitive'));
    const result = searchTheoremKnowledge(base(opposite, desired), 'DirichletCharacter', { goal: renamed });
    expect(result.hits[0]!.id).toBe(desired.id);
    expect(result.hits[0]!.score - result.hits[1]!.score).toBeGreaterThan(1000);
    expect(searchTheoremKnowledge(base(desired), 'absentproofsymbolzz', { goal: renamed }).total).toBe(0);
  });

  it('selects the requested contextual version while exposing all historical alternatives', () => {
    const oldEnv = mathDigest('old environment'), currentEnv = mathDigest('current environment'), receipt = mathDigest('current problem');
    const old = entry(name, normType, { id: '1'.repeat(64), environmentDigest: oldEnv });
    old.provenance = [{ ...old.provenance[0]!, environmentDigest: oldEnv, problemReceiptDigest: mathDigest('old problem') }];
    const current = entry(name, normType, { id: '2'.repeat(64), contextDigest: mathDigest('new context'), environmentDigest: currentEnv });
    current.provenance = [{ ...current.provenance[0]!, environmentDigest: currentEnv, problemReceiptDigest: receipt }];
    const unknown = entry(name, normType, { id: '3'.repeat(64), contextDigest: mathDigest('unknown context') });
    const catalog = base(unknown, current, old), preferred = searchTheoremKnowledge(catalog, name,
      { environmentDigest: currentEnv, problemReceiptDigest: receipt });
    expect(searchTheoremKnowledge(catalog, name).hits[0]!.id).toBe(old.id);
    expect(preferred.hits[0]).toMatchObject({ id: current.id, versionCount: 3, environmentMatch: 'match', problemReceiptMatch: 'match' });
    expect(preferred.hits[0]!.versions.map(version => [version.id, version.environmentMatch, version.problemReceiptMatch]))
      .toEqual([[current.id, 'match', 'match'], [unknown.id, 'unknown', 'unknown'], [old.id, 'different', 'different']]);
    expect(knowledgeVersionSummary(old).environmentMatch).toBe('not-requested');
  });

  it('keeps changed statements and changed proof bodies as distinct groups', () => {
    const original = entry(), changedType = entry(name, 'True'), changedProof = entry(name, normType,
      { id: mathDigest('changed proof'), declaration: 'theorem paper_root_number_norm := by exact other_saved_proof\n' });
    expect(new Set([original, changedType, changedProof].map(knowledgeSearchGroup)).size).toBe(3);
    expect(searchTheoremKnowledge(base(original, changedType, changedProof), name).total).toBe(3);
  });

  it('exposes different premise and dependency metadata for versions of one declaration', () => {
    const original = entry(), conditional = entry(name, normType, { id: mathDigest('conditional-version'),
      premises: ['local-condition'], dependencies: { statement: [{ file: 'Submission/Helpers.lean', name: 'condition' }],
        proof: [], tasks: [], coverage: 'recorded' } });
    const result = searchTheoremKnowledge(base(original, conditional), name);
    expect(result.total).toBe(1);
    expect(result.hits[0]!.versionCount).toBe(2);
    expect(result.hits[0]!.versions.map(version => version.premisesCount).sort()).toEqual([0, 1]);
    expect(new Set(result.hits[0]!.versions.map(version => version.premisesDigest)).size).toBe(2);
    expect(new Set(result.hits[0]!.versions.map(version => version.dependenciesDigest)).size).toBe(2);
    expect(knowledgeVersionSummary(original)).toMatchObject({ premisesCount: 0,
      premisesDigest: mathDigest('[]') });
  });

  it('filters problem identities before selecting contextual versions', () => {
    const desired = entry(), other = entry(name, normType, { id: mathDigest('other problem') });
    other.provenance = [{ ...other.provenance[0]!, problemId: 'other_problem' }];
    const result = searchTheoremKnowledge(base(other, desired), name, { problemId: 'annals_dirichlet_weyl_bound' });
    expect(result.totalVersions).toBe(1); expect(result.hits[0]!.versions.map(version => version.id)).toEqual([desired.id]);
  });

  it('bounds previews and version lists while preserving every entry identity', () => {
    const original = entry(name, `True ${' '.repeat(1000)}`, { description: 'saved result '.repeat(100) });
    const versions = Array.from({ length: 10 }, (_, index) => ({ ...original, id: mathDigest(String(index)), contextDigest: mathDigest(`context-${index}`) }));
    const result = searchTheoremKnowledge(base(...versions), name);
    expect(result).toMatchObject({ total: 1, totalVersions: 10 });
    expect(result.hits[0]).toMatchObject({ typeTruncated: true, versionsTruncated: true, versionCount: 10 });
    expect(result.hits[0]!.versions).toHaveLength(8); expect(result.hits[0]!.typePreview.length).toBe(800);
    expect(result.hits[0]!.description.length).toBe(500);
    expect(base(...versions).entries).toHaveLength(10);
  });

  it('ranks deterministically regardless of input order', () => {
    const a = entry('Submission.Helpers.root_norm_one', 'True'), b = entry('Submission.Helpers.root_norm_two', 'True');
    expect(searchTheoremKnowledge(base(a, b), 'root norm')).toEqual(searchTheoremKnowledge(base(b, a), 'root norm'));
  });

  it.each([
    { query: '', options: {} }, { query: 'a'.repeat(4001), options: {} },
    { query: 'norm', options: { goal: 'a'.repeat(16001) } }, { query: 'norm', options: { limit: 0 } },
    { query: 'norm', options: { limit: 33 } }, { query: 'norm', options: { environmentDigest: '' } },
  ])('rejects invalid input boundaries', ({ query, options }) => {
    expect(() => searchTheoremKnowledge(base(entry()), query, options)).toThrow('math_knowledge_invalid_query');
  });
});

describe('batched theorem knowledge retrieval', () => {
  it('preserves input order and independent-search results', () => {
    const catalog = base(entry(), entry('Submission.Helpers.natural_reflexivity', '∀ n : Nat, n = n'));
    const queries = Object.freeze(['natural', 'root number norm', 'absentproofsymbolzz', 'root number norm']);
    expect(searchTheoremKnowledgeBatch(catalog, queries, { limit: 2 }))
      .toEqual(queries.map(query => searchTheoremKnowledge(catalog, query, { limit: 2 })));
    expect(queries[0]).toBe('natural');
  });

  it('prepares each declaration once per batch and prepares it again for a later call', () => {
    const item = entry(), declaration = item.declaration;
    let reads = 0;
    Object.defineProperty(item, 'declaration', { get: () => { reads++; return declaration; } });
    const catalog = base(item);
    searchTheoremKnowledgeBatch(catalog, ['root', 'number', 'norm', 'root']);
    expect(reads).toBe(1);
    searchTheoremKnowledgeBatch(catalog, ['root']);
    expect(reads).toBe(2);
  });

  it('does not share mutable result objects for repeated queries', () => {
    const results = searchTheoremKnowledgeBatch(base(entry()), ['root', 'root']);
    results[0]!.hits[0]!.description = 'changed by caller';
    expect(results[1]!.hits[0]!.description).toBe('');
    expect(results[0]!.hits[0]!.versions).not.toBe(results[1]!.hits[0]!.versions);
  });

  it('observes changed metadata on the next independent call', () => {
    const item = entry('Submission.Helpers.result', 'obsoletekind'), catalog = base(item);
    expect(searchTheoremKnowledgeBatch(catalog, ['obsoletekind'])[0]!.total).toBe(1);
    item.type = 'updatedkind';
    expect(searchTheoremKnowledgeBatch(catalog, ['obsoletekind', 'updatedkind']).map(result => result.total)).toEqual([0, 1]);
  });

  it('counts token frequency by distinct declaration groups rather than contextual versions', () => {
    const item = entry(), unrelated = entry('Submission.Helpers.other_norm', 'True');
    const duplicate = { ...item, id: mathDigest('new version'), contextDigest: mathDigest('new context') };
    const before = searchTheoremKnowledge(base(item, unrelated), 'root norm'),
      after = searchTheoremKnowledgeBatch(base(item, duplicate, unrelated), ['root norm'])[0]!;
    expect(after.hits.map(hit => [hit.name, hit.score])).toEqual(before.hits.map(hit => [hit.name, hit.score]));
    expect(after.totalVersions).toBe(before.totalVersions + 1);
  });

  it('shares goal and problem preferences without widening the problem filter', () => {
    const desired = entry(), foreign = entry('Other.root_number_norm', normType);
    foreign.provenance = [{ ...foreign.provenance[0]!, problemId: 'foreign' }];
    const result = searchTheoremKnowledgeBatch(base(foreign, desired), ['', 'root number norm'],
      { goal: normType, problemId: 'annals_dirichlet_weyl_bound' });
    expect(result.every(search => search.hits[0]!.id === desired.id)).toBe(true);
    expect(result.every(search => search.totalVersions === 1)).toBe(true);
  });

  it.each([{ queries: [] }, { queries: Array(9).fill('root') }, { queries: ['root', ''] },
    { queries: ['root', 'a'.repeat(4001)] }])
  ('rejects an invalid batch before preparing entries', ({ queries }) => {
    const item = entry();
    Object.defineProperty(item, 'declaration', { get: () => { throw new Error('must not prepare'); } });
    expect(() => searchTheoremKnowledgeBatch(base(item), queries)).toThrow('math_knowledge_invalid_query');
  });
});
