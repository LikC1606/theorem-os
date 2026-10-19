import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, describe, expect, it } from 'vitest';
import { buildTheoremKnowledge, getKnowledgeTheorem, readTheoremKnowledge, searchTheoremKnowledge,
  knowledgeDeclaration, locateKnowledgeDeclaration, validateTheoremKnowledge, writeTheoremKnowledge,
  type KnowledgeCandidate } from '../src/solver/theoremKnowledge';

const roots: string[] = [];
afterEach(() => { for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });
const directory = () => {
  const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'theorem-knowledge-'))); roots.push(root); return root;
};
function candidate(overrides: Partial<KnowledgeCandidate> = {}): KnowledgeCandidate {
  return { name: 'Saved.density_bound', file: 'Submission.lean', type: 'forall (n : Nat), n = n',
    typeKind: 'closed-task-type', kind: 'lemma', description: 'Density estimate for the finite set consumer',
    premises: ['Retain the finite ambient set'], dependencies: { statement: [], proof: [], tasks: [], coverage: 'unavailable' },
    files: { 'Submission.lean': 'namespace Saved\nvariable (n : Nat)\nlemma density_bound : n = n := by rfl\nend Saved\n',
      'lean-toolchain': 'leanprover/lean4:v4.31.0\n' },
    provenance: { kind: 'solver-check', problemId: 'density', source: '/archived/state.json', sourceDigest: 'a'.repeat(64),
      runId: 'historical', environmentDigest: 'env-1', sourceCommit: 'source-commit', checkedCommit: 'projection-commit',
      receiptIds: ['historical-only'] }, ...overrides };
}

describe('callable theorem knowledge', () => {
  it('prefers exact qualified declarations over colliding raw names and only uses unique aliases', () => {
    const source = 'lemma shared : True := by trivial\nnamespace Nested\nlemma shared : False → False := by exact id\nend Nested\n';
    expect(knowledgeDeclaration(source, 'shared')).toBe('lemma shared : True := by trivial\n');
    expect(knowledgeDeclaration(source, '_root_.shared')).toBe('lemma shared : True := by trivial\n');
    expect(locateKnowledgeDeclaration(source, 'Nested.shared')).toMatchObject({ qualifiedName: 'Nested.shared',
      namespace: 'Nested', kind: 'theorem', declarationType: 'shared : False → False' });
    const ambiguous = 'namespace Left\nlemma shared : True := by trivial\nend Left\nnamespace Right\nlemma shared : True := by trivial\nend Right\n';
    expect(() => knowledgeDeclaration(ambiguous, 'shared')).toThrow('missing_or_ambiguous');
    expect(() => knowledgeDeclaration(ambiguous, '_root_.shared')).toThrow('missing_or_ambiguous');
    const colliding = 'namespace Other\nlemma Nested.shared : False → False := by exact id\nend Other\nnamespace Nested\nlemma shared : True := by trivial\nend Nested\n';
    expect(knowledgeDeclaration(colliding, 'Nested.shared')).toBe('lemma shared : True := by trivial\n');
  });

  it('retains both a root theorem and its namespaced namesake in a catalog', () => {
    const files = { 'Submission.lean': 'lemma shared : True := by trivial\nnamespace Nested\nlemma shared : False → False := by exact id\nend Nested\n' };
    const base = buildTheoremKnowledge([candidate({ name: 'shared', type: 'True', files }),
      candidate({ name: 'Nested.shared', type: 'False → False', files })]);
    expect(validateTheoremKnowledge(base).entries).toHaveLength(2);
    for (const item of base.entries) expect(getKnowledgeTheorem(base, item.id).type).toBe(item.type);
  });

  it('merges exact versions idempotently, retaining distinct source and environment versions', () => {
    const first = candidate();
    const otherOrigin = candidate({ provenance: { ...first.provenance, runId: 'second-run' } });
    const changedEnvironment = candidate({ provenance: { ...first.provenance, environmentDigest: 'env-2' } });
    const changedProof = candidate({ files: { ...first.files,
      'Submission.lean': first.files['Submission.lean'].replace('by rfl', 'by exact Eq.refl n') } });
    const base = buildTheoremKnowledge([first, first, otherOrigin, changedEnvironment, changedProof]);
    expect(base.entries).toHaveLength(3);
    expect(base.entries.find(item => item.provenance.length === 2)?.provenance.map(item => item.runId).sort())
      .toEqual(['historical', 'second-run']);
    expect(Object.keys(base.sources)).toHaveLength(3);
    expect(buildTheoremKnowledge([first, changedEnvironment], base)).toEqual(base);
  });

  it('returns exact types and complete source context only on demand, with historical evidence', () => {
    const exact = 'forall (n : Nat), ' + 'True -> '.repeat(200) + 'n = n';
    const input = candidate({ type: exact }), base = buildTheoremKnowledge([input]);
    const result = searchTheoremKnowledge(base, 'density', { limit: 1, goal: 'n : Nat' });
    expect(result).toMatchObject({ total: 1, evidence: 'recorded-not-replayed', requiresFreshCheck: true });
    expect(result.hits[0]).toMatchObject({ name: input.name, typeTruncated: true });
    expect(JSON.stringify(result)).not.toContain('by rfl');
    const saved = getKnowledgeTheorem(base, result.hits[0]!.id, 'Submission.lean');
    expect(saved.type).toBe(exact);
    expect(saved.premises).toEqual(input.premises);
    expect(saved.source?.text).toBe(input.files['Submission.lean']);
    expect(saved.provenance[0]).toMatchObject({ sourceCommit: 'source-commit', checkedCommit: 'projection-commit' });
    expect(saved.requiresFreshCheck).toBe(true);
  });

  it('searches names, types and prerequisites without treating goal overlap as a keyword hit', () => {
    const base = buildTheoremKnowledge([candidate(), candidate({ name: 'Other.spectral_norm',
      type: 'forall (x : Real), x = x', description: 'Spectral estimate',
      files: { 'Submission.lean': 'namespace Other\nlemma spectral_norm (x : Real) : x = x := by rfl\nend Other\n' },
      provenance: { ...candidate().provenance, problemId: 'spectral' } })]);
    expect(searchTheoremKnowledge(base, 'Other.spectral_norm').hits[0]?.name).toBe('Other.spectral_norm');
    expect(searchTheoremKnowledge(base, 'density', { problemId: 'spectral' }).total).toBe(0);
    expect(searchTheoremKnowledge(base, 'nonexistent', { goal: 'forall (n : Nat), n = n' }).total).toBe(0);
    expect(searchTheoremKnowledge(base, 'Real').hits[0]?.name).toBe('Other.spectral_norm');
    expect(() => searchTheoremKnowledge(base, 'density', { limit: 33 })).toThrow('invalid_query');
    expect(() => searchTheoremKnowledge(base, 'density', { goal: 'x'.repeat(16001) })).toThrow('invalid_query');
  });

  it('keeps contextual versions retrievable without letting one declaration fill the search page', () => {
    const first = candidate();
    const versions = Array.from({ length: 12 }, (_, index) => candidate({ files: {
      ...first.files, 'Submission.lean': `-- unrelated context version ${index}\n` + first.files['Submission.lean'],
    } }));
    const other = candidate({ name: 'Saved.density_nonnegative',
      files: { ...first.files, 'Submission.lean': first.files['Submission.lean'].replace('density_bound', 'density_nonnegative') } });
    const base = buildTheoremKnowledge([...versions, other]), result = searchTheoremKnowledge(base, 'density');
    expect(result).toMatchObject({ total: 2, totalVersions: 13 });
    expect(result.hits.map(hit => hit.name).sort()).toEqual(['Saved.density_bound', 'Saved.density_nonnegative']);
    const grouped = result.hits.find(hit => hit.name === 'Saved.density_bound')!;
    expect(grouped).toMatchObject({ versionCount: 12, versionsTruncated: true });
    const saved = getKnowledgeTheorem(base, grouped.id);
    expect(saved.relatedVersions).toHaveLength(12);
    for (const version of saved.relatedVersions) expect(getKnowledgeTheorem(base, version.id).name).toBe('Saved.density_bound');
  });

  it('rejects tampered source, context, declaration, type and pinned identity', () => {
    const base = buildTheoremKnowledge([candidate()]);
    for (const mutate of [
      (changed: typeof base) => { const key = Object.keys(changed.sources)[0]!; changed.sources[key] += '\n'; },
      (changed: typeof base) => { changed.contexts[changed.entries[0]!.contextDigest]['Submission.lean'] = 'b'.repeat(64); },
      (changed: typeof base) => { changed.entries[0]!.declaration = 'lemma forged : False := by sorry'; },
      (changed: typeof base) => { changed.entries[0]!.type = 'False'; },
    ]) {
      const changed = structuredClone(base); mutate(changed);
      expect(() => validateTheoremKnowledge(changed)).toThrow();
    }
    const file = path.join(directory(), 'knowledge.json'), written = writeTheoremKnowledge(file, base);
    expect(readTheoremKnowledge(file, written.sha256).base).toEqual(base);
    expect(() => readTheoremKnowledge(file, '0'.repeat(64))).toThrow('identity_changed');
    expect(() => writeTheoremKnowledge(file, base)).toThrow();
    expect(fs.statSync(file).mode & 0o222).toBe(0);
  });

  it.each(['Solution.lean', '../Submission.lean', '/Submission.lean', '.git/config', 'nested/Solution.lean',
    'environment.json', 'nested\\Submission.lean', '.lake/proof.lean'])(
    'refuses forbidden archived file %s before storing it', file => {
      expect(() => buildTheoremKnowledge([candidate({ files: { ...candidate().files, [file]: 'forbidden' } })]))
        .toThrow('forbidden_source');
    });

  it('rejects symlinked catalogs and missing source lookups', () => {
    const base = buildTheoremKnowledge([candidate()]), root = directory(), file = path.join(root, 'knowledge.json');
    writeTheoremKnowledge(file, base);
    const link = path.join(root, 'linked.json'); fs.symlinkSync(file, link);
    expect(() => readTheoremKnowledge(link)).toThrow('math_path_invalid');
    expect(() => getKnowledgeTheorem(base, 'missing')).toThrow('theorem_not_found');
    expect(() => getKnowledgeTheorem(base, base.entries[0]!.id, '../Submission.lean')).toThrow('source_not_found');
  });
});
