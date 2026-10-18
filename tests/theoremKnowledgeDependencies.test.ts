import { describe, expect, it } from 'vitest';
import { buildTheoremKnowledge, type KnowledgeCandidate } from '../src/solver/theoremKnowledge';
import { getKnowledgeDependencies } from '../src/solver/theoremKnowledgeDependencies';

const files = { 'Submission.lean': 'namespace Saved\nlemma a : True := by trivial\nlemma b : True := by trivial\nend Saved\n',
  'Challenge.lean': 'def fixedNumber := 1\n' };
const candidate = (name: string, overrides: Partial<KnowledgeCandidate> = {}): KnowledgeCandidate => ({
  name: `Saved.${name}`, file: 'Submission.lean', type: 'True', typeKind: 'closed-task-type', kind: 'lemma',
  description: 'Historical proof', premises: [], files,
  dependencies: { statement: [], proof: [], tasks: [], coverage: 'recorded' },
  provenance: { kind: 'solver-check', problemId: 'old', source: '/archive/state.json', sourceDigest: 'a'.repeat(64),
    environmentDigest: 'old-env', receiptIds: ['old-receipt'] }, ...overrides,
});
const dependsOn = (name: string) => ({ statement: [], proof: [{ file: 'Submission.lean', name: `Saved.${name}` }],
  tasks: [], coverage: 'recorded' as const });

describe('knowledge dependency lookup', () => {
  it('follows recorded cycles once and exposes source-backed definitions and missing context', () => {
    const base = buildTheoremKnowledge([candidate('a', { dependencies: {
      ...dependsOn('b'), statement: [{ file: 'Challenge.lean', name: 'fixedNumber' }],
      proof: [...dependsOn('b').proof, { file: 'Missing.lean', name: 'unknown' }],
    } }), candidate('b', { dependencies: dependsOn('a') })]);
    const root = base.entries.find(item => item.name === 'Saved.a')!;
    const result = getKnowledgeDependencies(base, root.id);
    expect(result.nodes.map(node => node.name)).toEqual(['Saved.a', 'Saved.b']);
    expect(result.references.map(ref => ref.resolution)).toEqual(['source-available', 'indexed', 'missing-source', 'indexed']);
    expect(result.references[0]!.source).toEqual({ theoremId: root.id, file: 'Challenge.lean',
      sha256: base.contexts[root.contextDigest]!['Challenge.lean'] });
    expect(result).toMatchObject({ requiresFreshCheck: true, hasUnavailableDependencies: false });
  });

  it('never joins names from a different source context or environment', () => {
    const base = buildTheoremKnowledge([candidate('a', { dependencies: dependsOn('b') }),
      candidate('b', { files: { ...files, 'Challenge.lean': 'def fixedNumber := 2\n' } }),
      candidate('b', { provenance: { ...candidate('b').provenance, environmentDigest: 'new-env' } })]);
    const result = getKnowledgeDependencies(base, base.entries.find(item => item.name === 'Saved.a')!.id);
    expect(result.nodes).toHaveLength(1);
    expect(result.references[0]).toMatchObject({ resolution: 'source-available', targetIds: [] });
  });

  it('reports ambiguous metadata versions and unavailable dependency coverage explicitly', () => {
    const base = buildTheoremKnowledge([candidate('a', { dependencies: dependsOn('b') }), candidate('b'),
      candidate('b', { premises: ['A historical premise'] })]);
    const result = getKnowledgeDependencies(base, base.entries.find(item => item.name === 'Saved.a')!.id);
    expect(result.references[0]).toMatchObject({ resolution: 'ambiguous' });
    expect(result.references[0]!.targetIds).toHaveLength(2);
    expect(result.nodes).toHaveLength(1);
    const unknown = buildTheoremKnowledge([candidate('a', { dependencies: { ...dependsOn('b'), coverage: 'unavailable' } })]);
    expect(getKnowledgeDependencies(unknown, unknown.entries[0]!.id).hasUnavailableDependencies).toBe(true);
  });

  it('bounds graph output and marks omitted references and nodes', () => {
    const base = buildTheoremKnowledge([candidate('a', { dependencies: {
      ...dependsOn('b'), statement: dependsOn('b').proof,
    } }), candidate('b', { dependencies: dependsOn('a') })]);
    const id = base.entries.find(item => item.name === 'Saved.a')!.id;
    expect(getKnowledgeDependencies(base, id, { depth: 0 })).toMatchObject({ nodes: [{ id }], references: [], truncated: { depth: true } });
    expect(getKnowledgeDependencies(base, id, { maxNodes: 1, maxReferences: 1 }))
      .toMatchObject({ truncated: { nodes: true, references: true } });
    expect(() => getKnowledgeDependencies(base, id, { depth: 9 })).toThrow('invalid_dependency_options');
    expect(() => getKnowledgeDependencies(base, 'missing')).toThrow('theorem_not_found');
  });

  it('can traverse metadata without reading archived source text', () => {
    const base = buildTheoremKnowledge([candidate('a', { dependencies: dependsOn('b') }), candidate('b')]);
    for (const hash of Object.keys(base.sources)) Object.defineProperty(base.sources, hash, { get: () => { throw new Error('unexpected_source_read'); } });
    expect(getKnowledgeDependencies(base, base.entries.find(item => item.name === 'Saved.a')!.id).nodes).toHaveLength(2);
  });
});
