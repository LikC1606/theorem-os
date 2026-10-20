import { describe, expect, it } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { buildTheoremKnowledge, type KnowledgeCandidate, type TheoremKnowledgeBase } from '../src/solver/theoremKnowledge';
import { getKnowledgeConsumers, type KnowledgeConsumersOptions } from '../src/solver/theoremKnowledgeConsumers';
import { getKnowledgeMetadata } from '../src/solver/theoremKnowledgeMetadata';
import { getKnowledgeSource } from '../src/solver/theoremKnowledgeSource';

const files = { 'Submission.lean': ['namespace Saved', 'lemma root : True := by trivial',
  'lemma first : True := by exact root', 'lemma second : True := by exact first', 'end Saved',
  'namespace Other', 'lemma root : True := by trivial', 'end Other', ''].join('\n'),
  'Alternate.lean': 'namespace Saved\nlemma root : True := by trivial\nend Saved\n' };
const origin = { kind: 'accepted-archive' as const, problemId: 'historical-fixture', source: '/archive/manifest.json',
  sourceDigest: 'a'.repeat(64), environmentDigest: 'historical-environment', receiptIds: ['historical-only'] };
const reference = { file: 'Submission.lean', name: 'Saved.root' };
const dependencies = (statement = false, proof = true) => ({ statement: statement ? [reference] : [],
  proof: proof ? [reference] : [], tasks: [], coverage: 'recorded' as const });
const candidate = (name: string, overrides: Partial<KnowledgeCandidate> = {}): KnowledgeCandidate => ({
  name: `Saved.${name}`, file: 'Submission.lean', type: 'True', typeKind: 'closed-task-type', kind: 'lemma',
  description: 'Historical declaration', premises: [], files,
  dependencies: { statement: [], proof: [], tasks: [], coverage: 'recorded' }, provenance: origin, ...overrides,
});
const rootId = (base: TheoremKnowledgeBase) => base.entries.find(item => item.name === 'Saved.root' && item.file === 'Submission.lean')!.id;
const measured = <T,>(packet: T, maxBytes: number): T => {
  expect(Buffer.byteLength(JSON.stringify(packet)) + 1).toBeLessThanOrEqual(maxBytes); return packet;
};

describe('bounded historical theorem consumers', () => {
  it('inverts exact recorded references and preserves both statement and proof uses', () => {
    const base = buildTheoremKnowledge([candidate('root'), candidate('first', { dependencies: dependencies(true, true),
      premises: ['Keep the original ambient assumptions'] })]);
    const result = getKnowledgeConsumers(base, rootId(base));
    expect(result).toMatchObject({ schema: 'theorem-os.theorem-knowledge-consumers.v1', evidence: 'recorded-not-replayed',
      requiresFreshCheck: true, referenceSemantics: 'local-transitive-closure', applicationArguments: 'not-recorded',
      use: 'historical-advisory', absence: 'not-evidence-of-no-consumers', environmentMatch: 'exact',
      coverage: { status: 'recorded', scopedEntries: 2, recordedEntries: 2, unavailableEntries: 0 },
      total: 1, offset: 0, truncated: false });
    const consumer = result.consumers[0]!;
    expect(consumer).toMatchObject({ uses: ['statement-use', 'proof-use'], referenceCoverage: 'recorded',
      typeKind: 'closed-task-type', fields: { name: { complete: true, value: 'Saved.first' },
        type: { complete: true, value: 'True', sha256: mathDigest('True') },
        premises: { complete: true, value: ['Keep the original ambient assumptions'] } }, elaborationCoverage: 'unknown' });
    expect(consumer.read.metadata).toEqual({ command: 'knowledge get', id: consumer.id, metadata: true });
    expect(consumer.context).toEqual({ digest: result.contextDigest, read: { field: 'files', startOffset: 0 } });
    expect(consumer.read.source).toEqual({ command: 'knowledge source', id: consumer.id, file: 'Submission.lean', name: 'Saved.first' });
    expect(getKnowledgeSource(base, consumer.id, consumer.read.source).text).toContain('by exact root');
    expect(result).not.toHaveProperty('officialAcceptance');
  });

  it('reports only existing closure edges rather than composing a new consumer relation', () => {
    const base = buildTheoremKnowledge([candidate('root'), candidate('first', { dependencies: dependencies() }),
      candidate('second', { dependencies: { ...dependencies(), proof: [{ file: 'Submission.lean', name: 'Saved.first' }] } })]);
    expect(getKnowledgeConsumers(base, rootId(base)).consumers.map(item => item.fields.name.value)).toEqual(['Saved.first']);
  });

  it('never joins an equal name across a different file, namespace, source context or environment', () => {
    const base = buildTheoremKnowledge([candidate('root'), candidate('first', { dependencies: dependencies() }),
      candidate('second', { dependencies: dependencies(), files: { ...files, 'Alternate.lean': files['Alternate.lean'] + '-- other context\n' } }),
      candidate('second', { dependencies: dependencies(), provenance: { ...origin, environmentDigest: 'different-environment' } }),
      candidate('second', { dependencies: { ...dependencies(), proof: [{ ...reference, file: 'Alternate.lean' }] } }),
      candidate('second', { dependencies: { ...dependencies(), proof: [{ ...reference, name: 'Other.root' }] } }),
      candidate('second', { dependencies: { ...dependencies(), proof: [{ ...reference, name: 'root' }] } })]);
    const result = getKnowledgeConsumers(base, rootId(base));
    expect(result.total).toBe(1); expect(result.consumers[0]!.fields.name.value).toBe('Saved.first');
  });

  it('does not infer an environment identity from two missing values or unrelated provenance', () => {
    const unknown = { ...origin, environmentDigest: undefined };
    const base = buildTheoremKnowledge([candidate('root', { provenance: unknown }),
      candidate('first', { provenance: unknown, dependencies: dependencies() })]);
    const result = getKnowledgeConsumers(base, rootId(base));
    expect(result).toMatchObject({ environmentMatch: 'unknown', coverage: { status: 'unknown', unknownEnvironmentEntries: 2 },
      consumers: [], total: 0, truncated: false });
    const known = buildTheoremKnowledge([candidate('root'), candidate('first', { provenance: unknown, dependencies: dependencies() })]);
    expect(getKnowledgeConsumers(known, rootId(known))).toMatchObject({ consumers: [], coverage: { status: 'unknown', unknownEnvironmentEntries: 1 } });
  });

  it('keeps missing coverage unknown while exposing any observed references', () => {
    const base = buildTheoremKnowledge([candidate('root'), candidate('first', { dependencies: { ...dependencies(), coverage: 'unavailable' } })]);
    expect(getKnowledgeConsumers(base, rootId(base))).toMatchObject({ total: 1,
      coverage: { status: 'unknown', unavailableEntries: 1 }, consumers: [{ referenceCoverage: 'unknown' }] });
    const empty = buildTheoremKnowledge([candidate('root', { dependencies: { ...dependencies(false, false), coverage: 'unavailable' } })]);
    expect(getKnowledgeConsumers(empty, rootId(empty))).toMatchObject({ total: 0, coverage: { status: 'unknown' },
      absence: 'not-evidence-of-no-consumers' });
  });

  it('retains distinct metadata views of the same exact consumer source', () => {
    const base = buildTheoremKnowledge([candidate('root'), candidate('first', { dependencies: dependencies() }),
      candidate('first', { dependencies: dependencies(), premises: ['An additional historical premise'] })]);
    const result = getKnowledgeConsumers(base, rootId(base));
    expect(result.total).toBe(2); expect(new Set(result.consumers.map(item => item.id)).size).toBe(2);
    expect(result.consumers.map(item => item.fields.name.value)).toEqual(['Saved.first', 'Saved.first']);
  });

  it('pages a deterministic bounded result without omitting consumers between pages', () => {
    const names = Array.from({ length: 19 }, (_, index) => `consumer_${String(index).padStart(2, '0')}`);
    const corpus = { 'Submission.lean': 'namespace Saved\nlemma root : True := by trivial\n' +
      names.map(name => `lemma ${name} : True := by exact root\n`).join('') + 'end Saved\n' };
    const base = buildTheoremKnowledge([candidate('root', { files: corpus }),
      ...names.map(name => candidate(name, { files: corpus, dependencies: dependencies() }))]);
    const found: string[] = [];
    let offset = 0, pages = 0;
    for (;;) {
      const page = measured(getKnowledgeConsumers(base, rootId(base), { offset, limit: 3, maxBytes: 6000 }), 6000);
      found.push(...page.consumers.map(item => item.id)); pages++;
      expect(page.consumers.length).toBeGreaterThan(0); expect(page.consumers.length).toBeLessThanOrEqual(3);
      if (!page.truncated) break;
      expect(page.nextOffset).toBeGreaterThan(offset); offset = page.nextOffset!;
      expect(pages).toBeLessThan(20);
    }
    expect(found).toHaveLength(19); expect(new Set(found).size).toBe(19); expect(pages).toBeGreaterThan(1);
    expect(getKnowledgeConsumers(base, rootId(base), { offset: 19 })).toMatchObject({ consumers: [], truncated: false, total: 19 });
    expect(() => getKnowledgeConsumers(base, rootId(base), { offset: 20 })).toThrow('consumers_position_invalid');
  });

  it('defers long types and premises without presenting a preview as the complete interface', () => {
    const type = 'forall (n : Nat), ' + 'True \u2192 '.repeat(1800) + 'n = n /- \u{1f642}\u96ea"\\\t -/';
    const premises = ['\u{1f642}\u96ea"\\\t'.repeat(900), 'Retain this separate final premise'];
    const base = buildTheoremKnowledge([candidate('root'), candidate('first', { type, premises, dependencies: dependencies() })]);
    const result = measured(getKnowledgeConsumers(base, rootId(base), { maxBytes: 4096 }), 4096), consumer = result.consumers[0]!;
    expect(consumer.fields.type).toMatchObject({ complete: false, bytes: Buffer.byteLength(type), sha256: mathDigest(type),
      read: { field: 'type', startOffset: 0 } });
    expect(consumer.fields.type).not.toHaveProperty('value');
    expect(consumer.fields.premises).toMatchObject({ complete: false, count: 2, read: { field: 'premises', startOffset: 0 } });
    let recovered = '', startOffset = 0;
    for (;;) {
      const page = getKnowledgeMetadata(base, consumer.id, { field: 'type', startOffset, maxBytes: 4096 });
      if (page.mode !== 'field') throw new Error('expected-field');
      recovered += page.text;
      if (!page.truncated) break;
      startOffset = page.nextOffset!;
    }
    expect(recovered).toBe(type);
    expect(JSON.stringify(result)).not.toContain('Retain this separate final premise');
  });

  it('bounds oversized names, paths and environments and retains exact metadata and root-source navigation', () => {
    const name = 'Saved.' + 'long'.repeat(1300), file = 'Archive/' + 'verylong'.repeat(700) + '.lean';
    const corpus = { [file]: `namespace Saved\nlemma root : True := by trivial\nend Saved\nlemma ${name} : True := by trivial\n` };
    const base = buildTheoremKnowledge([candidate('root', { file, files: corpus, provenance: { ...origin, environmentDigest: 'env'.repeat(5000) } }),
      candidate('first', { name, file, files: corpus, provenance: { ...origin, environmentDigest: 'env'.repeat(5000) },
        dependencies: { ...dependencies(), proof: [{ file, name: 'Saved.root' }] } })]);
    const id = base.entries.find(item => item.name === 'Saved.root')!.id;
    const result = measured(getKnowledgeConsumers(base, id, { maxBytes: 4096 }), 4096), consumer = result.consumers[0]!;
    expect(consumer.fields.name).toMatchObject({ complete: false, bytes: Buffer.byteLength(name), read: { field: 'name', startOffset: 0 } });
    expect(consumer.fields.file).toMatchObject({ complete: false, bytes: Buffer.byteLength(file), read: { field: 'file', startOffset: 0 } });
    expect(consumer.read.source).toEqual({ command: 'knowledge source', id: consumer.id });
    expect(getKnowledgeSource(base, consumer.id, { maxBytes: 65536 }).sha256).toBe(consumer.sourceSha256);
    expect(JSON.stringify(result)).not.toContain('env'.repeat(100));
  });

  it('measures JSON escaping and surrogate-safe previews within the complete output budget', () => {
    const base = buildTheoremKnowledge([candidate('root'), candidate('first', { type: '\u{1f642}'.repeat(79) + '\u96ea"\\\t'.repeat(400),
      premises: ['\u96ea"\\\t'.repeat(400)], dependencies: dependencies() })]);
    for (const maxBytes of [4096, 16000, 65536]) {
      const result = measured(getKnowledgeConsumers(base, rootId(base), { maxBytes }), maxBytes);
      for (const descriptor of Object.values(result.consumers[0]!.fields)) if (descriptor.preview)
        expect(new TextDecoder('utf-8', { fatal: true }).decode(Buffer.from(descriptor.preview))).toBe(descriptor.preview);
    }
  });

  it('keeps recorded elaboration separate from source headers and exactly recoverable through metadata pages', () => {
    const elaboration: NonNullable<KnowledgeCandidate['elaboration']> = {
      schema: 'theorem-os.knowledge-elaboration.v1', evidence: 'recorded-not-replayed',
      fullType: 'forall (n : Nat), ' + 'True -> '.repeat(1800) + 'n = n', universes: ['u'],
      statementContext: { type: 'True', constants: [], omitted: ['Historical fixture omits proof internals'] },
      omissions: [], enrichmentDigest: '1'.repeat(64), sourceDigest: '2'.repeat(64), declarationDigest: '3'.repeat(64),
      collectorDigest: '4'.repeat(64), queryDigest: '5'.repeat(64), artifactsDigest: '6'.repeat(64),
      environmentDigest: 'e'.repeat(64), toolIdentity: 'lean-fixture', sealedEnvironmentIdentity: 'fixture-environment',
    };
    const provenance = { ...origin, environmentDigest: elaboration.environmentDigest };
    const base = buildTheoremKnowledge([candidate('root', { provenance }), candidate('first', { provenance, elaboration,
      type: 'lemma first : True', typeKind: 'source-header', dependencies: dependencies() })]);
    const result = measured(getKnowledgeConsumers(base, rootId(base), { maxBytes: 4096 }), 4096), row = result.consumers[0]!;
    expect(row).toMatchObject({ typeKind: 'source-header', elaborationCoverage: 'recorded',
      fields: { type: { value: 'lemma first : True' }, elaboration: { complete: false,
        read: { field: 'elaboration', startOffset: 0 } } } });
    expect(row.fields.elaboration).not.toHaveProperty('value');
    let recovered = '', startOffset = 0, pages = 0;
    for (;;) {
      const page = measured(getKnowledgeMetadata(base, row.id, { field: 'elaboration', startOffset, maxBytes: 4096 }), 4096);
      if (page.mode !== 'field') throw new Error('expected-field');
      recovered += page.text; pages++;
      if (!page.truncated) break;
      expect(page.nextOffset).toBeGreaterThan(startOffset); startOffset = page.nextOffset!;
    }
    expect(pages).toBeGreaterThan(1);
    expect(JSON.parse(recovered)).toEqual(elaboration);
    expect(row.fields.elaboration.sha256).toBe(mathDigest(recovered));
    expect(row.fields.elaboration).not.toHaveProperty('proofAccepted');
  });

  it('reads only catalog metadata while finding consumers', () => {
    const base = buildTheoremKnowledge([candidate('root'), candidate('first', { dependencies: dependencies() })]);
    for (const hash of Object.keys(base.sources)) Object.defineProperty(base.sources, hash, { get: () => { throw new Error('unexpected_source_read'); } });
    expect(getKnowledgeConsumers(base, rootId(base)).total).toBe(1);
  });

  it('rejects invalid paging options and budgets that cannot carry one complete navigation record', () => {
    const base = buildTheoremKnowledge([candidate('root'), candidate('first', { dependencies: dependencies() })]), id = rootId(base);
    for (const options of [null, [], { offset: -1 }, { offset: 0.5 }, { offset: Infinity }, { limit: 0 }, { limit: 33 },
      { maxBytes: 1023 }, { maxBytes: 65537 }, { maxBytes: NaN }] as unknown as KnowledgeConsumersOptions[])
      expect(() => getKnowledgeConsumers(base, id, options)).toThrow('consumers_options_invalid');
    expect(() => getKnowledgeConsumers(base, id, { maxBytes: 1024 })).toThrow('consumers_budget_too_small');
    expect(() => getKnowledgeConsumers(base, 'missing')).toThrow('theorem_not_found');
  });
});
