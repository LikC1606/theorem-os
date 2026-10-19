import { describe, expect, it } from 'vitest';
import { buildTheoremKnowledge, locateKnowledgeDeclaration, type KnowledgeCandidate } from '../src/solver/theoremKnowledge';
import { getKnowledgeSource, type KnowledgeSourceOptions } from '../src/solver/theoremKnowledgeSource';

function knowledge(source = 'lemma root : True := by trivial\n', files: Record<string, string> = {}) {
  const candidate: KnowledgeCandidate = { name: 'root', file: 'Submission.lean', type: 'True',
    typeKind: 'closed-task-type', kind: 'lemma', description: 'Historical checked source', premises: [],
    dependencies: { statement: [], proof: [], tasks: [], coverage: 'unavailable' },
    files: { 'Submission.lean': source, ...files },
    provenance: { kind: 'solver-check', problemId: 'test-source', source: '/archive/state.json',
      sourceDigest: 'a'.repeat(64), receiptIds: ['historical-only'] } };
  const base = buildTheoremKnowledge([candidate]);
  return { base, id: base.entries[0]!.id, source };
}

describe('bounded knowledge source navigation', () => {
  it('returns exact advisory source with identities and exclusive UTF-16 offsets', () => {
    const source = 'import Mathlib\nsection\nvariable (n : Nat)\nopen Nat\n' +
      'local instance : Inhabited Nat := inferInstance\ndef helper := n\nlemma root : True := by trivial\nend\n';
    const { base, id } = knowledge(source);
    const result = getKnowledgeSource(base, id);
    expect(result).toMatchObject({ id, contextDigest: base.entries[0]!.contextDigest, file: 'Submission.lean',
      sha256: base.contexts[base.entries[0]!.contextDigest]['Submission.lean'], evidence: 'recorded-not-replayed',
      requiresFreshCheck: true, contextCoverage: 'source-excerpt-not-complete-context', offsetEncoding: 'utf16-code-unit',
      endOffsetExclusive: true, mode: 'lines', sourceBytes: Buffer.byteLength(source), sourceLines: 9,
      display: { startOffset: 0, endOffset: source.length, startLine: 1, endLine: 8, bytes: Buffer.byteLength(source) },
      text: source, truncated: false });
    expect(result.nextOffset).toBeUndefined();
    expect(result.declaration).toBeUndefined();
  });

  it('locates a helper definition in the exact context without requiring another knowledge entry', () => {
    const helper = 'namespace Saved\nvariable (n : Nat)\ndef helper : Nat := n\nend Saved\n';
    const { base, id } = knowledge(undefined, { 'Helper.lean': helper });
    const location = locateKnowledgeDeclaration(helper, 'Saved.helper');
    const result = getKnowledgeSource(base, id, { file: 'Helper.lean', name: 'Saved.helper' });
    expect(base.entries).toHaveLength(1);
    expect(result).toMatchObject({ id, file: 'Helper.lean', mode: 'name', truncated: false,
      display: { startOffset: location.startOffset, endOffset: location.endOffset },
      declaration: { name: 'helper', qualifiedName: 'Saved.helper', namespace: 'Saved', kind: 'definition',
        startOffset: location.startOffset, bodyOffset: location.bodyOffset, endOffset: location.endOffset, complete: true } });
    expect(result.text).toBe(helper.slice(location.startOffset, location.endOffset));
  });

  it('prefers exact qualified names over colliding raw names and rejects ambiguous aliases', () => {
    const source = 'lemma root : True := by trivial\nlemma foo : True := by trivial\n' +
      'namespace A\nlemma foo : True := by trivial\nend A\n' +
      'namespace B\nlemma A.foo : True := by trivial\nlemma sibling : True := by trivial\nend B\n' +
      'namespace C\nlemma sibling : True := by trivial\nend C\n';
    const { base, id } = knowledge(source);
    for (const name of ['foo', 'A.foo', 'B.A.foo', '_root_.foo']) {
      const result = getKnowledgeSource(base, id, { name });
      expect(result.declaration?.qualifiedName).toBe(name.replace('_root_.', ''));
      expect(result.display.startOffset).toBe(locateKnowledgeDeclaration(source, name).startOffset);
    }
    for (const name of ['missing', 'sibling'])
      expect(() => getKnowledgeSource(base, id, { name })).toThrow('declaration_missing_or_ambiguous');
  });

  it('retains exact CRLF and Unicode with 1-based line selection', () => {
    const source = '-- \u03b1\r\nlemma root : True := by\r\n  trivial\r\n-- \u{1f642}\u5c3e\r\n';
    const { base, id } = knowledge(source);
    const result = getKnowledgeSource(base, id, { startLine: 2, lines: 2 });
    expect(result).toMatchObject({ sourceLines: 5, sourceBytes: Buffer.byteLength(source),
      display: { startOffset: source.indexOf('lemma'), endOffset: source.indexOf('-- \u{1f642}'), startLine: 2, endLine: 3 },
      text: 'lemma root : True := by\r\n  trivial\r\n', truncated: true,
      nextOffset: source.indexOf('-- \u{1f642}'), nextStartLine: 4 });
    expect(getKnowledgeSource(base, id, { startLine: 5 })).toMatchObject({ text: '', truncated: false,
      display: { startOffset: source.length, endOffset: source.length, startLine: 5, endLine: 5 } });
  });

  it('applies default and explicit line limits to a named declaration', () => {
    const source = 'lemma root : True := by\n' + '  -- proof work\n'.repeat(210) +
      '  trivial\nlemma other : True := by trivial\n';
    const { base, id } = knowledge(source);
    for (const lines of [undefined, 2, 200]) {
      const result = getKnowledgeSource(base, id, { name: 'root', ...(lines === undefined ? {} : { lines }) });
      const count = lines ?? 80;
      expect(result.text).toBe(source.split('\n').slice(0, count).join('\n') + '\n');
      expect(result).toMatchObject({ truncated: true, nextStartLine: count + 1,
        declaration: { complete: false, endOffset: locateKnowledgeDeclaration(source, 'root').endOffset } });
    }
  });

  it('bounds the complete serialized packet and losslessly pages an escaped Unicode line', () => {
    const long = '-- ' + '\u{1f642}\u96ea"\\\t'.repeat(200) + '\r\n-- end\r\n';
    const { base, id } = knowledge(undefined, { 'Long.lean': long });
    let offset = 0, recovered = '', pages = 0, sawMidlineContinuation = false;
    do {
      const result = getKnowledgeSource(base, id, { file: 'Long.lean', startOffset: offset, maxBytes: 1024 });
      expect(Buffer.byteLength(JSON.stringify(result)) + 1).toBeLessThanOrEqual(1024);
      expect(new TextDecoder('utf-8', { fatal: true }).decode(Buffer.from(result.text))).toBe(result.text);
      expect(result.display.startOffset).toBe(offset);
      expect(result.display.bytes).toBe(Buffer.byteLength(result.text));
      expect(result.display.endOffset).toBe(offset + result.text.length);
      expect(result.text).toBe(long.slice(offset, result.display.endOffset));
      recovered += result.text; pages += 1;
      expect(pages).toBeLessThan(100);
      if (!result.truncated) break;
      expect(result.nextOffset).toBeGreaterThan(offset);
      if (result.nextStartLine === result.display.startLine) sawMidlineContinuation = true;
      offset = result.nextOffset!;
    } while (true);
    expect(recovered).toBe(long);
    expect(pages).toBeGreaterThan(1);
    expect(sawMidlineContinuation).toBe(true);
  });

  it('accounts for large named metadata and applies the default JSON budget', () => {
    const source = 'lemma root : True := by\n  -- ' + '\u{1f642}"\\'.repeat(20000) + '\n  trivial\n';
    const { base, id } = knowledge(source);
    for (const maxBytes of [1024, 16000, 65536]) {
      const result = getKnowledgeSource(base, id, { name: 'root', maxBytes });
      expect(Buffer.byteLength(JSON.stringify(result)) + 1).toBeLessThanOrEqual(maxBytes);
      expect(result.text.length).toBeGreaterThan(0);
      expect(result).toMatchObject({ truncated: true, declaration: { complete: false } });
    }
    const result = getKnowledgeSource(base, id);
    expect(Buffer.byteLength(JSON.stringify(result)) + 1).toBeLessThanOrEqual(16000);
    expect(result.truncated).toBe(true);
  });

  it('rejects a byte budget too small even for the required metadata', () => {
    const file = 'x'.repeat(1200) + '.lean';
    const { base, id } = knowledge(undefined, { [file]: '-- helper\n' });
    expect(() => getKnowledgeSource(base, id, { file, maxBytes: 1024 })).toThrow('source_budget_too_small');
  });

  it('validates options and positions without splitting a surrogate pair', () => {
    const { base, id, source } = knowledge(undefined, { 'Unicode.lean': '-- \u{1f642}\n' });
    const invalid: KnowledgeSourceOptions[] = [
      { startLine: 0 }, { startLine: -1 }, { startLine: 1.5 }, { startLine: NaN },
      { startOffset: -1 }, { startOffset: 0.5 }, { startOffset: Infinity },
      { lines: 0 }, { lines: 201 }, { lines: 1.5 },
      { maxBytes: 1023 }, { maxBytes: 65537 }, { maxBytes: 2048.5 },
      { name: '' }, { name: 'root', startLine: 1 }, { name: 'root', startOffset: 0 },
      { startLine: 1, startOffset: 0 },
    ];
    for (const options of invalid) expect(() => getKnowledgeSource(base, id, options)).toThrow('source_options_invalid');
    expect(() => getKnowledgeSource(base, id, null as never)).toThrow('source_options_invalid');
    expect(() => getKnowledgeSource(base, id, { startLine: 3 })).toThrow('source_position_invalid');
    expect(() => getKnowledgeSource(base, id, { startOffset: source.length + 1 })).toThrow('source_position_invalid');
    expect(() => getKnowledgeSource(base, id, { file: 'Unicode.lean', startOffset: 4 })).toThrow('source_position_invalid');
    expect(getKnowledgeSource(base, id, { file: 'Unicode.lean', startOffset: 3 }).text).toBe('\u{1f642}\n');
    expect(getKnowledgeSource(base, id, { startOffset: source.length })).toMatchObject({ text: '', truncated: false });
  });

  it('handles an empty context file without a non-progressing continuation', () => {
    const { base, id } = knowledge(undefined, { 'Empty.lean': '' });
    expect(getKnowledgeSource(base, id, { file: 'Empty.lean' })).toMatchObject({ sourceBytes: 0, sourceLines: 1,
      text: '', truncated: false, display: { startOffset: 0, endOffset: 0, startLine: 1, endLine: 1, bytes: 0 } });
  });

  it('revalidates source SHA and root binding on every call', () => {
    const { base, id } = knowledge(undefined, { 'Helper.lean': 'def helper := 0\n' });
    const entry = base.entries[0]!, rootHash = base.contexts[entry.contextDigest]['Submission.lean'];
    const helperHash = base.contexts[entry.contextDigest]['Helper.lean'];
    const rootSource = base.sources[rootHash], helperSource = base.sources[helperHash];
    getKnowledgeSource(base, id, { file: 'Helper.lean' });
    base.sources[helperHash] += '-- changed\n';
    expect(() => getKnowledgeSource(base, id, { file: 'Helper.lean' })).toThrow('source_changed');
    base.sources[helperHash] = helperSource;
    base.sources[rootHash] += '-- changed\n';
    expect(() => getKnowledgeSource(base, id, { file: 'Helper.lean' })).toThrow('declaration_changed');
    base.sources[rootHash] = rootSource;
    entry.declaration += '-- changed\n';
    expect(() => getKnowledgeSource(base, id, { file: 'Helper.lean' })).toThrow('declaration_changed');
  });

  it('loads only the bound root and selected source when the context is lazy', () => {
    const { base, id } = knowledge(undefined, { 'Helper.lean': 'def helper := 0\n', 'Unrelated.lean': '-- unrelated\n' });
    const context = base.contexts[base.entries[0]!.contextDigest];
    const rootText = base.sources[context['Submission.lean']], helperText = base.sources[context['Helper.lean']];
    let roots = 0, helpers = 0;
    Object.defineProperty(base.sources, context['Submission.lean'], { get: () => { roots += 1; return rootText; } });
    Object.defineProperty(base.sources, context['Helper.lean'], { get: () => { helpers += 1; return helperText; } });
    Object.defineProperty(base.sources, context['Unrelated.lean'], { get: () => { throw new Error('unrelated_read'); } });
    getKnowledgeSource(base, id);
    expect([roots, helpers]).toEqual([1, 0]);
    getKnowledgeSource(base, id, { file: 'Helper.lean', name: 'helper' });
    expect([roots, helpers]).toEqual([2, 1]);
  });

  it('rejects forbidden files and sources outside the pinned context', () => {
    const { base, id } = knowledge();
    for (const file of ['Solution.lean', 'nested/Solution.lean', '../Submission.lean', '/Submission.lean',
      'Missing.lean', 'Other.lean', 'nested\\Submission.lean'])
      expect(() => getKnowledgeSource(base, id, { file })).toThrow('source_not_found');
    expect(() => getKnowledgeSource(base, 'missing')).toThrow('theorem_not_found');
  });
});
