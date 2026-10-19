import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { afterEach, describe, expect, it } from 'vitest';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';
import { buildTheoremKnowledge, getKnowledgeTheorem, writeTheoremKnowledge, type KnowledgeCandidate, type TheoremKnowledgeBase } from '../src/solver/theoremKnowledge';
import { getKnowledgeMetadata, type KnowledgeMetadataField, type KnowledgeMetadataOptions } from '../src/solver/theoremKnowledgeMetadata';
import { getKnowledgeSource } from '../src/solver/theoremKnowledgeSource';
import { writePackedKnowledge } from '../src/solver/theoremKnowledgeStore';

const directories: string[] = [];
afterEach(() => { for (const directory of directories.splice(0)) fs.rmSync(directory, { recursive: true, force: true }); });

function candidate(overrides: Partial<KnowledgeCandidate> = {}): KnowledgeCandidate {
  return { name: 'Saved.root', file: 'Submission.lean', type: 'forall (n : Nat), n = n',
    typeKind: 'closed-task-type', kind: 'lemma', description: 'A historical exact interface',
    premises: ['Retain the original ambient type'],
    dependencies: { statement: [], proof: [], tasks: [], coverage: 'unavailable' },
    files: { 'Submission.lean': 'namespace Saved\nlemma root (n : Nat) : n = n := by\n  -- proof-body-marker\n  rfl\nend Saved\n' },
    provenance: { kind: 'solver-check', problemId: 'metadata-fixture', source: '/archive/state.json',
      sourceDigest: 'a'.repeat(64), environmentDigest: 'historical-environment', receiptIds: ['historical-only'] },
    ...overrides };
}
function summary(base: TheoremKnowledgeBase, id = base.entries[0]!.id, maxBytes?: number) {
  const result = getKnowledgeMetadata(base, id, { maxBytes });
  if (result.mode !== 'summary') throw new Error('expected-summary');
  return result;
}
function readField(base: TheoremKnowledgeBase, id: string, field: KnowledgeMetadataField, maxBytes = 2048) {
  let startOffset = 0, recovered = '', pages = 0, sha256 = '';
  while (true) {
    const result = getKnowledgeMetadata(base, id, { field, startOffset, maxBytes });
    if (result.mode !== 'field') throw new Error('expected-field');
    expect(Buffer.byteLength(JSON.stringify(result)) + 1).toBeLessThanOrEqual(maxBytes);
    expect(result.display.startOffset).toBe(startOffset);
    expect(result.display.endOffset).toBe(startOffset + result.text.length);
    expect(new TextDecoder('utf-8', { fatal: true }).decode(Buffer.from(result.text))).toBe(result.text);
    expect(result).toMatchObject({ field, requiresFreshCheck: true, evidence: 'recorded-not-replayed',
      offsetEncoding: 'utf16-code-unit', endOffsetExclusive: true });
    if (sha256) expect(result.sha256).toBe(sha256);
    sha256 = result.sha256;
    recovered += result.text;
    pages++;
    expect(pages).toBeLessThan(1000);
    if (!result.truncated) {
      expect(result.nextOffset).toBeUndefined();
      expect(Buffer.byteLength(recovered)).toBe(result.bytes);
      expect(mathDigest(recovered)).toBe(sha256);
      return { text: recovered, pages };
    }
    expect(result.nextOffset).toBeGreaterThan(startOffset);
    startOffset = result.nextOffset!;
  }
}

describe('bounded theorem knowledge metadata', () => {
  it('returns complete small interfaces and explicit source navigation without proof bodies', () => {
    const input = candidate(), base = buildTheoremKnowledge([input]), entry = base.entries[0]!;
    const result = summary(base);
    expect(result).toMatchObject({ id: entry.id, contextDigest: entry.contextDigest,
      typeKind: input.typeKind, kind: input.kind, evidence: 'recorded-not-replayed', requiresFreshCheck: true,
      contextCoverage: 'metadata-only-not-complete-lean-context', allFieldsComplete: true,
      proofSource: { readWith: 'knowledge source', fileField: 'file', nameField: 'name' } });
    expect(result.fields.type).toMatchObject({ format: 'text', complete: true, value: input.type,
      bytes: Buffer.byteLength(input.type), sha256: mathDigest(input.type) });
    expect(result.fields.premises).toMatchObject({ format: 'json', complete: true, count: 1, value: input.premises });
    expect(result.fields.dependencies.value).toEqual(input.dependencies);
    expect(result.fields.provenance.value).toEqual([input.provenance]);
    expect(JSON.stringify(result)).not.toContain('proof-body-marker');
    expect(result).not.toHaveProperty('declaration');
    expect(result).not.toHaveProperty('source');
    expect(getKnowledgeSource(base, entry.id, { name: input.name }).text).toContain('proof-body-marker');
  });

  it('keeps a 400042-byte proof out of default metadata while preserving the original get output', () => {
    const source = 'theorem Saved.huge : True := by\n' + '  -- a retained proof construction step\n'.repeat(10000) + '  trivial\n';
    const base = buildTheoremKnowledge([candidate({ name: 'Saved.huge', type: 'True',
      files: { 'Submission.lean': source } })]), entry = base.entries[0]!;
    expect(Buffer.byteLength(source)).toBe(400042);
    const result = summary(base), original = getKnowledgeTheorem(base, entry.id, entry.file);
    expect(Buffer.byteLength(JSON.stringify(result)) + 1).toBeLessThanOrEqual(16000);
    expect(JSON.stringify(result)).not.toContain('retained proof construction');
    expect(original.declaration).toBe(source);
    expect(original.source?.text).toBe(source);
    expect(Buffer.byteLength(JSON.stringify(original))).toBeGreaterThan(800000);
  });

  it('preserves source headers and closed task types as distinct exact metadata', () => {
    for (const typeKind of ['source-header', 'closed-task-type'] as const) {
      const input = candidate({ typeKind, type: typeKind === 'source-header'
        ? 'root (n : Nat) : n = n' : 'forall (n : Nat), n = n' });
      const base = buildTheoremKnowledge([input]), result = summary(base);
      expect(result.typeKind).toBe(typeKind);
      expect(result.fields.type.value).toBe(input.type);
      expect(readField(base, base.entries[0]!.id, 'type').text).toBe(input.type);
    }
  });

  it('defers oversized types and premises explicitly and reconstructs them without changing source headers', () => {
    const input = candidate({ type: 'forall (n : Nat), ' + 'True -> '.repeat(2000) + 'n = n /- \u{1f642}\u96ea"\\\t -/',
      premises: ['\u{1f642}\u96ea"\\\t\r\n'.repeat(700), 'Keep this separate final premise'] });
    const base = buildTheoremKnowledge([input]), entry = base.entries[0]!, result = summary(base, entry.id, 4096);
    expect(Buffer.byteLength(JSON.stringify(result)) + 1).toBeLessThanOrEqual(4096);
    expect(result.allFieldsComplete).toBe(false);
    for (const field of ['type', 'premises'] as const) {
      expect(result.fields[field]).toMatchObject({ complete: false, read: { field, startOffset: 0 } });
      expect(result.fields[field]).not.toHaveProperty('value');
    }
    expect(result.fields.premises.count).toBe(2);
    const type = readField(base, entry.id, 'type'), premises = readField(base, entry.id, 'premises');
    expect(type.pages).toBeGreaterThan(1);
    expect(premises.pages).toBeGreaterThan(1);
    expect(type.text).toBe(input.type);
    expect(JSON.parse(premises.text)).toEqual(input.premises);
    expect(getKnowledgeSource(base, entry.id, { name: entry.name }).text).not.toContain(input.type);
  });

  it('provides continuations for large names, paths, environment identities and descriptions', () => {
    const name = 'Saved.' + 'root'.repeat(1500), file = 'Archived/' + 'file'.repeat(1500) + '.lean';
    const input = candidate({ name, file, description: '\u{1f642}"\\'.repeat(2000),
      files: { [file]: `theorem ${name} : True := by trivial\n` },
      provenance: { ...candidate().provenance, environmentDigest: 'environment'.repeat(1000) } });
    const base = buildTheoremKnowledge([input]), entry = base.entries[0]!, result = summary(base, entry.id, 4096);
    for (const field of ['name', 'file', 'environmentDigest', 'description'] as const) {
      expect(result.fields[field]).toMatchObject({ complete: false, read: { field, startOffset: 0 } });
      const expected = field === 'environmentDigest' ? input.provenance.environmentDigest! : input[field];
      expect(readField(base, entry.id, field).text).toBe(expected);
    }
  });

  it('pages large dependency, provenance, contextual-version and file inventories without hiding omissions', () => {
    const input = candidate({ dependencies: { statement: Array.from({ length: 35 }, (_, index) =>
      ({ file: 'Submission.lean', name: `Saved.dependency_${index}_${'x'.repeat(200)}` })), proof: [], tasks: [], coverage: 'recorded' },
      provenance: { ...candidate().provenance, source: '/archive/' + 'state'.repeat(3000) },
      files: { ...candidate().files, ...Object.fromEntries(Array.from({ length: 50 }, (_, index) =>
        [`Archived/helper_${index}_${'x'.repeat(80)}.lean`, `-- archived helper ${index}\n`])) } });
    const versions = Array.from({ length: 30 }, (_, index) => ({ ...input,
      files: { ...input.files, 'Submission.lean': `-- context ${index}\n` + input.files['Submission.lean']! } }));
    const base = buildTheoremKnowledge(versions), entry = base.entries[0]!, result = summary(base, entry.id, 4096);
    const original = getKnowledgeTheorem(base, entry.id);
    for (const field of ['dependencies', 'provenance', 'relatedVersions', 'files'] as const) {
      expect(result.fields[field]).toMatchObject({ complete: false, read: { field, startOffset: 0 } });
      const recovered = JSON.parse(readField(base, entry.id, field, 4096).text);
      const expected = field === 'files' ? original.files.map(({ file, sha256 }) => ({ file, sha256 })) : original[field];
      expect(recovered).toEqual(expected);
    }
    expect(result.fields.relatedVersions.count).toBe(30);
    expect(result.fields.files.count).toBe(51);
  });

  it('measures JSON escaping and the trailing newline at every supported output size', () => {
    const input = candidate({ type: 'True /- ' + '\u{1f642}\u96ea"\\\t'.repeat(3000) + ' -/' });
    const base = buildTheoremKnowledge([input]), id = base.entries[0]!.id;
    for (const maxBytes of [1024, 4096, 16000, 65536]) {
      const result = getKnowledgeMetadata(base, id, { field: 'type', maxBytes });
      expect(Buffer.byteLength(JSON.stringify(result)) + 1).toBeLessThanOrEqual(maxBytes);
    }
    for (const maxBytes of [4096, 16000, 65536]) {
      const result = summary(base, id, maxBytes);
      expect(Buffer.byteLength(JSON.stringify(result)) + 1).toBeLessThanOrEqual(maxBytes);
      expect(result.fields.type.complete).toBe(result.fields.type.value === input.type);
    }
  });

  it('keeps missing environment information explicit and handles empty fields and exhausted continuations', () => {
    const input = candidate({ description: '', premises: [], provenance: {
      kind: 'solver-check', problemId: 'fixture', source: '/archive/state.json',
      sourceDigest: 'a'.repeat(64), receiptIds: ['historical-only'] } });
    const base = buildTheoremKnowledge([input]), id = base.entries[0]!.id, result = summary(base);
    expect(result.fields.environmentDigest).toMatchObject({ format: 'json', complete: true, value: null });
    expect(readField(base, id, 'environmentDigest').text).toBe('null');
    expect(readField(base, id, 'description')).toEqual({ text: '', pages: 1 });
    expect(readField(base, id, 'premises').text).toBe('[]');
    expect(getKnowledgeMetadata(base, id, { field: 'type', startOffset: input.type.length }))
      .toMatchObject({ text: '', truncated: false });
  });

  it('validates options and positions and never accepts an offset inside a surrogate pair', () => {
    const base = buildTheoremKnowledge([candidate({ description: '\u{1f642}tail' })]), id = base.entries[0]!.id;
    const invalid: KnowledgeMetadataOptions[] = [
      { maxBytes: 1023 }, { maxBytes: 65537 }, { maxBytes: NaN }, { maxBytes: 2048.5 },
      { startOffset: 0 }, { field: 'type', startOffset: -1 }, { field: 'type', startOffset: 0.5 },
      { field: 'type', startOffset: Infinity }, { field: 'declaration' as KnowledgeMetadataField },
    ];
    for (const options of invalid)
      expect(() => getKnowledgeMetadata(base, id, options)).toThrow('metadata_options_invalid');
    expect(() => getKnowledgeMetadata(base, id, null as never)).toThrow('metadata_options_invalid');
    expect(() => getKnowledgeMetadata(base, id, { field: 'description', startOffset: 1 })).toThrow('metadata_position_invalid');
    expect(() => getKnowledgeMetadata(base, id, { field: 'description', startOffset: 7 })).toThrow('metadata_position_invalid');
    expect(getKnowledgeMetadata(base, id, { field: 'description', startOffset: 2 })).toMatchObject({ text: 'tail' });
    expect(() => summary(base, id, 1024)).toThrow('metadata_budget_too_small');
    expect(() => getKnowledgeMetadata(base, 'missing')).toThrow('theorem_not_found');
  });

  it('revalidates root source identity for summaries and individual fields', () => {
    const base = buildTheoremKnowledge([candidate()]), entry = base.entries[0]!, digest = base.contexts[entry.contextDigest]![entry.file]!;
    const source = base.sources[digest];
    for (const options of [{}, { field: 'type' as const }]) {
      base.sources[digest] = source + '-- changed\n';
      expect(() => getKnowledgeMetadata(base, entry.id, options)).toThrow('declaration_changed');
      base.sources[digest] = source;
      const declaration = entry.declaration;
      entry.declaration += '-- changed\n';
      expect(() => getKnowledgeMetadata(base, entry.id, options)).toThrow('declaration_changed');
      entry.declaration = declaration;
    }
  });

  it('reads only the bound root source and leaves unrelated metadata fields lazy during field reads', () => {
    const input = candidate({ files: { ...candidate().files, 'Unrelated.lean': '-- unrelated archived file\n' } });
    const base = buildTheoremKnowledge([input]), entry = base.entries[0]!, context = base.contexts[entry.contextDigest]!;
    const rootText = base.sources[context[entry.file]!];
    let roots = 0;
    Object.defineProperty(base.sources, context[entry.file]!, { get: () => { roots++; return rootText; } });
    Object.defineProperty(base.sources, context['Unrelated.lean']!, { get: () => { throw new Error('unrelated-source-read'); } });
    expect(summary(base).fields.files.count).toBe(2);
    expect(roots).toBe(1);
    Object.defineProperty(entry, 'provenance', { get: () => { throw new Error('unrelated-metadata-read'); } });
    expect(readField(base, entry.id, 'type').text).toBe(input.type);
    expect(roots).toBe(2);
    expect(JSON.parse(readField(base, entry.id, 'files').text))
      .toEqual(Object.keys(context).sort().map(file => ({ file, sha256: context[file] })));
    expect(roots).toBe(3);
  });

  it('hashes exact structured metadata rather than an abbreviated preview', () => {
    const input = candidate(), base = buildTheoremKnowledge([input]), result = summary(base);
    expect(result.fields.premises.sha256).toBe(mathDigest(canonicalMathJson(input.premises)));
    expect(result.fields.dependencies.sha256).toBe(mathDigest(canonicalMathJson(input.dependencies)));
  });
});

describe('knowledge metadata CLI', () => {
  const cli = (file: string, digest: string, id: string, args: string[]) => spawnSync('bun',
    [path.resolve('bin/math.ts'), 'knowledge', ...args, '--catalog', file, '--sha256', digest, '--id', id],
    { encoding: 'utf8', maxBuffer: 2 * 1024 * 1024 });
  function catalog(input = candidate(), format: 'v1' | 'v2' = 'v2') {
    const directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'knowledge-metadata-cli-')));
    directories.push(directory);
    const file = path.join(directory, 'catalog.json'), base = buildTheoremKnowledge([input]);
    const written = format === 'v1' ? writeTheoremKnowledge(file, base) : writePackedKnowledge(file, base);
    return { file, digest: written.sha256, base, id: base.entries[0]!.id };
  }
  it.each(['v1', 'v2'] as const)('prints bounded metadata for a %s catalog and preserves complete legacy get output', format => {
    const input = candidate({ files: { 'Submission.lean': 'namespace Saved\nlemma root : True := by\n' +
      '  -- retained CLI proof body\n'.repeat(10000) + '  trivial\nend Saved\n' } });
    const { file, digest, base, id } = catalog(input, format);
    const metadata = cli(file, digest, id, ['get', '--metadata', '--max-bytes', '4096']);
    expect(metadata.status).toBe(0);
    expect(metadata.stderr).toBe('');
    expect(Buffer.byteLength(metadata.stdout)).toBeLessThanOrEqual(4096);
    expect(JSON.parse(metadata.stdout)).toMatchObject({ mode: 'summary', requiresFreshCheck: true,
      fields: { type: { complete: true, value: input.type }, premises: { complete: true, value: input.premises } } });
    expect(metadata.stdout).not.toContain('retained CLI proof body');
    const original = cli(file, digest, id, ['get', '--source', 'Submission.lean']);
    expect(original.status).toBe(0);
    expect(JSON.parse(original.stdout)).toEqual(getKnowledgeTheorem(base, id, 'Submission.lean'));
    const source = cli(file, digest, id, ['source', '--file', 'Submission.lean', '--name', 'Saved.root', '--max-bytes', '1024']);
    expect(source.status).toBe(0);
    expect(Buffer.byteLength(source.stdout)).toBeLessThanOrEqual(1024);
    const first = JSON.parse(source.stdout);
    expect(first).toMatchObject({ truncated: true, declaration: { complete: false } });
    const continuation = cli(file, digest, id, ['source', '--file', 'Submission.lean', '--offset', String(first.nextOffset), '--max-bytes', '1024']);
    expect(continuation.status).toBe(0);
    expect(JSON.parse(continuation.stdout).display.startOffset).toBe(first.nextOffset);
  });

  it('losslessly reconstructs oversized exact types and premises through CLI field continuations', () => {
    const input = candidate({ type: 'forall (n : Nat), ' + 'True -> '.repeat(1400) + 'n = n /- \u{1f642}\u96ea"\\\t -/',
      premises: ['\u{1f642}\u96ea"\\\t'.repeat(500), 'The final premise must remain separate'] });
    const { file, digest, id } = catalog(input);
    const response = cli(file, digest, id, ['get', '--metadata', '--max-bytes', '4096']);
    expect(response.status).toBe(0);
    const result = JSON.parse(response.stdout);
    for (const field of ['type', 'premises'] as const) {
      expect(result.fields[field]).toMatchObject({ complete: false, read: { field, startOffset: 0 } });
      let offset = result.fields[field].read.startOffset, recovered = '', pages = 0;
      while (true) {
        const response = cli(file, digest, id, ['get', '--metadata', '--field', field, '--offset', String(offset), '--max-bytes', '4096']);
        expect(response.status).toBe(0);
        expect(Buffer.byteLength(response.stdout)).toBeLessThanOrEqual(4096);
        const page = JSON.parse(response.stdout);
        recovered += page.text;
        pages++;
        expect(pages).toBeLessThan(30);
        if (!page.truncated) break;
        expect(page.nextOffset).toBeGreaterThan(offset);
        offset = page.nextOffset;
      }
      expect(pages).toBeGreaterThan(1);
      expect(mathDigest(recovered)).toBe(result.fields[field].sha256);
      expect(field === 'premises' ? JSON.parse(recovered) : recovered).toEqual(input[field]);
    }
  });

  it('rejects conflicting output modes, invalid field reads and changed catalog pins without unbounded fallback', () => {
    const { file, digest, id } = catalog();
    for (const args of [
      ['get', '--metadata', '--source', 'Submission.lean'], ['get', '--field', 'type'],
      ['get', '--max-bytes', '4096'], ['get', '--metadata', '--field', 'declaration'],
      ['get', '--metadata', '--offset', '0'], ['get', '--metadata', '--field', 'type', '--offset', '-1'],
    ]) {
      const result = cli(file, digest, id, args);
      expect(result.status).toBe(1);
      expect(result.stdout).toBe('');
      expect(result.stderr).toBeTruthy();
    }
    const result = cli(file, 'b'.repeat(64), id, ['get', '--metadata']);
    expect(result.status).toBe(1);
    expect(result.stdout).toBe('');
    expect(result.stderr).toContain('knowledge_identity_changed');
  });
});
