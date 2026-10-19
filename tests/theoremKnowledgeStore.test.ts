import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';
import { buildTheoremKnowledge, getKnowledgeTheorem, searchTheoremKnowledge, theoremKnowledgeStats,
  writeTheoremKnowledge, type KnowledgeCandidate } from '../src/solver/theoremKnowledge';
import { copyKnowledgeSnapshot, copyPackedKnowledge, readKnowledgeCatalog, readPackedKnowledge, writePackedKnowledge } from '../src/solver/theoremKnowledgeStore';

describe('packed theorem knowledge with lazy verified sources', () => {
  let root: string;
  const candidate = (name = 'Saved.identity'): KnowledgeCandidate => ({ name, file: 'Submission.lean',
    type: 'forall (n : Nat), n = n', typeKind: 'closed-task-type', kind: 'lemma', description: 'Saved identity lemma', premises: [],
    dependencies: { statement: [], proof: [], tasks: [], coverage: 'unavailable' },
    files: { 'Submission.lean': `namespace Saved\nlemma ${name.split('.').at(-1)} (n : Nat) : n = n := by rfl\nend Saved\n`,
      'lean-toolchain': 'leanprover/lean4:v4.33.0\n' },
    provenance: { kind: 'solver-check', problemId: 'identity', source: '/archived/state.json', sourceDigest: 'a'.repeat(64),
      runId: 'old-run', environmentDigest: 'saved-env', sourceCommit: 'source-commit', checkedCommit: 'checked-commit', receiptIds: ['old-receipt'] } });
  const fixture = () => {
    const base = buildTheoremKnowledge([candidate(), candidate('Saved.reflexive')]);
    const file = path.join(root, 'catalog.json'), written = writePackedKnowledge(file, base, 'b'.repeat(64));
    return { base, file, written, text: fs.readFileSync(file, 'utf8'), objects: file + '.objects' };
  };
  const replace = (file: string, text: string) => {
    fs.chmodSync(file, 0o600); fs.writeFileSync(file, text); fs.chmodSync(file, 0o400);
  };
  beforeEach(() => { root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'packed-knowledge-test-'))); });
  afterEach(() => { vi.restoreAllMocks(); fs.rmSync(root, { recursive: true, force: true }); });

  it('preserves exact entry IDs, contexts, provenance and full source materialization', () => {
    const f = fixture(), loaded = readPackedKnowledge(f.file, f.written.sha256);
    expect(loaded.format).toBe('v2');
    expect(loaded.base.entries).toEqual(f.base.entries);
    expect(loaded.base.contexts).toEqual(f.base.contexts);
    expect(JSON.parse(JSON.stringify(loaded.base))).toEqual(f.base);
    expect(loaded.digest).toBe(mathDigest(loaded.text));
    expect(JSON.parse(loaded.text)).toMatchObject({ schema: 'theorem-os.theorem-knowledge.v2', originSha256: 'b'.repeat(64) });
    expect(theoremKnowledgeStats(loaded.base)).toEqual(theoremKnowledgeStats(f.base));
    expect(fs.statSync(f.file).mode & 0o222).toBe(0);
    for (const digest of Object.keys(f.base.sources)) expect(fs.statSync(path.join(f.objects, digest)).mode & 0o222).toBe(0);
  });

  it('reads only the manifest while loading metadata, searching and reporting statistics', () => {
    const f = fixture(), opened = vi.spyOn(fs, 'openSync');
    const loaded = readPackedKnowledge(f.file, f.written.sha256);
    expect(searchTheoremKnowledge(loaded.base, 'identity').hits).toHaveLength(2);
    expect(theoremKnowledgeStats(loaded.base).entries).toBe(2);
    expect(opened.mock.calls.map(call => String(call[0]))).toEqual([f.file]);
  });

  it('keeps unified v2 loading on the same metadata-only path', () => {
    const f = fixture(), opened = vi.spyOn(fs, 'openSync');
    expect(readKnowledgeCatalog(f.file, f.written.sha256).format).toBe('v2');
    expect(opened.mock.calls.map(call => String(call[0]))).toEqual([f.file]);
  });

  it('validates and returns one consistent v1 snapshot from a single read', () => {
    const base = buildTheoremKnowledge([candidate()]), file = path.join(root, 'legacy.json');
    const written = writeTheoremKnowledge(file, base), text = fs.readFileSync(file, 'utf8');
    const opened = vi.spyOn(fs, 'openSync'), loaded = readKnowledgeCatalog(file, written.sha256);
    expect(loaded).toEqual({ base, text, digest: written.sha256, format: 'v1' });
    expect(loaded.digest).toBe(mathDigest(loaded.text));
    expect(opened.mock.calls.map(call => String(call[0]))).toEqual([file]);
  });

  it('retains v1 parsing, schema, content and pinned identity checks', () => {
    const base = buildTheoremKnowledge([candidate()]), file = path.join(root, 'legacy.json');
    const written = writeTheoremKnowledge(file, base);
    expect(() => readKnowledgeCatalog(file, '0'.repeat(64))).toThrow('math_knowledge_identity_changed');
    replace(file, '{');
    expect(() => readKnowledgeCatalog(file)).toThrow('math_knowledge_schema_invalid');
    replace(file, JSON.stringify({ ...base, entries: null }));
    expect(() => readKnowledgeCatalog(file)).toThrow('math_knowledge_schema_invalid');
    base.sources[Object.keys(base.sources)[0]!] += 'changed';
    const changed = JSON.stringify(base);
    replace(file, changed);
    expect(() => readKnowledgeCatalog(file, mathDigest(changed))).toThrow('math_knowledge_source_changed');
    expect(() => readKnowledgeCatalog(file, written.sha256)).toThrow('math_knowledge_identity_changed');
  });

  it('verifies source bytes and hashes whenever a requested source is read', () => {
    const f = fixture(), loaded = readPackedKnowledge(f.file), entry = loaded.base.entries[0]!;
    const digest = loaded.base.contexts[entry.contextDigest]![entry.file]!;
    expect(getKnowledgeTheorem(loaded.base, entry.id, entry.file).source?.text).toBe(f.base.sources[digest]);
    replace(path.join(f.objects, digest), f.base.sources[digest]!.replace('rfl', 'foo'));
    expect(() => getKnowledgeTheorem(loaded.base, entry.id, entry.file)).toThrow('math_knowledge_source_changed');
    expect(() => readPackedKnowledge(f.file).base.sources[digest]).toThrow('math_knowledge_source_changed');
  });

  it('does not read unrelated proof blobs during a theorem lookup', () => {
    const f = fixture(), loaded = readPackedKnowledge(f.file), first = loaded.base.entries[0]!, second = loaded.base.entries[1]!;
    const unrelated = loaded.base.contexts[second.contextDigest]![second.file]!;
    replace(path.join(f.objects, unrelated), f.base.sources[unrelated]!.replace('rfl', 'foo'));
    const opened = vi.spyOn(fs, 'openSync');
    expect(getKnowledgeTheorem(loaded.base, first.id).name).toBe(first.name);
    expect(opened.mock.calls.map(call => String(call[0]))).not.toContain(path.join(f.objects, unrelated));
  });

  it.each(['type', 'declaration', 'context', 'source-key'])('rejects tampered manifest %s metadata', field => {
    const f = fixture(), manifest = JSON.parse(f.text);
    if (field === 'type') manifest.entries[0].type = 'False';
    else if (field === 'declaration') manifest.entries[0].declaration = 'lemma forged : False := by sorry';
    else if (field === 'context') manifest.contexts[manifest.entries[0].contextDigest]['Submission.lean'] = '0'.repeat(64);
    else { const key = Object.keys(manifest.sources)[0]!; manifest.sources['0'.repeat(64)] = manifest.sources[key]; delete manifest.sources[key]; }
    replace(f.file, JSON.stringify(manifest));
    expect(() => readPackedKnowledge(f.file)).toThrow();
    expect(() => readPackedKnowledge(f.file, f.written.sha256)).toThrow('math_knowledge_identity_changed');
  });

  it('binds a self-consistent metadata declaration to the actual source when retrieved', () => {
    const f = fixture(), manifest = JSON.parse(f.text), entry = manifest.entries[0];
    entry.declaration = entry.declaration.replace('by rfl', 'by exact Eq.refl n');
    const { id: _id, provenance: _provenance, ...identity } = entry;
    entry.id = mathDigest(canonicalMathJson(identity));
    replace(f.file, JSON.stringify(manifest));
    const loaded = readPackedKnowledge(f.file);
    expect(() => getKnowledgeTheorem(loaded.base, entry.id)).toThrow('math_knowledge_declaration_changed');
  });

  it.each(['../objects', '/tmp/objects', 'nested/objects', 'nested\\objects', '.', '..'])
  ('rejects objects directory traversal %s', directory => {
    const f = fixture(), manifest = JSON.parse(f.text); manifest.objectsDirectory = directory;
    replace(f.file, JSON.stringify(manifest));
    expect(() => readPackedKnowledge(f.file)).toThrow('math_knowledge_packed_schema_invalid');
  });

  it('rejects missing or resized source objects without reading their bytes', () => {
    const f = fixture(), digest = Object.keys(f.base.sources)[0]!, blob = path.join(f.objects, digest);
    fs.unlinkSync(blob);
    expect(() => readPackedKnowledge(f.file)).toThrow('math_knowledge_packed_source_missing_or_invalid');
    fs.writeFileSync(blob, 'changed', { mode: 0o400 });
    expect(() => readPackedKnowledge(f.file)).toThrow('math_knowledge_source_changed');
  });

  it('rejects linked manifest, object directory and blobs', () => {
    const f = fixture(), link = path.join(root, 'linked.json'); fs.symlinkSync(f.file, link);
    expect(() => readPackedKnowledge(link)).toThrow('math_path_invalid');
    const saved = f.objects + '-saved'; fs.renameSync(f.objects, saved); fs.symlinkSync(saved, f.objects);
    expect(() => readPackedKnowledge(f.file)).toThrow('math_path_invalid');
    fs.unlinkSync(f.objects); fs.renameSync(saved, f.objects);
    const digest = Object.keys(f.base.sources)[0]!, blob = path.join(f.objects, digest), target = blob + '-saved';
    fs.renameSync(blob, target); fs.symlinkSync(target, blob);
    expect(() => readPackedKnowledge(f.file)).toThrow('math_path_invalid');
  });

  it('rejects hard-linked or writable blobs', () => {
    const f = fixture(), digest = Object.keys(f.base.sources)[0]!, blob = path.join(f.objects, digest);
    fs.linkSync(blob, blob + '-link');
    expect(() => readPackedKnowledge(f.file)).toThrow('math_knowledge_packed_source_missing_or_invalid');
    fs.unlinkSync(blob + '-link'); fs.chmodSync(blob, 0o600);
    expect(() => readPackedKnowledge(f.file)).toThrow('math_knowledge_packed_source_not_frozen');
  });

  it('refuses to overwrite an existing manifest or object directory', () => {
    const f = fixture();
    expect(() => writePackedKnowledge(f.file, f.base)).toThrow('math_knowledge_packed_output_exists');
    const next = path.join(root, 'next.json'); fs.mkdirSync(next + '.objects');
    expect(() => writePackedKnowledge(next, f.base)).toThrow('math_knowledge_packed_output_exists');
    expect(fs.readFileSync(f.file, 'utf8')).toBe(f.text);
    expect(fs.existsSync(next)).toBe(false);
  });

  it('fully verifies a new catalog before creating any publication artifacts', () => {
    const base = buildTheoremKnowledge([candidate()]), file = path.join(root, 'invalid.json');
    base.sources[Object.keys(base.sources)[0]!] += 'changed';
    expect(() => writePackedKnowledge(file, base)).toThrow('math_knowledge_source_changed');
    expect(fs.existsSync(file)).toBe(false);
    expect(fs.existsSync(file + '.objects')).toBe(false);
  });

  it('rejects invalid UTF-8 when the matching content-addressed object is requested', () => {
    const f = fixture(), manifest = JSON.parse(f.text), bytes = Buffer.from([0xff, 0xfe]), digest = mathDigest(bytes);
    manifest.sources[digest] = { bytes: bytes.length };
    fs.writeFileSync(path.join(f.objects, digest), bytes, { mode: 0o400 });
    replace(f.file, JSON.stringify(manifest));
    const loaded = readPackedKnowledge(f.file);
    expect(() => loaded.base.sources[digest]).toThrow('math_knowledge_packed_source_invalid_utf8');
  });

  it('copies isolated worker objects while retaining exact manifest bytes and digest across retries', () => {
    const f = fixture(), worker = path.join(root, 'worker/theorem-knowledge.json');
    const copied = copyPackedKnowledge(f.text, f.file, worker), loaded = readPackedKnowledge(worker, f.written.sha256);
    expect(copied.sha256).toBe(f.written.sha256);
    expect(loaded.text).toBe(f.text);
    expect(JSON.parse(JSON.stringify(loaded.base))).toEqual(f.base);
    const copiedObjects = path.join(path.dirname(worker), JSON.parse(f.text).objectsDirectory);
    for (const digest of Object.keys(f.base.sources)) {
      expect(fs.statSync(path.join(copiedObjects, digest)).ino).not.toBe(fs.statSync(path.join(f.objects, digest)).ino);
      expect(fs.statSync(path.join(copiedObjects, digest)).nlink).toBe(1);
    }
    expect(copyPackedKnowledge(f.text, f.file, worker).sha256).toBe(f.written.sha256);
  });

  it('rejects an inconsistent source catalog before creating a worker snapshot', () => {
    const f = fixture(), worker = path.join(root, 'worker/theorem-knowledge.json');
    const digest = Object.keys(f.base.sources).find(key => f.base.sources[key]!.includes('rfl'))!;
    replace(path.join(f.objects, digest), f.base.sources[digest]!.replace('rfl', 'foo'));
    expect(() => copyPackedKnowledge(f.text, f.file, worker)).toThrow('math_knowledge_source_changed');
    expect(fs.existsSync(path.dirname(worker))).toBe(false);
  });

  it('rejects a conflicting worker manifest or blob without overwriting it', () => {
    const f = fixture(), worker = path.join(root, 'worker/theorem-knowledge.json');
    copyPackedKnowledge(f.text, f.file, worker);
    replace(worker, f.text + ' ');
    expect(() => copyPackedKnowledge(f.text, f.file, worker)).toThrow('math_knowledge_identity_changed');
    expect(fs.readFileSync(worker, 'utf8')).toBe(f.text + ' ');
    replace(worker, f.text);
    const digest = Object.keys(f.base.sources).find(key => f.base.sources[key]!.includes('rfl'))!;
    const blob = path.join(path.dirname(worker), JSON.parse(f.text).objectsDirectory, digest);
    const changed = f.base.sources[digest]!.replace('rfl', 'foo'); replace(blob, changed);
    expect(() => copyPackedKnowledge(f.text, f.file, worker)).toThrow('math_knowledge_source_changed');
    expect(fs.readFileSync(blob, 'utf8')).toBe(changed);
  });

  it('reads and copies either catalog format through one interface', () => {
    const f = fixture(), legacy = path.join(root, 'legacy.json');
    writeTheoremKnowledge(legacy, f.base);
    for (const [file, format] of [[legacy, 'v1'], [f.file, 'v2']] as const) {
      const loaded = readKnowledgeCatalog(file);
      expect(loaded.format).toBe(format);
      expect(JSON.parse(JSON.stringify(loaded.base))).toEqual(f.base);
      const target = path.join(root, format, 'snapshot.json');
      expect(copyKnowledgeSnapshot(loaded, file, target)).toMatchObject({ sha256: loaded.digest, format });
      expect(copyKnowledgeSnapshot(loaded, file, target)).toMatchObject({ sha256: loaded.digest, format });
      expect(readKnowledgeCatalog(target, loaded.digest).base.entries).toEqual(f.base.entries);
      expect(fs.statSync(target).mode & 0o222).toBe(0);
    }
  });

  it('checks the supplied snapshot digest before copying and refuses conflicting v1 snapshots', () => {
    const base = buildTheoremKnowledge([candidate()]), legacy = path.join(root, 'legacy.json');
    writeTheoremKnowledge(legacy, base);
    const loaded = readKnowledgeCatalog(legacy), target = path.join(root, 'copy.json');
    expect(() => copyKnowledgeSnapshot({ ...loaded, digest: '0'.repeat(64) }, legacy, target))
      .toThrow('math_knowledge_identity_changed');
    expect(fs.existsSync(target)).toBe(false);
    copyKnowledgeSnapshot(loaded, legacy, target); replace(target, loaded.text + ' ');
    expect(() => copyKnowledgeSnapshot(loaded, legacy, target)).toThrow('math_knowledge_identity_changed');
    expect(fs.readFileSync(target, 'utf8')).toBe(loaded.text + ' ');
  });
});
