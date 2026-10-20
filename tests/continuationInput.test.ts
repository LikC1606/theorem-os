import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';
import { readContinuationInput, freezeContinuationInput, readContinuationSnapshot, copyContinuationSnapshot,
  continuationContextSection, readContinuationPage, type ContinuationIdentity } from '../src/solver/continuationInput';

describe('frozen advisory continuation attachments', () => {
  let root: string, file: string, runtime: string;
  const task = 'Prove the original theorem.\nKeep all assumptions explicit.\n';
  const identity: ContinuationIdentity = { taskDigest: mathDigest(task), problemReceiptDigest: mathDigest('problem-receipt') };
  const notes = 'A previous route still needs a uniform estimate.\nThis is an unverified hypothesis.\n';
  const source = 'theorem previous_helper : True := by trivial\n';

  beforeEach(() => {
    root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'continuation-input-')));
    file = path.join(root, 'input.json'); runtime = path.join(root, 'runtime');
    fs.writeFileSync(path.join(root, 'notes.md'), notes);
    fs.writeFileSync(path.join(root, 'Previous.lean'), source);
    writeInput();
  });
  afterEach(() => fs.rmSync(root, { recursive: true, force: true }));

  function attachment(id: string, kind = 'research-notes', name = 'notes.md', text = notes) {
    return { id, kind, path: name, bytes: Buffer.byteLength(text), sha256: mathDigest(text) };
  }
  function writeInput(overrides: Record<string, unknown> = {}) {
    const input = { schema: 'theorem-os.continuation-input.v1', ...identity,
      attachments: [attachment('notes'), attachment('proof', 'proof-source', 'Previous.lean', source)], ...overrides };
    fs.writeFileSync(file, JSON.stringify(input));
    return input;
  }
  const freeze = () => freezeContinuationInput(readContinuationInput(file, identity), runtime);
  function replaceFrozen(target: string, text: string | Buffer) {
    fs.unlinkSync(target); fs.writeFileSync(target, text, { mode: 0o400 });
  }

  it('pins task, problem, complete content and advisory provenance without changing the task', () => {
    const original = fs.readFileSync(file, 'utf8'), input = readContinuationInput(file, identity), snapshot = freezeContinuationInput(input, runtime);
    expect(input.digest).toBe(snapshot.digest);
    expect(snapshot).toMatchObject({ file: path.join(runtime, 'continuation.json'), manifest: { ...identity,
      schema: 'theorem-os.continuation-snapshot.v1', attachments: [
        { id: 'notes', provenance: { evidence: 'unverified' } }, { id: 'proof', provenance: { evidence: 'unverified' } },
      ] } });
    expect(snapshot.digest).toBe(mathDigest(fs.readFileSync(snapshot.file)));
    expect(fs.readFileSync(snapshot.file, 'utf8')).toBe(canonicalMathJson(snapshot.manifest));
    expect(fs.statSync(snapshot.file).mode & 0o777).toBe(0o400);
    for (const item of snapshot.manifest.attachments) {
      const target = path.join(runtime, item.contentPath);
      expect(fs.statSync(target).mode & 0o777).toBe(0o400);
      expect(mathDigest(fs.readFileSync(target))).toBe(item.sha256);
    }
    expect(fs.readFileSync(file, 'utf8')).toBe(original);
    expect(identity.taskDigest).toBe(mathDigest(task));
    expect(freezeContinuationInput(input, runtime)).toEqual(snapshot);
  });

  it('deduplicates identical content while retaining each attachment identity and provenance', () => {
    writeInput({ attachments: [attachment('first'), { ...attachment('second'),
      provenance: { source: 'old-run/RESEARCH.md', evidence: 'recorded-not-replayed', runId: 'old-run', commit: 'a'.repeat(40) } }] });
    const snapshot = freeze();
    expect(fs.readdirSync(path.join(runtime, 'continuation'))).toEqual([`${mathDigest(notes)}.txt`]);
    expect(snapshot.manifest.attachments.map(item => item.id)).toEqual(['first', 'second']);
    expect(readContinuationPage(snapshot.file, snapshot.digest, 'second')).toMatchObject({
      text: notes, authority: 'advisory-continuation', evidence: 'recorded-not-replayed', proofAcceptance: 'not-assessed' });
  });

  it('accepts explicit absolute attachment paths and resolves relative paths beside the manifest', () => {
    writeInput({ attachments: [attachment('notes', 'research-notes', path.join(root, 'notes.md'))] });
    expect(readContinuationInput(file, identity).contents.get(mathDigest(notes))).toBe(notes);
  });

  it.each(['taskDigest', 'problemReceiptDigest'] as const)('rejects a manifest for another %s', field => {
    writeInput({ [field]: mathDigest('another-identity') });
    expect(() => readContinuationInput(file, identity)).toThrow('math_continuation_identity_changed');
  });

  it.each(['id', 'kind', 'path', 'provenance'] as const)('binds attachment %s to a separate continuation digest', field => {
    const before = readContinuationInput(file, identity).digest;
    fs.writeFileSync(path.join(root, 'same-notes.md'), notes);
    const changes = { id: 'changed-id', kind: 'diagnostics', path: 'same-notes.md',
      provenance: { evidence: 'recorded-not-replayed', source: 'different historical run' } };
    writeInput({ attachments: [{ ...attachment('notes'), [field]: changes[field] }, attachment('proof', 'proof-source', 'Previous.lean', source)] });
    expect(readContinuationInput(file, identity).digest).not.toBe(before);
  });

  it.each(['bytes', 'sha256', 'missing'])('rejects a changed or missing attachment (%s)', change => {
    if (change === 'missing') fs.unlinkSync(path.join(root, 'notes.md'));
    else writeInput({ attachments: [{ ...attachment('notes'), [change]: change === 'bytes' ? Buffer.byteLength(notes) - 1 : mathDigest('other') }] });
    expect(() => readContinuationInput(file, identity)).toThrow();
  });

  it.each([
    { schema: 'unknown' }, { unexpected: true }, { attachments: [] },
    { attachments: [attachment('same'), attachment('same')] },
    { attachments: [{ ...attachment('notes'), kind: 'instructions' }] },
    { attachments: [{ ...attachment('notes'), id: '../escape' }] },
    { attachments: [{ ...attachment('notes'), path: '\0' }] },
    { attachments: [{ ...attachment('notes'), provenance: { evidence: 'kernel-verified' } }] },
    { attachments: [{ ...attachment('notes'), proofAcceptance: 'accepted' }] },
  ])('rejects malformed or authority-claiming manifests: %j', input => {
    writeInput(input); expect(() => readContinuationInput(file, identity)).toThrow();
  });

  it('rejects malformed JSON and invalid UTF-8 while preserving a valid BOM as exact content', () => {
    fs.writeFileSync(file, '{');
    expect(() => readContinuationInput(file, identity)).toThrow('math_continuation_manifest_invalid');
    const invalid = Buffer.from([0xc3, 0x28]);
    fs.writeFileSync(path.join(root, 'notes.md'), invalid);
    writeInput({ attachments: [{ ...attachment('notes'), bytes: invalid.length, sha256: mathDigest(invalid) }] });
    expect(() => readContinuationInput(file, identity)).toThrow('math_continuation_invalid_utf8');
    const content = '\ufeffexact text\r\n';
    fs.writeFileSync(path.join(root, 'notes.md'), content);
    writeInput({ attachments: [attachment('notes', 'research-notes', 'notes.md', content)] });
    const snapshot = freeze();
    expect(readContinuationPage(snapshot.file, snapshot.digest, 'notes').text).toBe(content);
    expect(mathDigest(readContinuationPage(snapshot.file, snapshot.digest, 'notes').text)).toBe(mathDigest(content));
  });

  it.each(['manifest', 'content'] as const)('rejects a symbolic or hard-linked input %s', target => {
    const selected = target === 'manifest' ? file : path.join(root, 'notes.md'), saved = `${selected}.saved`;
    fs.renameSync(selected, saved); fs.symlinkSync(saved, selected);
    expect(() => readContinuationInput(file, identity)).toThrow();
    fs.unlinkSync(selected); fs.linkSync(saved, selected);
    expect(() => readContinuationInput(file, identity)).toThrow('math_runtime_integrity');
  });

  it('rejects an attachment beneath a symbolic directory', () => {
    fs.mkdirSync(path.join(root, 'actual')); fs.writeFileSync(path.join(root, 'actual/notes.md'), notes);
    fs.symlinkSync(path.join(root, 'actual'), path.join(root, 'linked'), 'dir');
    writeInput({ attachments: [attachment('notes', 'research-notes', 'linked/notes.md')] });
    expect(() => readContinuationInput(file, identity)).toThrow('math_path_invalid');
  });

  it('keeps frozen material usable after every original path is deleted, including worker copies and the mandatory index', () => {
    const snapshot = freeze();
    for (const name of ['input.json', 'notes.md', 'Previous.lean']) fs.unlinkSync(path.join(root, name));
    expect(readContinuationSnapshot(snapshot.file, snapshot.digest, identity)).toEqual(snapshot);
    const copied = copyContinuationSnapshot(snapshot, path.join(root, 'worker/generated/p'));
    expect(copied.file).toBe(path.join(root, 'worker/generated/p/.lake/continuation.json'));
    expect(copied.digest).toBe(snapshot.digest);
    expect(fs.readFileSync(copied.file, 'utf8')).toBe(fs.readFileSync(snapshot.file, 'utf8'));
    expect(readContinuationPage(copied.file, copied.digest, 'proof').text).toBe(source);
    expect(copyContinuationSnapshot(snapshot, path.join(root, 'worker/generated/p'))).toEqual(copied);
    const section = continuationContextSection(copied, "bun '/path with spaces/bin/math.ts'", 'generated/p');
    expect(section).toMatchObject({ id: `continuation-input:${snapshot.digest}`, kind: 'continuation' });
    const packet = JSON.parse(section.text.split('\n')[1]);
    expect(packet).toMatchObject({ authority: 'advisory-continuation', proofAcceptance: 'not-assessed', ...identity,
      snapshot: 'generated/p/.lake/continuation.json', sha256: snapshot.digest });
    expect(packet.attachments[0].readCommand).toContain(`--snapshot '${copied.file}'`);
    expect(section.text).not.toContain(notes); expect(section.text).not.toContain(source);
  });

  it('rejects changed frozen identities before supplying any body or index', () => {
    const snapshot = freeze();
    expect(() => readContinuationSnapshot(snapshot.file, mathDigest('different'), identity)).toThrow('math_continuation_identity_changed');
    expect(() => readContinuationSnapshot(snapshot.file, snapshot.digest, { ...identity, taskDigest: mathDigest('changed') }))
      .toThrow('math_continuation_identity_changed');
    expect(() => readContinuationSnapshot(snapshot.file, snapshot.digest, { ...identity, problemReceiptDigest: mathDigest('changed') }))
      .toThrow('math_continuation_identity_changed');
    replaceFrozen(snapshot.file, fs.readFileSync(snapshot.file, 'utf8') + '\n');
    expect(() => readContinuationPage(snapshot.file, snapshot.digest, 'notes')).toThrow('math_continuation_identity_changed');
    expect(() => continuationContextSection(snapshot, 'bun bin/math.ts', '.')).toThrow('math_continuation_identity_changed');
  });

  it.each(['manifest', 'content'] as const)('rejects writable or linked frozen %s files', target => {
    const snapshot = freeze(), selected = target === 'manifest' ? snapshot.file : path.join(runtime, snapshot.manifest.attachments[0].contentPath);
    fs.chmodSync(selected, 0o600);
    expect(() => readContinuationSnapshot(snapshot.file, snapshot.digest, identity)).toThrow('math_continuation_file_not_frozen');
    fs.chmodSync(selected, 0o400); fs.linkSync(selected, `${selected}.extra-link`);
    expect(() => readContinuationSnapshot(snapshot.file, snapshot.digest, identity)).toThrow('math_runtime_integrity');
    fs.unlinkSync(`${selected}.extra-link`);
    fs.renameSync(selected, `${selected}.saved`); fs.symlinkSync(`${selected}.saved`, selected);
    expect(() => readContinuationSnapshot(snapshot.file, snapshot.digest, identity)).toThrow('math_path_invalid');
  });

  it('requires every frozen body, including siblings of the attachment requested by a page reader', () => {
    const snapshot = freeze(), other = path.join(runtime, snapshot.manifest.attachments[1].contentPath);
    fs.unlinkSync(other);
    expect(() => readContinuationSnapshot(snapshot.file, snapshot.digest, identity)).toThrow();
    expect(() => readContinuationPage(snapshot.file, snapshot.digest, 'notes')).toThrow();
    expect(() => copyContinuationSnapshot(snapshot, path.join(root, 'worker'))).toThrow();
  });

  it('rejects tampered content even when its byte length and permissions are unchanged', () => {
    const snapshot = freeze(), selected = path.join(runtime, snapshot.manifest.attachments[0].contentPath);
    replaceFrozen(selected, 'x'.repeat(Buffer.byteLength(notes)));
    expect(() => readContinuationPage(snapshot.file, snapshot.digest, 'notes')).toThrow('math_continuation_content_changed');
  });

  it.each(['../notes.md', 'continuation/other.txt', `/tmp/${'a'.repeat(64)}.txt`])('refuses a self-consistent snapshot pointing outside its exact blob: %s', contentPath => {
    const snapshot = freeze();
    const forged = { ...snapshot.manifest, attachments: snapshot.manifest.attachments.map(item => ({ ...item, contentPath })) };
    const text = canonicalMathJson(forged); replaceFrozen(snapshot.file, text);
    expect(() => readContinuationSnapshot(snapshot.file, mathDigest(text))).toThrow('math_continuation_snapshot_invalid');
  });

  it('does not replace an existing different frozen snapshot or altered worker material', () => {
    const snapshot = freeze();
    writeInput({ attachments: [attachment('other')] });
    expect(() => freeze()).toThrow();
    expect(readContinuationSnapshot(snapshot.file, snapshot.digest, identity)).toEqual(snapshot);
    const copied = copyContinuationSnapshot(snapshot, path.join(root, 'worker'));
    replaceFrozen(copied.file, 'changed');
    expect(() => copyContinuationSnapshot(snapshot, path.join(root, 'worker'))).toThrow();
    expect(fs.readFileSync(copied.file, 'utf8')).toBe('changed');
  });

  it('rejects a mutated in-memory input rather than freezing altered text under the prior digest', () => {
    const input = readContinuationInput(file, identity);
    expect(() => freezeContinuationInput({ ...input, contents: new Map([[mathDigest(notes), 'changed']]) }, runtime))
      .toThrow('math_continuation_content_changed');
    expect(() => freezeContinuationInput({ ...input, digest: mathDigest('changed') }, runtime))
      .toThrow('math_continuation_identity_changed');
    expect(fs.existsSync(path.join(runtime, 'continuation.json'))).toBe(false);
  });

  it('losslessly pages escaped Unicode text with the complete serialized JSON line within its budget', () => {
    const content = ('\u{1f642}\u6c49\u5b57\n"quoted"\\\u0000\r\t').repeat(3000);
    fs.writeFileSync(path.join(root, 'notes.md'), content);
    writeInput({ attachments: [attachment('notes', 'research-notes', 'notes.md', content)] });
    const snapshot = freeze();
    let offset = 0, rebuilt = '';
    for (let count = 0; ; count++) {
      expect(count).toBeLessThan(1000);
      const page = readContinuationPage(snapshot.file, snapshot.digest, 'notes', { offset, maxBytes: 1024 });
      expect(Buffer.byteLength(JSON.stringify(page)) + 1).toBeLessThanOrEqual(1024);
      expect(page.startOffset).toBe(offset); expect(page.text).toBe(content.slice(offset, page.endOffset));
      rebuilt += page.text;
      if (!page.truncated) { expect(page.nextOffset).toBeUndefined(); break; }
      expect(page.nextOffset).toBeGreaterThan(offset); offset = page.nextOffset!;
    }
    expect(rebuilt).toBe(content);
    const page = readContinuationPage(snapshot.file, snapshot.digest, 'notes');
    expect(Buffer.byteLength(JSON.stringify(page)) + 1).toBeLessThanOrEqual(16000);
    expect(page).toMatchObject({ offsetEncoding: 'utf16-code-unit', endOffsetExclusive: true, proofAcceptance: 'not-assessed' });
  });

  it('handles empty bodies, exact end positions, unknown ids and surrogate boundaries explicitly', () => {
    const content = 'A\u{1f642}B';
    fs.writeFileSync(path.join(root, 'notes.md'), content); fs.writeFileSync(path.join(root, 'empty.md'), '');
    writeInput({ attachments: [attachment('notes', 'research-notes', 'notes.md', content), attachment('empty', 'diagnostics', 'empty.md', '')] });
    const snapshot = freeze();
    expect(readContinuationPage(snapshot.file, snapshot.digest, 'empty')).toMatchObject({ text: '', truncated: false, startOffset: 0, endOffset: 0 });
    expect(readContinuationPage(snapshot.file, snapshot.digest, 'notes', { offset: 4 })).toMatchObject({ text: '', truncated: false });
    expect(readContinuationPage(snapshot.file, snapshot.digest, 'notes', { offset: 1 }).text).toBe('\u{1f642}B');
    expect(() => readContinuationPage(snapshot.file, snapshot.digest, 'notes', { offset: 2 })).toThrow('math_continuation_read_position_invalid');
    expect(() => readContinuationPage(snapshot.file, snapshot.digest, 'notes', { offset: 5 })).toThrow('math_continuation_read_position_invalid');
    expect(() => readContinuationPage(snapshot.file, snapshot.digest, 'unknown')).toThrow('math_continuation_attachment_not_found');
  });

  it.each([{ offset: -1 }, { offset: 0.5 }, { offset: Infinity }, { maxBytes: 0 }, { maxBytes: 1023 },
    { maxBytes: 16001 }, { maxBytes: NaN }])('rejects invalid page options before reading files: %j', options => {
    expect(() => readContinuationPage('missing', mathDigest('missing'), 'notes', options)).toThrow('math_continuation_read_options_invalid');
  });

  it('exposes bounded CLI pages after original inputs are deleted and rejects missing digest, bad options and original manifests', () => {
    const snapshot = freeze();
    fs.unlinkSync(path.join(root, 'notes.md')); fs.unlinkSync(path.join(root, 'Previous.lean'));
    const cli = (args: string[]) => spawnSync('bun', ['scripts/mathematics/readContinuation.ts', ...args],
      { encoding: 'utf8', timeout: 10_000 });
    const args = ['read', '--snapshot', snapshot.file, '--sha256', snapshot.digest, '--id', 'notes', '--max-bytes', '1024'];
    const first = cli(args);
    expect(first.status, first.stderr).toBe(0); expect(Buffer.byteLength(first.stdout)).toBeLessThanOrEqual(1024);
    expect(JSON.parse(first.stdout)).toMatchObject({ text: notes, snapshotDigest: snapshot.digest, authority: 'advisory-continuation' });
    for (const bad of [args.filter((_, index) => ![3, 4].includes(index)), [...args, '--offset', '-1'],
      ['read', '--snapshot', file, '--sha256', mathDigest(fs.readFileSync(file)), '--id', 'notes'], ['write']]) {
      const result = cli(bad); expect(result.status).toBe(1); expect(result.stdout).toBe('');
    }
    expect(cli(['--help']).stdout).toContain('UTF-16');
  });
});
