import crypto from 'node:crypto';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { describe, expect, it } from 'vitest';
import { leanReferenceCommands, parseLeanReferenceReport, parseLeanReferences, type LeanReferenceCollectionOptions } from '../src/math/leanReferences';
import { runLeanProcess } from '../src/math/mathProcess';

describe('Lean reference reports', () => {
  const marker = 'DS_REFERENCE_fixture:';
  const parse = (value: unknown) => parseLeanReferences(marker + JSON.stringify(value), marker, ['Submission.lean']);
  it('keeps statement and proof references distinct and normalizes duplicates', () => {
    expect(parse([[['N.Predicate', 'Submission.lean']], [['N.lemma', 'Submission.lean'], ['N.lemma', 'Submission.lean']]]))
      .toEqual({ statement: [{ name: 'N.Predicate', file: 'Submission.lean' }], proof: [{ name: 'N.lemma', file: 'Submission.lean' }] });
  });
  it('recognizes an explicit empty report, while missing output remains unknown', () => {
    expect(parse([[], []])).toEqual({ statement: [], proof: [] });
    expect(parseLeanReferences('', marker, ['Submission.lean'])).toBeUndefined();
  });
  it.each([null, [[], [['outside', '../other.lean']]], [[], [['', 'Submission.lean']]], [[], [['name']]], { proof: [] }])(
    'treats an incomplete or invalid report as unknown: %j', value => { expect(parse(value)).toBeUndefined(); });
  it('rejects ambiguous and oversized output', () => {
    const valid = marker + '[[],[]]';
    expect(parseLeanReferences(valid + '\n' + valid, marker, ['Submission.lean'])).toBeUndefined();
    expect(parseLeanReferences(marker + ' '.repeat(8001) + '[[],[]]', marker, ['Submission.lean'])).toBeUndefined();
  });
});

const v2 = { maxBytes: 256000, maxReferences: 4096, fuel: 2000000 };
const modules = [{ module: 'Submission', file: 'Submission.lean' }];
const marker = 'DS_REFERENCE_v2:';
const options = { ...v2, expectedTheoremName: 'N.root', expectedModules: modules };
const moduleDigest = crypto.createHash('sha256').update(JSON.stringify([['Submission', 'Submission.lean']])).digest('hex');
const report = (fields: Record<string, unknown> = {}) => ({ schema: 'theorem-os.lean-references.v2',
  theoremName: 'N.root', moduleDigest, limits: v2, complete: true, references: [[], []], ...fields });
const parseReport = (value: unknown, bound: LeanReferenceCollectionOptions = options) =>
  parseLeanReferenceReport(marker + JSON.stringify(value), marker, ['Submission.lean'], bound);

describe('explicit complete-proof reference collection', () => {
  it('preserves the exact v1 collector generator for frozen historical queries', () => {
    const legacy = JSON.stringify(leanReferenceCommands('__ROOT__', [{ module: '__MODULE__', file: '__FILE__' }], '__REFERENCES__'));
    expect(crypto.createHash('sha256').update(legacy).digest('hex'))
      .toBe('0028f365d439203c58be7985b93c4ea1d25b02ef2edd7e334abfff2939a8a778');
  });

  it('admits a complete larger report only with explicit limits and matching identities', () => {
    const references = Array.from({ length: 700 }, (_, index) => [`N.constant_${index}`, 'Submission.lean']);
    const value = report({ references: [references, []] }), text = marker + JSON.stringify(value);
    expect(Buffer.byteLength(JSON.stringify(value))).toBeGreaterThan(8000);
    expect(parseLeanReferences(text, marker, ['Submission.lean'])).toBeUndefined();
    const parsed = parseLeanReferenceReport(text, marker, ['Submission.lean'], options);
    expect(parsed.status).toBe('complete');
    if (parsed.status === 'complete') {
      expect(parsed.references.statement).toHaveLength(700);
      expect(parsed.references.statement).toContainEqual({ name: 'N.constant_699', file: 'Submission.lean' });
      expect(parsed.references.proof).toEqual([]);
    }
    expect(parseLeanReferences(text, marker, ['Submission.lean'], options)?.statement).toHaveLength(700);
  });

  it.each([
    ['traversal-budget-exhausted', 'statement', 2000001, 2000000],
    ['reference-count-limit', 'proof', 4097, 4096],
    ['output-byte-limit', 'report', 256001, 256000],
    ['proof-unavailable', 'proof', 0, 0],
  ] as const)('retains %s while withholding any partial dependency set', (reason, phase, observed, limit) => {
    const value = report({ complete: false, reason, phase, observed, limit }); delete (value as Record<string, unknown>).references;
    expect(parseReport(value)).toEqual({ status: 'unavailable', reason, phase, observed, limit });
    expect(parseLeanReferences(marker + JSON.stringify(value), marker, ['Submission.lean'], options)).toBeUndefined();
    expect(parseReport({ ...value, references: [[['Partial', 'Submission.lean']], []] }))
      .toEqual({ status: 'unavailable', reason: 'malformed-report' });
  });

  it('distinguishes absent, ambiguous, legacy unknown and malformed reports', () => {
    expect(parseLeanReferenceReport('', marker, ['Submission.lean'], options)).toEqual({ status: 'unavailable', reason: 'missing-report' });
    const line = marker + JSON.stringify(report());
    expect(parseLeanReferenceReport(line + '\n' + line, marker, ['Submission.lean'], options))
      .toEqual({ status: 'unavailable', reason: 'ambiguous-report' });
    expect(parseReport(null)).toEqual({ status: 'unavailable', reason: 'legacy-unknown' });
    expect(parseLeanReferenceReport(marker + '{', marker, ['Submission.lean'], options))
      .toEqual({ status: 'unavailable', reason: 'malformed-report' });
  });

  it('binds the theorem, complete module map and collection limits rather than accepting another query result', () => {
    for (const changes of [{ theoremName: 'Other.root' }, { moduleDigest: 'f'.repeat(64) },
      { limits: { ...v2, fuel: 1 } }]) expect(parseReport(report(changes))).toEqual({ status: 'unavailable', reason: 'identity-mismatch' });
    expect(parseReport([[], []])).toEqual({ status: 'unavailable', reason: 'identity-mismatch' });
  });

  it('normalizes both Lean JSON diagnostic envelopes without losing duplicate-report detection', () => {
    const line = marker + JSON.stringify(report({ references: [[['N.Predicate', 'Submission.lean']], []] }));
    for (const field of ['data', 'message']) {
      const parsed = parseLeanReferenceReport(JSON.stringify({ [field]: line }), marker, ['Submission.lean'], options);
      expect(parsed).toEqual({ status: 'complete', references: { statement: [{ name: 'N.Predicate', file: 'Submission.lean' }], proof: [] } });
    }
    expect(parseLeanReferenceReport(JSON.stringify({ data: line + '\n' + line }), marker, ['Submission.lean'], options))
      .toEqual({ status: 'unavailable', reason: 'ambiguous-report' });
  });

  it('applies reference-count and file boundaries to complete v2 reports before normalizing them', () => {
    const narrow = { ...options, maxReferences: 1 }, fields = { limits: { ...v2, maxReferences: 1 } };
    expect(parseReport(report({ ...fields, references: [[], [['A', 'Submission.lean'], ['B', 'Submission.lean']]] }), narrow))
      .toEqual({ status: 'unavailable', reason: 'reference-count-limit', phase: 'proof', observed: 2, limit: 1 });
    expect(parseReport(report({ references: [[], [['Outside', '../Other.lean']]] })))
      .toEqual({ status: 'unavailable', reason: 'invalid-reference' });
    expect(parseReport(report({ references: [[], [['', 'Submission.lean']]] })))
      .toEqual({ status: 'unavailable', reason: 'invalid-reference' });
  });

  it('measures output bytes rather than JavaScript string length', () => {
    const value = [Array.from({ length: 4 }, (_, index) => ['量'.repeat(800) + index, 'Submission.lean']), []];
    const text = JSON.stringify(value);
    expect(text.length).toBeLessThan(8000); expect(Buffer.byteLength(text)).toBeGreaterThan(8000);
    expect(parseLeanReferenceReport(marker + text, marker, ['Submission.lean']))
      .toEqual({ status: 'unavailable', reason: 'output-byte-limit', phase: 'report', observed: Buffer.byteLength(text), limit: 8000 });
  });

  it.each([{ fuel: -1 }, { maxBytes: 0 }, { maxReferences: Infinity }, { fuel: 1.2 }, { maxBytes: Number.MAX_SAFE_INTEGER + 1 }])(
    'rejects invalid numeric limits: %j', invalid => {
      expect(() => leanReferenceCommands('N.root', modules, marker, invalid)).toThrow('math_lean_reference_limits_invalid');
      expect(() => parseLeanReferenceReport('', marker, ['Submission.lean'], invalid)).toThrow('math_lean_reference_limits_invalid');
    });
});

const lean = path.join(os.homedir(), '.elan', 'toolchains', 'leanprover--lean4---v4.33.0', 'bin', 'lean');
it.skipIf(!fs.existsSync(lean))('collects a real large local closure, preserving bounded failure reasons and the legacy report', async () => {
  const directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'lean-references-')));
  try {
    const source = ['namespace RefFixture', 'def chain0 (n : Nat) := n',
      ...Array.from({ length: 319 }, (_, index) => `def chain${index + 1} (n : Nat) := chain${index} n`),
      'theorem root (n : Nat) : chain319 n = chain319 n := by rfl', 'axiom missing : True', 'end RefFixture'].join('\n');
    fs.writeFileSync(path.join(directory, 'Submission.lean'), source);
    const input = { cwd: directory, env: { ...process.env, LEAN_PATH: directory }, timeoutMs: Infinity, outputLimit: 2_000_000 };
    const built = await runLeanProcess(lean, ['-o', 'Submission.olean', 'Submission.lean'], input);
    expect(built.exitCode, built.stdout + built.stderr).toBe(0);
    const cases: { marker: string; root: string; options?: LeanReferenceCollectionOptions }[] = [
      { marker: 'COMPLETE:', root: 'RefFixture.root', options: v2 },
      { marker: 'LEGACY:', root: 'RefFixture.root' },
      { marker: 'TRAVERSAL:', root: 'RefFixture.root', options: { ...v2, fuel: 1 } },
      { marker: 'COUNT:', root: 'RefFixture.root', options: { ...v2, maxReferences: 3 } },
      { marker: 'BYTES:', root: 'RefFixture.root', options: { ...v2, maxBytes: 8000 } },
      { marker: 'PROOF:', root: 'RefFixture.missing', options: v2 },
      { marker: 'UNIQUE:', root: 'RefFixture.root', options: { ...v2, fuel: 400 } },
    ];
    fs.writeFileSync(path.join(directory, 'Query.lean'), ['import Lean', 'import Submission',
      ...cases.flatMap(item => leanReferenceCommands(item.root, modules, item.marker, item.options))].join('\n'));
    const checked = await runLeanProcess(lean, ['--json', 'Query.lean'], input);
    expect(checked.exitCode, checked.stdout + checked.stderr).toBe(0);
    const read = (index: number) => {
      const item = cases[index];
      return parseLeanReferenceReport(checked.stdout, item.marker, ['Submission.lean'], item.options && {
        ...item.options, expectedTheoremName: item.root, expectedModules: modules });
    };
    const complete = read(0);
    expect(complete.status).toBe('complete');
    if (complete.status === 'complete') {
      expect(complete.references.statement).toHaveLength(320); expect(complete.references.proof).toHaveLength(320);
      expect(complete.references.statement).toContainEqual({ name: 'RefFixture.chain0', file: 'Submission.lean' });
      expect(complete.references.proof).toContainEqual({ name: 'RefFixture.chain319', file: 'Submission.lean' });
    }
    expect(read(1)).toEqual({ status: 'unavailable', reason: 'legacy-unknown' });
    expect(read(2)).toEqual({ status: 'unavailable', reason: 'traversal-budget-exhausted', phase: 'statement', observed: 2, limit: 1 });
    expect(read(3)).toEqual({ status: 'unavailable', reason: 'reference-count-limit', phase: 'statement', observed: 4, limit: 3 });
    expect(read(4)).toMatchObject({ status: 'unavailable', reason: 'output-byte-limit', phase: 'report', limit: 8000 });
    expect(read(5)).toEqual({ status: 'unavailable', reason: 'proof-unavailable', phase: 'proof', observed: 0, limit: 0 });
    expect(read(6)).toEqual(complete);
  } finally { fs.rmSync(directory, { recursive: true, force: true }); }
}, 30000);
