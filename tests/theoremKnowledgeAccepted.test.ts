import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { importAcceptedKnowledge } from '../src/solver/theoremKnowledgeAccepted';
import { buildTheoremKnowledge, theoremKnowledgeStats } from '../src/solver/theoremKnowledge';

describe('accepted submission theorem knowledge', () => {
  let root: string;
  const source = 'import Mathlib\nnamespace Submission\nsection\nvariable (P : Prop)\n' +
    'def retainedDefinition : Prop := P\n' +
    'lemma retained\n    (h : P) : P := by\n  exact h\nend\nend Submission\n';
  const initialFiles: Record<string, string> = { 'Submission.lean': source,
    'Submission/Helpers.lean': 'namespace Submission.Helpers\ntheorem useful : True := by trivial\nend Submission.Helpers\n',
    'Dependencies.lean': 'def savedContext : Prop := True\n',
    'lakefile.toml': 'name = "knowledge-fixture"\n', 'lean-toolchain': 'leanprover/lean4:v4.33.0\n',
    'README.md': 'Archived fixture.\n', 'verification.json': '{"status":"passed"}\n' };
  const record = (problemId = 'example', files = initialFiles) => ({
    problem_id: problemId, directory: problemId, status: 'official_accepted',
    original_source_commit: 'a'.repeat(40), result_url: 'https://example.org/results/1',
    source_sha256: Object.fromEntries(Object.entries(files).map(([file, contents]) => [file, mathDigest(contents)])),
  });
  const save = (records: unknown[], name = 'accepted.json') => {
    const file = path.join(root, name);
    fs.writeFileSync(file, JSON.stringify(records));
    return file;
  };
  const writeFiles = (problemId = 'example', files = initialFiles) => {
    for (const [file, contents] of Object.entries(files)) {
      const absolute = path.join(root, problemId, file);
      fs.mkdirSync(path.dirname(absolute), { recursive: true });
      fs.writeFileSync(absolute, contents);
    }
  };
  beforeEach(() => {
    root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'accepted-knowledge-test-')));
    writeFiles();
  });
  afterEach(() => { vi.restoreAllMocks(); fs.rmSync(root, { recursive: true, force: true }); });

  it('retains qualified names, exact source headers and full definition context without claiming closed types or new acceptance', () => {
    const file = save([record()]), result = importAcceptedKnowledge(file);
    expect(result.skipped).toEqual([]);
    expect(result.candidates.map(item => item.name)).toEqual(['Submission.retained', 'Submission.Helpers.useful']);
    const retained = result.candidates[0]!;
    expect(retained).toMatchObject({ type: 'lemma retained\n    (h : P) : P', typeKind: 'source-header', kind: 'lemma',
      dependencies: { statement: [], proof: [], tasks: [], coverage: 'unavailable' },
      provenance: { kind: 'accepted-archive', problemId: 'example', source: file,
        sourceDigest: mathDigest(fs.readFileSync(file)), sourceCommit: 'a'.repeat(40), receiptIds: [],
        resultUrl: 'https://example.org/results/1' } });
    expect(retained.files).toEqual(Object.fromEntries(Object.entries(initialFiles)
      .filter(([name]) => name !== 'README.md' && name !== 'verification.json')));
    const base = buildTheoremKnowledge(result.candidates);
    expect(base).toMatchObject({ evidence: 'recorded-not-replayed', requiresFreshCheck: true });
    expect(base.entries[0]!.provenance[0]).not.toHaveProperty('official');
  });

  it.each(['Submission.lean', 'README.md', 'verification.json'])('checks the exact hash of %s before producing knowledge', changed => {
    const file = save([record()]);
    fs.appendFileSync(path.join(root, 'example', changed), '\nchanged\n');
    expect(() => importAcceptedKnowledge(file)).toThrow('math_knowledge_accepted_source_changed');
  });

  it('validates all records before generating any candidates', () => {
    writeFiles('later');
    const file = save([record(), record('later')]);
    fs.appendFileSync(path.join(root, 'later/Submission.lean'), '\nchanged\n');
    expect(() => importAcceptedKnowledge(file)).toThrow('math_knowledge_accepted_source_changed');
  });

  it('rejects a source hash that was computed after normalizing line endings', () => {
    const file = save([record()]);
    fs.writeFileSync(path.join(root, 'example/Submission.lean'), source.replaceAll('\n', '\r\n'));
    expect(() => importAcceptedKnowledge(file)).toThrow('math_knowledge_accepted_source_changed');
  });

  it('retains a source BOM and line endings in the complete archived byte identity', () => {
    const files = { ...initialFiles, 'Submission.lean': '\ufeff' + source.replaceAll('\n', '\r\n') };
    writeFiles('example', files);
    const file = save([record('example', files)]), result = importAcceptedKnowledge(file);
    expect(result.candidates[0]!.files['Submission.lean']).toBe(files['Submission.lean']);
    const base = buildTheoremKnowledge(result.candidates);
    const entry = base.entries.find(item => item.name === 'Submission.retained')!;
    expect(base.contexts[entry.contextDigest]!['Submission.lean']).toBe(mathDigest(Buffer.from(files['Submission.lean'])));
    expect(base.sources[base.contexts[entry.contextDigest]!['Submission.lean']!]).toBe(files['Submission.lean']);
  });

  it.each(['pending', 'evaluated_passed'])('requires a recorded official_accepted status instead of %s', status => {
    expect(() => importAcceptedKnowledge(save([{ ...record(), status }]))).toThrow('math_knowledge_accepted_manifest_invalid');
  });

  it.each(['../outside.lean', '/outside.lean', 'Solution.lean', 'Submission/Solution.lean', '.env',
    'sessions/Submission.lean', 'environment.json', 'journal.json', 'credentials.json'])
  ('rejects forbidden manifest source %s before opening archive files', forbidden => {
    const item = record(), file = save([{ ...item, source_sha256: { ...item.source_sha256, [forbidden]: 'b'.repeat(64) } }]);
    const opened = vi.spyOn(fs, 'openSync');
    expect(() => importAcceptedKnowledge(file)).toThrow('math_knowledge_accepted_forbidden_path');
    expect(opened.mock.calls.map(call => String(call[0]))).toEqual([file]);
  });

  it('rejects a symlink source before following it', () => {
    const file = save([record()]), target = path.join(root, 'example/Submission.lean');
    fs.renameSync(target, path.join(root, 'example/saved.lean'));
    fs.symlinkSync('saved.lean', target);
    const opened = vi.spyOn(fs, 'openSync');
    expect(() => importAcceptedKnowledge(file)).toThrow('math_path_invalid');
    expect(opened.mock.calls.map(call => String(call[0]))).toEqual([file]);
  });

  it('rejects a symlink directory and manifest', () => {
    const item = record(), file = save([{ ...item, directory: 'linked' }]);
    fs.symlinkSync('example', path.join(root, 'linked'));
    expect(() => importAcceptedKnowledge(file)).toThrow('math_path_invalid');
    fs.renameSync(file, path.join(root, 'saved.json'));
    fs.symlinkSync('saved.json', file);
    expect(() => importAcceptedKnowledge(file)).toThrow('math_path_invalid');
  });

  it('rejects oversized files without reading their contents', () => {
    const file = save([record()]);
    fs.truncateSync(path.join(root, 'example/Submission.lean'), 16 * 1024 * 1024 + 1);
    const opened = vi.spyOn(fs, 'openSync');
    expect(() => importAcceptedKnowledge(file)).toThrow('math_knowledge_accepted_source_too_large');
    expect(opened.mock.calls.map(call => String(call[0]))).toEqual([file]);
  });

  it('rejects invalid manifest hashes and duplicate identities', () => {
    expect(() => importAcceptedKnowledge(save([{ ...record(), source_sha256: { 'Submission.lean': 'wrong' } }])))
      .toThrow('math_knowledge_accepted_manifest_invalid');
    expect(() => importAcceptedKnowledge(save([record(), record()])))
      .toThrow('math_knowledge_accepted_duplicate_problem');
  });

  describe('locally verified submissions with pending official results', () => {
    const validation = { signatureValid: true, solverStateUnchanged: true,
      solverAndOfficialProjectionBytesIdentical: true, frozenDependencyFilesIdentical: true };
    const fixture = () => {
      const local = { evidence_file: 'verification.json', scope: 'local_official_comparator', command: 'lake test',
        exit_code: 0, receipt_id: 'local-receipt-1', checked_at: '2026-10-16T17:15:19.387Z',
        solver_commit: 'b'.repeat(40), official_projection_commit: 'c'.repeat(40), official_baseline_commit: 'd'.repeat(40),
        evidence_validation: { ...validation } };
      const files = Object.fromEntries(Object.entries(initialFiles).filter(([name]) => name !== 'README.md' && name !== 'verification.json'));
      const evidence = { schema: 'theoremos.lean-eval-submission-provenance.v1', problem: {
        problemId: 'example', statementRevision: 1, solverCommit: local.solver_commit,
        officialProjectionCommit: local.official_projection_commit,
        files: Object.fromEntries(Object.entries(files).map(([name, contents]) => [name, { sha256: mathDigest(contents), bytes: Buffer.byteLength(contents) }])),
        localEvidenceValidation: { ...validation },
        localOfficialReceipt: { receiptId: local.receipt_id, status: 'official_verified', exitCode: 0, timedOut: false,
          verifier: 'official-comparator', command: 'lake test', problemId: 'example', targetCommit: local.official_projection_commit,
          officialBaselineCommit: local.official_baseline_commit, proofHash: mathDigest(source), checkedAt: Date.parse(local.checked_at) },
      } };
      const localFiles = { ...files, 'verification.json': JSON.stringify(evidence) };
      writeFiles('example', localFiles);
      const { result_url: _result, ...item } = record('example', localFiles);
      return { record: { ...item, status: 'local_verified_pending_official', statement_revision: 1, local_verification: local }, evidence };
    };

    it('keeps local comparator history separate from official acceptance', () => {
      const local = fixture(), result = importAcceptedKnowledge(save([local.record], 'submitted.json'));
      expect(result.candidates).toHaveLength(2);
      expect(result.candidates[0]).toMatchObject({ description: expect.stringContaining('official result remains pending'),
        dependencies: { coverage: 'unavailable' }, provenance: { kind: 'local-verified-archive', receiptIds: ['local-receipt-1'],
          sourceCommit: 'a'.repeat(40), checkedCommit: 'c'.repeat(40) } });
      expect(result.candidates[0]!.provenance).not.toHaveProperty('resultUrl');
      expect(theoremKnowledgeStats(buildTheoremKnowledge(result.candidates)))
        .toMatchObject({ localVerifiedArchiveEntries: 2, acceptedArchiveEntries: 0, requiresFreshCheck: true });
    });

    it('requires a hashed verification file for local history', () => {
      const local = fixture();
      delete local.record.source_sha256['verification.json'];
      expect(() => importAcceptedKnowledge(save([local.record], 'submitted.json')))
        .toThrow('math_knowledge_local_verification_missing');
    });

    it('rejects a changed local evidence file before parsing its claims', () => {
      const local = fixture(), file = save([local.record], 'submitted.json');
      fs.appendFileSync(path.join(root, 'example/verification.json'), '\nchanged\n');
      expect(() => importAcceptedKnowledge(file)).toThrow('math_knowledge_accepted_source_changed');
    });

    it.each(['receipt_id', 'solver_commit', 'official_projection_commit', 'checked_at'])
    ('binds local manifest %s to the hashed evidence', field => {
      const local = fixture();
      if (field === 'checked_at') local.record.local_verification.checked_at = '2026-10-16T17:15:19.388Z';
      else if (field === 'receipt_id') local.record.local_verification.receipt_id = 'other-receipt';
      else local.record.local_verification[field as 'solver_commit' | 'official_projection_commit'] = 'e'.repeat(40);
      expect(() => importAcceptedKnowledge(save([local.record], 'submitted.json')))
        .toThrow('math_knowledge_local_verification_mismatch');
    });

    it.each(['sha256', 'bytes'])('binds archived source %s to local comparator evidence', field => {
      const local = fixture(), identity = local.evidence.problem.files['Submission.lean']!;
      if (field === 'sha256') identity.sha256 = '0'.repeat(64);
      else identity.bytes++;
      const evidence = JSON.stringify(local.evidence);
      fs.writeFileSync(path.join(root, 'example/verification.json'), evidence);
      local.record.source_sha256['verification.json'] = mathDigest(evidence);
      expect(() => importAcceptedKnowledge(save([local.record], 'submitted.json')))
        .toThrow('math_knowledge_local_verification_mismatch');
    });

    it('rejects failed local comparison or incomplete evidence-validation metadata', () => {
      const local = fixture();
      local.record.local_verification.evidence_validation.signatureValid = false;
      expect(() => importAcceptedKnowledge(save([local.record], 'submitted.json')))
        .toThrow('math_knowledge_accepted_manifest_invalid');
      local.record.local_verification.evidence_validation.signatureValid = true;
      local.record.local_verification.exit_code = 1;
      expect(() => importAcceptedKnowledge(save([local.record], 'submitted.json')))
        .toThrow('math_knowledge_accepted_manifest_invalid');
    });

    it('requires each archive status to match its explicit manifest type', () => {
      const local = fixture();
      expect(() => importAcceptedKnowledge(save([local.record]))).toThrow('math_knowledge_accepted_manifest_status_mismatch');
      expect(() => importAcceptedKnowledge(save([record()], 'submitted.json'))).toThrow('math_knowledge_accepted_manifest_status_mismatch');
    });
  });
});
