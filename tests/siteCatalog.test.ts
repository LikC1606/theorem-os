import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import crypto from 'node:crypto';
import { afterEach, describe, expect, it } from 'vitest';
import { buildSiteCatalog } from '../docs/web/catalog';

const directories: string[] = [];
const revision = 'a'.repeat(40);
const sha256 = (value: string) => crypto.createHash('sha256').update(value).digest('hex');
afterEach(() => {
  for (const directory of directories.splice(0)) fs.rmSync(directory, { recursive: true, force: true });
});

function fixture() {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'theoremos-site-'));
  directories.push(root);
  const write = (file: string, value: string | object) => {
    fs.mkdirSync(path.dirname(path.join(root, file)), { recursive: true });
    fs.writeFileSync(path.join(root, file), typeof value === 'string' ? value : JSON.stringify(value));
  };
  const proof = 'theorem example : True := by trivial\n';
  const challenge = 'theorem research : True := by sorry\n';
  const runId = '145b477c-2f3c-43e2-94d1-f0de28bc6015';
  const accepted = [{
    problem_id: 'example', directory: 'example', statement_revision: 1, model: 'Original project + original model',
    status: 'official_accepted', submission_url: 'https://example.com/submission',
    result_url: 'https://example.com/result', result_reported_at: '2026-10-14T00:00:00Z',
    result_body: 'pass', original_source_url: 'https://example.com/original', original_source_commit: 'b'.repeat(40),
    source_sha256: { 'Submission.lean': sha256(proof) },
  }];
  write('accepted/accepted.json', accepted);
  write('accepted/example/Submission.lean', proof);
  write('in-progress/snapshot.json', {
    schema: 'lean-eval.in-progress-snapshot.v1', status: 'in_progress_not_officially_accepted',
    captureFinishedAt: '2026-10-15T01:00:00Z',
    problems: [{ problemId: 'research', directory: 'research', runId, phase: 'checking', turns: 2, workers: 4 }],
  });
  write('in-progress/research/manifest.json', {
    problemId: 'research', runId, status: 'in_progress_not_officially_accepted', capturedAt: '2026-10-15T00:00:00Z',
    model: 'research model', projectRelative: 'generated/research', taskStatuses: { completed: 3, blocked: 1 },
    files: [{ file: 'workers/solver/generated/research/Challenge.lean', sha256: sha256(challenge) }],
    internalNote: 'synthetic-private-fixture-marker',
  });
  write('in-progress/research/workers/solver/generated/research/Challenge.lean', challenge);
  write('in-progress/research/state.json', { kernel_verified: true, internalNote: 'synthetic-private-fixture-marker' });
  return { root, write, accepted };
}

describe('GitHub Pages archive catalog', () => {
  it('preserves provenance and keeps completed research tasks separate from official acceptance', () => {
    const { root } = fixture();
    const catalog = buildSiteCatalog(root, revision);
    const accepted = catalog.records.find(record => record.id === 'example')!;
    const research = catalog.records.find(record => record.id === 'research')!;
    expect(accepted.model).toBe('Original project + original model');
    expect(accepted.official?.resultUrl).toBe('https://example.com/result');
    expect(accepted.local).toBeUndefined();
    expect(accepted.sources[0].url).toContain(`/blob/${revision}/accepted/`);
    expect(research).toMatchObject({
      status: 'in_progress_not_officially_accepted', snapshot: { taskStatuses: { completed: 3 } },
    });
    expect(research.official).toBeUndefined();
    expect(research.local).toBeUndefined();
    expect(JSON.stringify(catalog)).not.toContain('synthetic-private-fixture-marker');
  });

  it('rejects altered accepted sources instead of presenting stale verification evidence', () => {
    const { root, write } = fixture();
    write('accepted/example/Submission.lean', 'theorem example : False := by sorry\n');
    expect(() => buildSiteCatalog(root, revision)).toThrow('Archive checksum mismatch: accepted/example/Submission.lean');
  });

  it('labels a local check of a different projection without changing the official result', () => {
    const { root, write, accepted } = fixture();
    const local = JSON.stringify({
      problem_id: 'example', source_proof_commit: 'c'.repeat(40),
      source_sha256: { 'Submission.lean': 'd'.repeat(64) },
      local_evaluation: { status: 'evaluated_passed', kernel_verified: true, official_comparator: 'official_verified' },
    });
    write('accepted/example/verification.json', local);
    write('accepted/accepted.json', [{ ...accepted[0], source_sha256: {
      ...accepted[0].source_sha256, 'verification.json': sha256(local),
    } }]);
    const record = buildSiteCatalog(root, revision).records.find(item => item.id === 'example')!;
    expect(record.status).toBe('official_accepted');
    expect(record.local).toMatchObject({ sourceBinding: 'differs', sourceProofCommit: 'c'.repeat(40) });
    expect(record.sources[0].sha256).toBe(accepted[0].source_sha256['Submission.lean']);
  });

  it('rejects a changed research source against its snapshot manifest', () => {
    const { root, write } = fixture();
    write('in-progress/research/workers/solver/generated/research/Challenge.lean', 'changed');
    expect(() => buildSiteCatalog(root, revision)).toThrow('Archive checksum mismatch: in-progress/research/');
  });

  it('rejects unsupported acceptance status and mismatched problem identity', () => {
    const { root, write, accepted } = fixture();
    write('accepted/accepted.json', [{ ...accepted[0], status: 'kernel_verified' }]);
    expect(() => buildSiteCatalog(root, revision)).toThrow();
    write('accepted/accepted.json', [{ ...accepted[0], directory: 'different_problem' }]);
    expect(() => buildSiteCatalog(root, revision)).toThrow('Archive identity mismatch');
  });
});
