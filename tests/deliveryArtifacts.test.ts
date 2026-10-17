import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { captureDeliveryArtifacts, diagnoseUnbackedLeanClaims, validateDeliveryArtifactClaims } from '../src/solver/deliveryArtifacts';
import { MAX_RESEARCH_NOTES_BYTES } from '../src/solver/deliveries';
import { git, type SolverProblem } from '../src/solver/problem';
import { taskVersion, type CooperativeTask, type TaskAssignment } from '../src/solver/tasks';

describe('recoverable advisory delivery artifacts', () => {
  let root: string, problem: SolverProblem, assignment: TaskAssignment;
  const helper = 'Submission/Helpers.lean';
  const original = 'namespace Submission\ntheorem original : True := by sorry\nend Submission\n';
  const checkpoint = () => {
    git(root, ['add', '--', '.']);
    git(root, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--quiet', '--no-gpg-sign', '--allow-empty', '-m', 'Artifact fixture']);
    return git(root, ['rev-parse', 'HEAD']);
  };
  const capture = (commit = checkpoint()) => captureDeliveryArtifacts({ problem, worktree: root, commit, assignment });
  beforeEach(() => {
    root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'delivery-artifacts-test-')));
    fs.mkdirSync(path.join(root, 'generated/p/Submission'), { recursive: true });
    fs.writeFileSync(path.join(root, 'generated/p/Submission.lean'), original);
    fs.writeFileSync(path.join(root, 'generated/p', helper), 'namespace Submission.Helpers\nend Submission.Helpers\n');
    fs.writeFileSync(path.join(root, 'RESEARCH.md'), 'Initial notes.\n');
    git(root, ['init', '--quiet']);
    const baseCommit = checkpoint();
    problem = { projectRelative: 'generated/p', ownedFiles: ['Submission.lean', helper], baseCommit,
      receiptDigest: 'same-problem-receipt' } as SolverProblem;
    const task: CooperativeTask = { id: 'unfinished', kind: 'lemma', revision: 0, dependsOn: [], objective: 'Prove the actual target',
      proofPath: helper, theoremName: 'Submission.Helpers.unfinished', type: 'True' };
    assignment = { taskId: task.id, taskDigest: taskVersion(task), seedCommit: baseCommit, workerId: 'researcher' };
  });
  afterEach(() => fs.rmSync(root, { recursive: true, force: true }));

  it('retains new supporting helpers when the assigned root is absent without granting proof acceptance', () => {
    const source = 'namespace Submission.Helpers\nlemma useful : True := by trivial\nend Submission.Helpers\n';
    fs.writeFileSync(path.join(root, 'generated/p', helper), source);
    const manifest = capture();
    expect(manifest).toMatchObject({ scope: 'advisory-unverified', problemReceiptDigest: problem.receiptDigest,
      taskId: 'unfinished', seedCommit: assignment.seedCommit });
    expect(manifest.artifacts).toHaveLength(1);
    expect(manifest.artifacts[0]).toMatchObject({ kind: 'owned-source', file: `generated/p/${helper}`,
      proofPath: helper, sha256: mathDigest(source), declarations: [{ name: 'Submission.Helpers.useful', draft: false }] });
    expect(manifest).not.toHaveProperty('evidence');
    expect(manifest.artifacts[0]).not.toHaveProperty('verified');
    expect(git(root, ['show', `${manifest.commit}:generated/p/${helper}`])).toBe(source.trim());
    expect(validateDeliveryArtifactClaims({ leanChecks: [{ status: 'passed', path: helper,
      declarations: ['Submission.Helpers.useful'], sha256: mathDigest(source) }] }, manifest)[0])
      .toMatchObject({ status: 'passed', artifactIds: [manifest.artifacts[0].id] });
  });

  it('recovers a complete Lean proposal from committed notes after temporary source restoration', () => {
    const code = 'namespace Proposal\nlemma bridge (P : Prop) (h : P) : P := by exact h\nend Proposal\n';
    const notes = '# 新证明提案\n\n```lean\n' + code + '```\n';
    fs.writeFileSync(path.join(root, 'RESEARCH.md'), notes);
    const manifest = capture(), artifact = manifest.artifacts[0];
    expect(artifact).toMatchObject({ kind: 'notes-lean', file: 'RESEARCH.md', sha256: mathDigest(code),
      fileSha256: mathDigest(notes), declarations: [{ name: 'Proposal.bridge', draft: false }] });
    expect(notes.slice(artifact.startOffset, artifact.endOffset)).toBe(code);
    expect(validateDeliveryArtifactClaims({ leanChecks: [{ status: 'passed', path: 'RESEARCH.md',
      declarations: ['Proposal.bridge'] }] }, manifest)[0].artifactIds).toEqual([artifact.id]);
    expect(fs.readFileSync(path.join(root, 'generated/p/Submission.lean'), 'utf8')).toBe(original);
  });

  it('rejects an explicit success claim whose code was restored and never retained', () => {
    fs.writeFileSync(path.join(root, 'RESEARCH.md'), 'The saved temporary Helpers check passed with exitCode 0.\n');
    const manifest = capture();
    expect(manifest.artifacts).toEqual([]);
    expect(() => validateDeliveryArtifactClaims({ leanChecks: [{ status: 'passed', path: 'RESEARCH.md',
      declarations: ['Proposal.missing'] }] }, manifest)).toThrow('math_delivery_artifact_required');
    expect(diagnoseUnbackedLeanClaims({ summary: 'Helpers check passed with exitCode 0.' }, manifest))
      .toContain('without recoverable new code');
    expect(validateDeliveryArtifactClaims({ summary: 'A mathematical route might work.' }, manifest)).toEqual([]);
    expect(diagnoseUnbackedLeanClaims({ summary: 'No Lean checks were run; this is a mathematical argument.' }, manifest)).toBeUndefined();
  });

  it('does not count an unchanged inherited proposal or placeholder as a newly retained successful proof', () => {
    const code = '```lean\nlemma placeholder : True := by sorry\n```\n';
    fs.writeFileSync(path.join(root, 'RESEARCH.md'), code);
    const first = capture();
    expect(first.artifacts[0].declarations[0].draft).toBe(true);
    expect(() => validateDeliveryArtifactClaims({ leanChecks: [{ status: 'passed', path: 'RESEARCH.md',
      declarations: ['placeholder'] }] }, first)).toThrow('math_delivery_artifact_required');
    assignment = { ...assignment, seedCommit: first.commit };
    fs.writeFileSync(path.join(root, 'RESEARCH.md'), '# Updated prose\n' + code);
    expect(capture().artifacts).toEqual([]);
  });

  it('retains a declaration moved to a different namespace despite an identical local body', () => {
    fs.writeFileSync(path.join(root, 'generated/p', helper),
      'namespace Before\nlemma useful : True := by trivial\nend Before\n');
    assignment = { ...assignment, seedCommit: checkpoint() };
    fs.writeFileSync(path.join(root, 'generated/p', helper),
      'namespace After\nlemma useful : True := by trivial\nend After\n');
    expect(capture().artifacts[0].declarations).toMatchObject([{ name: 'After.useful', draft: false }]);
  });

  it('applies the host notes byte bound before loading a committed journal', () => {
    fs.writeFileSync(path.join(root, 'RESEARCH.md'), 'x'.repeat(MAX_RESEARCH_NOTES_BYTES + 1));
    expect(() => capture()).toThrow('math_delivery_artifact_too_large');
  });

  it.each(['path', 'hash', 'name'])('rejects a claim bound to a different %s', field => {
    fs.writeFileSync(path.join(root, 'RESEARCH.md'), '```lean\nlemma retained : True := by trivial\n```\n');
    const manifest = capture();
    const claim = { status: 'passed', path: field === 'path' ? '../other/Submission.lean' : 'RESEARCH.md',
      declarations: [field === 'name' ? 'not_retained' : 'retained'],
      ...(field === 'hash' ? { sha256: '0'.repeat(64) } : {}) };
    expect(() => validateDeliveryArtifactClaims({ leanChecks: [claim] }, manifest)).toThrow('math_delivery_artifact_required');
  });

  it('does not inspect non-owned files and rejects a symlink journal without following it', () => {
    fs.writeFileSync(path.join(root, 'private-unowned.lean'), 'unowned material');
    const manifest = capture();
    expect(manifest.artifacts).toEqual([]);
    fs.rmSync(path.join(root, 'RESEARCH.md'));
    fs.symlinkSync('private-unowned.lean', path.join(root, 'RESEARCH.md'));
    expect(() => capture()).toThrow('math_delivery_artifact_not_regular_file');
  });

  it('rejects a commit without the assignment ancestry instead of importing another candidate', () => {
    const unrelated = git(root, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit-tree',
      `${assignment.seedCommit}^{tree}`, '-m', 'Unrelated root']);
    expect(() => capture(unrelated)).toThrow('math_delivery_artifact_source_unavailable');
  });

  it('permits explicit failed and inconclusive checks without a success artifact', () => {
    const manifest = capture();
    expect(validateDeliveryArtifactClaims({ leanChecks: [{ status: 'failed' }, { status: 'inconclusive' }] }, manifest))
      .toEqual([{ status: 'failed' }, { status: 'inconclusive' }]);
    expect(() => validateDeliveryArtifactClaims({ leanChecks: 'passed' }, manifest)).toThrow('math_delivery_artifact_claim_invalid');
  });
});
