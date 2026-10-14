import { describe, expect, it } from 'vitest';
import type { ProofCheck } from '../src/solver/modules/evidence';
import { solverProofFeedback } from '../src/solver/feedback';

function failed(sourceDigest: string, line = 10, goal = '⊢ x > 0'): ProofCheck {
  return { passed: false, sourceDigest, verification: { status: 'failed', results: ['first', 'second'].map(theoremName => ({
    proofPath: 'Submission.lean', theoremName, status: 'failed', error: 'lean_compilation_failed',
    stdoutPreview: `Submission.lean:${line}:2: error: unsolved goals\nx : ℝ\nh : x ≥ 0\n${goal}\n`,
  })) } } as ProofCheck;
}

describe('proof progress feedback', () => {
  it('preserves coded Lean errors before their dependent unsolved goals', () => {
    const previous = failed('old-source');
    previous.verification.results.forEach(result => {
      result.stdoutPreview = 'Submission.lean:9:17: error(lean.unknownIdentifier): Unknown identifier `lower_bound`\n' + result.stdoutPreview;
    });
    const current = structuredClone(previous);
    current.sourceDigest = 'new-source';
    current.verification.results.forEach(result => { result.stdoutPreview = result.stdoutPreview!.replace(':9:17:', ':19:17:').replace(':10:2:', ':20:2:'); });
    const feedback = solverProofFeedback(current, previous);
    expect(feedback).toContain('Submission.lean:19:17: error(lean.unknownIdentifier)');
    expect(feedback.indexOf('Unknown identifier')).toBeLessThan(feedback.indexOf('unsolved goals'));
    expect(feedback).toContain('same Lean errors and goal contexts');
  });

  it('recognizes repeated errors after positions move, while preserving the current location', () => {
    const current = failed('new-source', 24);
    const feedback = solverProofFeedback(current, failed('old-source'));
    expect(feedback).toContain('same Lean errors and goal contexts');
    expect(feedback).toContain('Submission.lean:24:2: error: unsolved goals');
    expect(feedback).not.toContain('proof source is unchanged');
  });

  it('treats a changed goal or assumption as progress', () => {
    const previous = failed('old-source');
    const goal = failed('new-source', 24, '⊢ x ≥ 0');
    expect(solverProofFeedback(goal, previous)).not.toContain('same Lean errors and goal contexts');
    const assumption = failed('new-source', 24);
    assumption.verification.results.forEach(result => { result.stdoutPreview = result.stdoutPreview!.replace('h : x ≥ 0', 'h : x > 0'); });
    expect(solverProofFeedback(assumption, previous)).not.toContain('same Lean errors and goal contexts');
  });

  it('recognizes completed targets as progress despite unchanged diagnostics in another target', () => {
    const current = failed('new-source', 24);
    current.verification.results[1].status = 'kernel_verified';
    expect(solverProofFeedback(current, failed('old-source'))).not.toContain('same Lean errors and goal contexts');
  });

  it('keeps errors in different files distinct', () => {
    const current = failed('new-source');
    current.verification.results.forEach(result => { result.stdoutPreview = result.stdoutPreview!.replace('Submission.lean:', 'Helper.lean:'); });
    expect(solverProofFeedback(current, failed('old-source'))).not.toContain('same Lean errors and goal contexts');
  });

  it('does not infer repeated proof failures from missing diagnostics or infrastructure failures', () => {
    const previous = failed('old-source');
    for (const check of [previous, failed('new-source')]) {
      check.verification.results.forEach(result => { result.stdoutPreview = undefined; });
      expect(solverProofFeedback(check, previous)).not.toContain('same Lean errors and goal contexts');
    }
    const unavailable = failed('new-source');
    unavailable.verification.status = 'unavailable';
    expect(solverProofFeedback(unavailable, failed('old-source'))).not.toContain('same Lean errors and goal contexts');
  });
});
