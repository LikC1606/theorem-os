import { describe, expect, it } from 'vitest';
import { maskLeanCommentsAndStrings } from '../src/math/leanSyntax';
import {
  assertLeanEvalHoleCompleteness,
  assertLeanEvalSubmissionComplete,
  assertLeanEvalSubmissionNamespace,
  assertLeanEvalSubmissionOwned,
} from '../src/math/leanEvalSubmission';
import { inspectLeanSource } from '../src/math/verifier';

describe('Lean comment and string masking', () => {
  it('handles nested comments and escaped strings without moving source offsets', () => {
    const literal = '"/- \\"sorry\\" -- \u{1f600}"';
    const block = '/- outer\n/- inner -/ end -/';
    const line = '-- admit \u{1f600}';
    const source = `def \u03b1 := ${literal} ${block} ${line}\r\naxiom real : True`;
    const masked = maskLeanCommentsAndStrings(source);
    expect(masked).toBe(
      `def \u03b1 := ${' '.repeat(literal.length)} ${' '.repeat(8)}\n${' '.repeat(18)} ${' '.repeat(line.length)}\r\naxiom real : True`
    );
    expect(masked.length).toBe(source.length);
    expect(masked.indexOf('axiom real')).toBe(source.indexOf('axiom real'));
  });

  it.each(['-- sorry', '/- sorry /- nested -/', '"sorry \\"admit'])(
    'masks an unterminated hidden region through EOF: %s',
    hidden => {
      expect(maskLeanCommentsAndStrings(`by trivial ${hidden}`)).toBe(`by trivial ${' '.repeat(hidden.length)}`);
    }
  );

  it('counts only proof holes and axioms in visible code', () => {
    const source = [
      '-- sorry admit axiom fake',
      '/- sorry /- admit -/ axiom fake -/',
      'def message := "sorry admit axiom fake"',
      'theorem first : True := by sorry',
      'theorem second : True := by admit',
      'axiom/- comment between tokens -/ real : True',
    ].join('\n');
    expect(inspectLeanSource(source)).toEqual({ sorryCount: 1, admitCount: 1, axioms: ['real'] });
  });
});

describe('Lean-Eval submission checks', () => {
  const valid = [
    'namespace Submission -- end Submission',
    'def message : String := "theorem missing : True := by sorry"',
    '/- end Submission\n/- nested -/ theorem missing : True := by sorry -/',
    'theorem first : True := by trivial',
    'namespace Algebra',
    'theorem goal : True := by trivial',
    'end Algebra',
    'theorem fallback : True := by trivial',
    'end Submission',
  ].join('\n');

  it('preserves all exported checks, nested namespaces and basename fallback', () => {
    const names = ['first', 'Submission.Algebra.goal', 'Other.fallback'];
    expect(() => assertLeanEvalSubmissionNamespace(valid)).not.toThrow();
    expect(() => assertLeanEvalSubmissionOwned(valid)).not.toThrow();
    expect(() => assertLeanEvalHoleCompleteness(names, valid)).not.toThrow();
    expect(() => assertLeanEvalSubmissionComplete(names, valid)).not.toThrow();
  });

  it('does not accept declarations hidden in strings or comments', () => {
    expect(() => assertLeanEvalSubmissionComplete(['missing'], valid)).toThrow('missing configured holes: missing');
    expect(() => assertLeanEvalHoleCompleteness(['Algebra.missing'], valid)).toThrow('missing configured holes');
  });

  it('rejects duplicate configured declarations', () => {
    const source = `${valid}\nnamespace Submission\ntheorem first : True := by trivial\nend Submission`;
    expect(() => assertLeanEvalSubmissionComplete(['first'], source)).toThrow('more than once: Submission.first');
  });

  it('rejects declarations outside Submission even when all holes exist', () => {
    const source = `namespace Other\ndef forbidden : Nat := 0\nend Other\n${valid}`;
    expect(() => assertLeanEvalSubmissionOwned(source)).toThrow('outside the allowed Submission namespace: forbidden');
    expect(() => assertLeanEvalSubmissionComplete(['first'], source)).toThrow('outside the allowed Submission namespace');
  });

  it('requires a visible Submission namespace and configured holes', () => {
    const hidden = '-- namespace Submission\n/- end Submission -/';
    expect(() => assertLeanEvalSubmissionNamespace(hidden)).toThrow('namespace must be Submission');
    expect(() => assertLeanEvalSubmissionComplete([], valid)).toThrow('expected holes are required');
  });
});
