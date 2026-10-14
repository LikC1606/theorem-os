import { describe, expect, it } from 'vitest';
import { maskLeanCommentsAndStrings, maskLeanComments } from '../src/math/leanSyntax';
import {
  assertLeanEvalHoleCompleteness,
  assertLeanEvalSubmissionComplete,
  assertLeanEvalSubmissionNamespace,
  assertLeanEvalSubmissionOwned,
  resolveLeanEvalSubmissionName,
} from '../src/math/leanEvalSubmission';
import { inspectLeanSource } from '../src/math/verifier';
import { hashMathFormalSourceDeclaration, inspectLeanDeclarationRegions, leanDeclarationContextCommands } from '../src/math/leanSource';

describe('declaration type bindings', () => {
  it('keeps nested let and letI assignments inside the full protected return type', () => {
    const source = 'theorem target (n : Nat) :\n' +
      '  let k := let j := n + 1; j + 1\n' +
      '  letI : Inhabited Nat := ⟨k⟩\n' +
      '  k = n + 2 := by\n  rfl\n';
    const [region] = inspectLeanDeclarationRegions(source);
    expect(source.slice(region.bodyOffset)).toBe(' by\n  rfl\n');
    expect(region.declarationType).toContain('k = n + 2');
    expect(hashMathFormalSourceDeclaration(source, 'target')).not.toBe(
      hashMathFormalSourceDeclaration(source.replace('k = n + 2', 'k = n + 3'), 'target'));
    expect(hashMathFormalSourceDeclaration(source, 'target')).toBe(
      hashMathFormalSourceDeclaration(source.replace('by\n  rfl', 'by\n  simp'), 'target'));
  });
});

describe('Lean declaration query context', () => {
  it('preserves active namespace and notation scopes without leaking closed scopes or proof-local commands', () => {
    const source = `open Nat
section Closed
open scoped Hidden
end Closed
namespace Submission
section Active
open scoped ENNReal
theorem earlier : True := by
  open Int in
  trivial
-- open scoped Comment
theorem target : True := by trivial
end Active
end Submission
open scoped Later
`;
    expect(leanDeclarationContextCommands(source, 'Submission.target')).toEqual({
      before: ['open Nat', 'namespace Submission', 'section Active', 'open scoped ENNReal'], after: ['end Active', 'end Submission'],
    });
  });
});

describe('Lean comment and string masking', () => {
  it('preserves strings and escaped comment markers while removing nested comments', () => {
    const source = 'def label := "-- /- \\"quoted\\" -/" /- outer /- hidden -/ end -/\n-- secret\ndef next := "kept"';
    const masked = maskLeanComments(source);
    expect(masked).toContain('def label := "-- /- \\"quoted\\" -/"');
    expect(masked).toContain('def next := "kept"');
    expect(masked).not.toMatch(/outer|hidden|secret/u);
    expect(masked.length).toBe(source.length);
    expect(masked.indexOf('def next')).toBe(source.indexOf('def next'));
  });
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
  it.each(['section', 'section Local', 'noncomputable section', 'public section'])('preserves namespaces after %s ends', section => {
    const source = `namespace Submission\n${section}\ntheorem first : True := by trivial\nend${section === 'section Local' ? ' Local' : ''}\ntheorem second : True := by trivial\nend Submission`;
    expect(resolveLeanEvalSubmissionName('LeanEval.second', source)).toBe('Submission.second');
    expect(() => assertLeanEvalSubmissionComplete(['first', 'second'], source)).not.toThrow();
  });
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
