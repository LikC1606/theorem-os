import { describe, expect, it } from 'vitest';
import {
  declarationHashes,
  hashMathFormalSourceDeclaration,
  inspectLeanDeclarationRegions,
  inspectLeanDeclarations,
  inspectScopedLeanDeclarations,
  leanDeclarationContextCommands,
} from '../src/math/leanSource';

describe('Lean declaration universe parameters', () => {
  it('keeps distinct helper names usable for lookup and duplicate detection', () => {
    const source = `namespace Submission.Helpers
theorem contDiffOn_superposition_compact_nat.{uK, uE, uF}
    {K : Type uK} (x : K) : x = x := by
  rfl
theorem contDiffOn_superposition_compact.{uK, uE, uF}
    {K : Type uK} (x : K) : x = x := by
  rfl
end Submission.Helpers
`;
    const names = ['contDiffOn_superposition_compact_nat', 'contDiffOn_superposition_compact'];
    expect(inspectLeanDeclarationRegions(source).map(region => region.name)).toEqual(names);
    expect(new Set(inspectLeanDeclarationRegions(source).map(region => region.name.split('.').at(-1))).size).toBe(2);
    for (const name of names) {
      expect(declarationHashes(source).get(name)).toMatch(/^[a-f0-9]{64}$/u);
      expect(hashMathFormalSourceDeclaration(source, `Submission.Helpers.${name}`)).toBe(declarationHashes(source).get(name));
    }
    expect(leanDeclarationContextCommands(source, 'Submission.Helpers.contDiffOn_superposition_compact')).toEqual({
      before: ['namespace Submission.Helpers'], after: ['end Submission.Helpers'],
    });
  });

  it('preserves qualified names, root qualification, Unicode and apostrophes', () => {
    const source = `namespace Outer
theorem Algebra.α'.{u} {K : Type u} (x : K) : x = x := by rfl
theorem _root_.Submission.Flow.apply'.{u} {K : Type u} (x : K) : x = x := by rfl
end Outer
`;
    expect(inspectScopedLeanDeclarations(source).map(({ name, qualifiedName }) => ({ name, qualifiedName }))).toEqual([
      { name: "Algebra.α'", qualifiedName: "Outer.Algebra.α'" },
      { name: "_root_.Submission.Flow.apply'", qualifiedName: "Submission.Flow.apply'" },
    ]);
    expect(declarationHashes(source).get("apply'")).toBe(declarationHashes(source).get("_root_.Submission.Flow.apply'"));
  });

  it('retains universe binders in the protected header while excluding proof changes', () => {
    const source = 'theorem target.{u, v} {K : Type u} (x : K) : x = x := by rfl\n';
    const hash = hashMathFormalSourceDeclaration(source, 'target');
    expect(inspectLeanDeclarations(source)[0].declarationType).toBe('target.{u, v} {K : Type u} (x : K) : x = x');
    expect(hash).toMatch(/^[a-f0-9]{64}$/u);
    expect(hashMathFormalSourceDeclaration(source.replace('.{u, v}', '.{u}'), 'target')).not.toBe(hash);
    expect(hashMathFormalSourceDeclaration(source.replace('by rfl', 'by exact rfl'), 'target')).toBe(hash);
  });

  it('leaves projections, decimals and explicit universe applications in types and bodies intact', () => {
    const source = `def Algebra.project (x : Nat × Nat) : Nat := x.1
def Algebra.decimal : Float := 1.25
theorem Algebra.target.{u} (α : Type u) : id.{u + 1} α = α := by
  rfl
`;
    const regions = inspectLeanDeclarationRegions(source);
    expect(regions.map(region => region.name)).toEqual(['Algebra.project', 'Algebra.decimal', 'Algebra.target']);
    expect(regions.map(region => source.slice(region.bodyOffset, region.endOffset).trim())).toEqual(['x.1', '1.25', 'by\n  rfl']);
    expect(regions[2].declarationType).toContain('id.{u + 1} α = α');
  });
});

describe('Lean declaration equation boundaries', () => {
  it.each([
    '|d / (q : ℝ) - d0| ≤ eta * d0 / 2',
    '|(H.edgeDensity A B : ℝ) - (G.edgeDensity A B : ℝ) / (q : ℝ)| <\n      1 / ((A.card : ℝ) * (B.card : ℝ))',
    '|D.sum (fun w => T.sum (fun t => f t *\n      (if supported w t then (1 : ℝ) else 0)))| ≤ bound',
    '|fun x => f x| = bound',
    '|λ x => f x| = bound',
  ])('keeps a line-leading absolute-value conclusion in the protected header: %s', conclusion => {
    const source = `theorem target (d : ℝ) :\n    ${conclusion} := by\n  exact proof\n`;
    const inline = source.replace(':\n    |', ': |');
    const [region] = inspectLeanDeclarationRegions(source);
    expect(region.declarationType).toBe(`target (d : ℝ) : ${conclusion.replace(/\s+/gu, ' ')}`);
    expect(source.slice(region.bodyOffset, region.endOffset).trim()).toBe('by\n  exact proof');
    const originalHash = hashMathFormalSourceDeclaration(source, 'target');
    expect(originalHash).toBe(hashMathFormalSourceDeclaration(inline, 'target'));
    expect(originalHash).not.toBe(hashMathFormalSourceDeclaration(source.replace(conclusion, 'True'), 'target'));
    expect(originalHash).toBe(hashMathFormalSourceDeclaration(source.replace('exact proof', 'exact anotherProof'), 'target'));
  });

  it('keeps an absolute-value return type before real equation clauses', () => {
    const source = `def target (x : ℝ) :
    |x| ≤ 1 → Nat → Nat
  | _, 0 => 0
  | _, n + 1 => n
theorem next : True := by trivial
`;
    const regions = inspectLeanDeclarationRegions(source);
    expect(regions.map(region => region.name)).toEqual(['target', 'next']);
    expect(regions[0].declarationType).toBe('target (x : ℝ) : |x| ≤ 1 → Nat → Nat');
    expect(source.slice(regions[0].bodyOffset, regions[0].endOffset)).toBe('| _, 0 => 0\n  | _, n + 1 => n\n');
  });

  it.each([
    '0 => 0\n  | n + 1 => n',
    '0 | 1 => 0\n  | n => n',
    '0\n  | 1 => 0\n  | n => n',
    '0 | 1\n  | 2 => 0\n  | n => n',
    'some\n      (n) => n\n  | none => 0',
    '"(=>|" => 0\n  | _ => 1',
    "'(' => 0\n  | _ => 1",
    "')' => 0\n  | _ => 1",
    "'=' => 0\n  | _ => 1",
    "'|' => 0\n  | _ => 1",
    String.raw`'\'' => 0
  | _ => 1`,
    'n /- outer /- => ( -/ nested -/ -- => [\n    => n',
  ])('preserves equation bodies with nested or quoted pattern tokens: %s', clauses => {
    const source = `def target : Nat → Nat\n  | ${clauses}\n`;
    const [region] = inspectLeanDeclarationRegions(source);
    expect(region.declarationType).toBe('target : Nat → Nat');
    expect(source.slice(region.bodyOffset, region.endOffset)).toBe(`| ${clauses}\n`);
    expect(hashMathFormalSourceDeclaration(source, 'target')).toBe(
      hashMathFormalSourceDeclaration(source.replace(/=> [01n]/gu, '=> 2'), 'target'));
  });

  it('keeps binder defaults and top-level match return types protected', () => {
    const source = `def defaulted (n : Nat := match true with
    | true => 0
    | false => 1) : Nat → Nat
  | 0 => n
  | k + 1 => k
def matched : match true with
    | true => Nat
    | false => Nat := 0
`;
    const regions = inspectLeanDeclarationRegions(source);
    expect(regions.map(region => region.name)).toEqual(['defaulted', 'matched']);
    expect(regions[0].declarationType).toBe('defaulted (n : Nat := match true with | true => 0 | false => 1) : Nat → Nat');
    expect(source.slice(regions[0].bodyOffset, regions[0].endOffset)).toBe('| 0 => n\n  | k + 1 => k\n');
    expect(regions[1].declarationType).toBe('matched : match true with | true => Nat | false => Nat');
    expect(source.slice(regions[1].bodyOffset, regions[1].endOffset).trim()).toBe('0');
  });
});
