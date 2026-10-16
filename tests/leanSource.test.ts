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
