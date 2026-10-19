import { describe, expect, it } from 'vitest';
import { knowledgeGoalSurfaceShape as shape } from '../src/solver/theoremKnowledgeGoal';

function same(left: string, right: string) {
  const result = shape(left);
  expect(result).toBeDefined();
  expect(shape(right)).toBe(result);
}

describe('conservative theorem knowledge goal surfaces', () => {
  it('normalizes typed forall names, dependent types, and field receivers', () => {
    same('∀ (p : ℕ) [Fact p.Prime] (χ ψ : DirichletCharacter ℂ (p ^ 2)), χ.IsPrimitive → ¬ ψ.IsPrimitive → χ = χ',
      'forall (primeModulus : Nat) [Fact primeModulus.Prime] (firstCharacter secondCharacter : DirichletCharacter Complex (primeModulus ^ 2)), ' +
      'firstCharacter.IsPrimitive -> ¬ secondCharacter.IsPrimitive -> firstCharacter = firstCharacter');
  });

  it('normalizes nested typed sums without losing outer references', () => {
    same('∀ (p : Nat), (∑ t : Fin p, ∑ u : Fin p, F t u p) = 0',
      '∀ (modulus : Nat), (∑ outerIndex : Fin modulus, ∑ innerIndex : Fin modulus, F outerIndex innerIndex modulus) = 0');
  });

  it('keeps a sum variable out of the following parenthesized expression', () => {
    const left = shape('∀ (p : Nat), (∑ i : Fin p, F i) + i');
    expect(left).toBeDefined();
    expect(shape('∀ (n : Nat), (∑ j : Fin n, F j) + j')).not.toBe(left);
    same('∀ (p : Nat), (∑ i : Fin p, F i) + p', '∀ (n : Nat), (∑ j : Fin n, F j) + n');
  });

  it('normalizes typed products while preserving the quantifier kind', () => {
    same('∏ i : Nat, F i', '∏ index : Nat, F index');
    expect(shape('∏ i : Nat, F i')).not.toBe(shape('∑ i : Nat, F i'));
    expect(shape('∀ i : Nat, F i')).not.toBe(shape('∑ i : Nat, F i'));
  });

  it('preserves qualified constants even when their tail is a bound variable name', () => {
    same('∀ (x : Widget), x.value = Library.x', '∀ (item : Widget), item.value = Library.x');
    expect(shape('∀ (x : Widget), x.value = Library.x')).not.toBe(shape('∀ (item : Widget), item.value = Library.item'));
    expect(shape('∀ (x : Widget), _root_.Library.x = x.value')).not.toBe(shape('∀ (x : Widget), Library.x = x.value'));
  });

  it('does not confuse free-variable capture with a renamed binder', () => {
    const original = shape('∀ (x : Nat), Relation x free');
    expect(original).toBeDefined();
    expect(shape('∀ (free : Nat), Relation free free')).not.toBe(original);
  });

  it('preserves dependency links and argument order', () => {
    same('∀ (n : Nat) (x : Fin n), Relation n x', '∀ (size : Nat) (item : Fin size), Relation size item');
    expect(shape('∀ (n : Nat) (x : Fin n), Relation n x'))
      .not.toBe(shape('∀ (size : Nat) (item : Fin fixed), Relation size item'));
    expect(shape('∀ (x y : Nat), Relation x y')).not.toBe(shape('∀ (a b : Nat), Relation b a'));
  });

  it.each([
    ['∀ (x : Nat), P x', '∀ (y : Int), P y'],
    ['∀ (x : Object), P x', '∀ (y : object), P y'],
    ['∀ (x : Nat), ¬ P x', '∀ (y : Nat), P y'],
    ['∀ (x : Nat), F x = 0', '∀ (y : Nat), F y = 1'],
    ['∀ (x : Nat), x.left = x.right', '∀ (y : Nat), y.right = y.left'],
  ])('preserves types, constants and proposition structure: %s', (left, right) => {
    expect(shape(left)).toBeDefined(); expect(shape(right)).toBeDefined();
    expect(shape(right)).not.toBe(shape(left));
  });

  it('masks comments without erasing string-valued constants into a matching shape', () => {
    same('∀ (x : Nat), /- ignore "text" and ∃ y here -/ P x', '∀ (y : Nat), P y');
    expect(shape('∀ (x : Nat), P "left" x')).toBeUndefined();
    expect(shape('∀ (x : Nat), P "right" x')).toBeUndefined();
  });

  it.each([
    '∀ (x : Nat), ∀ (x : Nat), P x',
    '∀ (x x : Nat), P x',
    '∀ (x : Nat) [x : Class], P x',
    '∀ x, P x',
    '∑ x ∈ S, F x',
    '∑ x : Nat, F x = free',
    '∏ x : Nat, F x ≤ free',
    '∀ (x : Nat), ∃ y : Nat, Relation x y',
    '∀ (x : Nat), (fun x => x) x = x',
    '∀ (x : Nat), (x : Nat) → P x',
    '∀ (x : Nat), {x : Nat // P x}',
    '∀ (x : Nat), let x := 0; P x',
    '∀ (x : Nat), if P x then Q x else R x',
    '∀ (x : Nat), P «quoted» x',
    '∀ (x : Nat], P x',
    'x : Nat\n⊢ P x',
    'P x',
  ])('declines unsupported or ambiguous binding syntax: %s', goal => {
    expect(shape(goal)).toBeUndefined();
  });
});
