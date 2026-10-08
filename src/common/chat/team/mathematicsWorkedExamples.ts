/** Fixed teaching resources. The host freezes these texts as ordinary authorized artifacts. */
export type MathematicsWorkedExample = Readonly<{
  id: string;
  title: string;
  purpose: string;
  body: string;
  sources: readonly string[];
}>;

const WARNING =
  "Generic teaching reconstruction, not a verified fact about the current problem or a historical account of anyone's private thinking. Recheck domain assumptions before transferring a relation. This is supplied instructional material, not evidence of autonomous discovery.";

export const MATHEMATICS_WORKED_EXAMPLES: readonly MathematicsWorkedExample[] = Object.freeze([
  Object.freeze({
    id: 'constraint-witness',
    title: 'Deriving a witness from its required equation',
    purpose:
      'Deriving a witness from its required equation: for a missing construction, read on demand to see how substitution and residual conditions determine a candidate; check applicability to this problem.',
    body: `# Deriving a witness from its required equation

${WARNING}

## Problem and candidate form
Let R be a commutative ring with identity, x in R, and r a natural number with r >= 1 and x^r = 0. Find y in R with (1+x)y = 1 and y(1+x) = 1.

Start from the required equation (1+x)y = 1. Since the given object is x and the available operations are ring operations, try a finite polynomial in x:
y = a_0 + a_1 x + ... + a_(r-1) x^(r-1), with a_k in R.
This is a justified candidate family, not a claim that every element of R is such a polynomial. The simple choice y=1 leaves residual x, so it works only when x=0; the higher-degree terms are intended to cancel this residual successively.

## Substitute and choose sufficient cancellation relations
Direct distribution gives
(1+x)y = a_0 + sum_(k=1)^(r-1) (a_k+a_(k-1)) x^k + a_(r-1) x^r.
Choose a_0=1 and a_k=-a_(k-1). These are sufficient construction conditions, not necessary or unique coefficient comparisons in an arbitrary ring: powers of x may satisfy relations. The choices give a_k=(-1)^k and
S_r = sum_(k=0)^(r-1) (-x)^k.

The full finite-sum identity, before using nilpotence, is
(1+x) S_r = 1 - (-x)^r = 1 + (-1)^(r-1) x^r.
Indeed the two sums in S_r + x S_r cancel term by term except their constant and final terms. This explains the residual rather than checking numerical samples. Since x^r=0 the residual vanishes; take y=S_r. Commutativity gives y(1+x)=(1+x)y=1.

## Boundary and concrete specialization
For r=1 the sum has only its constant term: y=1 and x=0 by the hypothesis, so both inverse equations hold. For r=3, y=1-x+x^2 and (1+x)(1-x+x^2)=1+x^3. A generic commutative-ring Lean check of this cubic identity and its inverse conclusion covers r=3 only; it is not a formal proof of the arbitrary-r finite-sum formula.

## Transfer and limits
Identify the unknown object's type, its required relation, the structural reason for a candidate family, and the conditions still unmet after substitution. Distinguish sufficient parameter choices from necessary conditions. A failed candidate does not refute its family, and a failed family does not refute the original target without a coverage argument. Do not transplant this inverse formula into a task without the required ring structure; transfer the substitution-and-residual method instead.

## Structural transfer: a general ring
Suppose the current object has only Ring structure, for example a ring of linear operators with multiplication given by composition. The element, addition, multiplication and powers correspond to those above, but arbitrary elements need not commute. A theorem stated with CommRing cannot be directly instantiated by silently supplying CommRing; its proof mechanism may nevertheless need less structure. Look for a general local theorem first, or rebuild the needed relations with exactly the available assumptions.

Keep S_r = sum_(k=0)^(r-1) (-x)^k. Distribute and cancel separately on the two sides:
(1+x) S_r = 1 - (-x)^r,
S_r (1+x) = 1 - (-x)^r.
For the left cancellation use x * (-x)^k = -(-x)^(k+1); for the right use (-x)^k * x = -(-x)^(k+1). Both follow from associativity, distributivity, negation and powers of the same element, not arbitrary mul_comm. Since (-x)^r = (-1)^r * x^r = 0, both residuals vanish. A one-sided inverse alone does not imply a two-sided inverse in an arbitrary ring: the second calculation is necessary. For r=1 the same x=0, S_r=1 boundary applies. This is the general mathematical derivation; the earlier cubic Lean fixture does not formalize this arbitrary-r finite-sum identity.

## Let an applicable library result change the plan
The immediate intent may instead be: given x^r=0 in a Ring, prove IsUnit (1+x). Search the authorized fixed local library for the concepts IsNilpotent and IsUnit, read the declaration with its section variables, then check its full type and current-context application. The checked local example is Mathlib.RingTheory.Nilpotent.Basic at revision fabf563a7c95a166b8d7b6efca11c8b4dc9d911f (Lean v4.31.0):
@IsNilpotent.isUnit_one_add : ∀ {R : Type u_1} [inst : Ring R] {r : R}, IsNilpotent r → IsUnit (1 + r).
In that environment, the actual call is:
have hnil : IsNilpotent x := ⟨r, hx⟩
exact hnil.isUnit_one_add
Here hx : x^r=0 supplies the premise without any commutativity assumption. Re-read the current fixed declaration before reuse; this recorded version is an example, not permission to change dependencies or assume a name exists elsewhere. Name resolution alone is not applicability: read the actual remaining goals and diagnostics.

For an IsUnit target, revise the proposed work from reproving a finite sum to providing hnil and directly calling the library. If the original target specifies y=S_r or particular product equalities, IsUnit alone does not prove that formula; retain and prove those exact obligations. The general Ring Lean check establishes abstract invertibility for arbitrary r, not the displayed finite-sum formula or a separate operator formalization. Share the checked current-context call and any remaining gap, not a list of names; research only the gap still needed by the unchanged target.

## Sources and scope
Independent algebraic derivation inspired by Frieder et al., Data for Mathematical Copilots, v2, section 4.4.1, https://arxiv.org/html/2412.15184v2 . The negative recurrence here follows the displayed expansion, rather than copying the inconsistent recurrence in that discussion. Motivated exposition: Rebecca Lea Morris, Motivated proofs, section 2, https://arxiv.org/html/2001.02657 . Official declaration reference: https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Nilpotent/Basic.html ; online documentation does not certify the local pinned version.
`,
    sources: Object.freeze([
      'https://arxiv.org/html/2412.15184v2',
      'https://arxiv.org/html/2001.02657',
      'https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Nilpotent/Basic.html',
    ]),
  }),
  Object.freeze({
    id: 'recursive-relation',
    title: 'Deriving a stronger relation from a recursive call',
    purpose:
      'Deriving a stronger relation from a recursive call: for a changed recursive parameter, read on demand to derive a useful invariant and its specialization; check the actual laws available.',
    body: `# Deriving a stronger relation from a recursive call

${WARNING}

## Definitions and original requirement
Let alpha be a type, op : alpha -> alpha -> alpha and e : alpha. Assume associativity op (op a b) c = op a (op b c), left identity op e a = a, and right identity op a e = a. Use these definitions:

accumulate op z [] = z
accumulate op z (x :: xs) = accumulate op (op z x) xs
reduce op e [] = e
reduce op e (x :: xs) = op x (reduce op e xs)

The initial goal is accumulate op e xs = reduce op e xs. An induction hypothesis stated only for initial value e cannot be directly applied to the recursive call with initial value op e x. Even after left identity simplifies op e x to x, the initial value is generally not e. This diagnoses the missing relation; it does not show induction is impossible.

## Form a relation that follows the changed parameter
Seek a statement about an arbitrary initial value z, with its contribution retained:
for every z, accumulate op z xs = op z (reduce op e xs).
This strengthens the auxiliary conclusion by quantifying z; it adds no assumptions to the original theorem.

Prove it by induction on xs, keeping z universally quantified in the induction hypothesis. At [], the equation is z = op z e, exactly the reverse of right identity. For x :: xs the actual calculation is
accumulate op z (x :: xs)
= accumulate op (op z x) xs
= op (op z x) (reduce op e xs)
= op z (op x (reduce op e xs))
= op z (reduce op e (x :: xs)).
The second equality applies the induction hypothesis at op z x; the third uses associativity. The generalized relation needs only associativity and right identity. Set z=e and apply left identity to obtain the initial goal.

## Reuse with a separate composition fact
A separate induction, requiring no associativity or identity laws, proves
accumulate op z (xs ++ ys) = accumulate op (accumulate op z xs) ys.
At [] both sides reduce to accumulate op z ys; at x :: xs use its induction hypothesis at op z x. Combining this with the generalized relation twice and left identity gives
accumulate op e (xs ++ ys) = op (reduce op e xs) (reduce op e ys).
Thus the two auxiliary facts have different hypotheses and can be developed independently. The definitions and laws here are exactly those of the existing composable-proof correctness fixture; that fixture is a maintainer check, not a runtime reading dependency or permission to read test files.

## Transfer and limits
Expand the actual general recursive call in the current task, identify which parameter changes, and propose a relation that survives this change. Check the base case, step and specialization back to the original target. Do not generalize every parameter mechanically. Without associativity this particular relation is not automatic, so analyze the mechanism again; failure of it does not refute the original problem. A list identity should not be copied as a solution to unrelated number theory or geometry. Transfer the changed recursive parameter and the roles of associativity and identity, not merely the word recursion; verify the corresponding operations and the return to the current target.

## Sources and scope
Self-contained derivation matching the repository's existing generic fold fixture. Motivated exposition: Rebecca Lea Morris, Motivated proofs, https://arxiv.org/html/2001.02657 . Auxiliary-result purpose: Terence Tao, Think ahead, https://terrytao.wordpress.com/career-advice/think-ahead/ . These are method references, not evidence of a model's discovery process.
`,
    sources: Object.freeze([
      'https://arxiv.org/html/2001.02657',
      'https://terrytao.wordpress.com/career-advice/think-ahead/',
    ]),
  }),
  Object.freeze({
    id: 'remove-detour',
    title: 'Removing an unnecessary global strengthening',
    purpose:
      'Removing an unnecessary global strengthening: when a chosen connection adds a difficult premise, read on demand to distinguish that route requirement from the original target and find a checked local connection.',
    body: `# Removing an unnecessary global strengthening

${WARNING}

## Original problem and a sufficient detour
Given f : Nat -> Nat, x : Nat and h : f x = 0, prove f x * f x = 0.
One sufficient route is first to prove H: for every t, f t = 0, then specialize at x. A private trial using this route can leave H as an unsolved goal. That goal was introduced by the chosen connection; a proof checker returning it does not establish that H is necessary for the original target.

## An exact obstruction to the strengthening
Take f(t)=t and x=0. Then f x=0 and f x * f x=0, but f(1)=1 is not 0. This is a witness satisfying the original hypothesis and conclusion while falsifying H. It refutes the implication from the local conditions to H, not the original target. Repeated tactic failures alone would not provide this conclusion.

## Replace the connection and finish
The original target uses only f at x. Rewrite with h:
f x * f x = 0 * 0 = 0.
This local connection is both available from the exact original assumption and sufficient for the original conclusion. It completes the problem without proving H or adding H as an assumption. Stop work that serves only the invalid strengthening; keep independently useful checked facts. The critique of H alone would not be a solution without this replacement connection.

## Transfer and limits
Locate the precise extra premise introduced by a chosen representation or connection in the actual task. Determine which part the original goal uses and propose a checkable replacement. A counterexample must satisfy all hypotheses of the implication it refutes; a counterexample to an abstraction need not refute the original problem. If no replacement or exact obstruction is known, keep uncertainty explicit and retain valid work. Do not reject a lemma because it contains the word global: global lemmas can be useful, and weaker statements or fewer subgoals are not automatically easier. Transfer the distinction between the available local condition and the global strengthening introduced by this route; inspect a library lemma's actual assumptions before deciding whether its connection is useful.

## Sources and scope
Independent elementary example illustrating Terence Tao, Think ahead, https://terrytao.wordpress.com/career-advice/think-ahead/ , and Learn the limitations of your tools, https://terrytao.wordpress.com/career-advice/learn-the-limitations-of-your-tools/ . This is a teaching reconstruction, not a historical discovery claim or an IMO reference solution.
`,
    sources: Object.freeze([
      'https://terrytao.wordpress.com/career-advice/think-ahead/',
      'https://terrytao.wordpress.com/career-advice/learn-the-limitations-of-your-tools/',
    ]),
  }),
]);
