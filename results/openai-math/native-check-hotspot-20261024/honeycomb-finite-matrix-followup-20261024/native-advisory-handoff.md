Shared advisory input for the ongoing Honeycomb finite-box route. This is a newly kernel-checked reusable finite nonnegative matrix lemma. It does not replace ongoing objectives or assume an original-goal estimate. Attribution: independent Codex helper mathematics, with no publisher solution or hidden reasoning read.

The finite-matrix Green-to-first-moment step is now supplied: for a finite state type, A entrywise nonnegative and u,v nonnegative, define c_n = u dot (A^n * v). Summable c implies Summable (fun n => (n:Real)*c_n). No irreducibility, full-matrix Green summability, trimming construction, or spectral-radius theorem is needed.

The proof is shorter than the previous proposed trim-and-contract route. It first proves a generic finite nonnegative factorization theorem: if c_(a+b) = sum_i L_a(i)R_b(i), then Summable c implies the first moment. A state with an identically zero side contributes zero; otherwise a nonzero witness from the opposite side and a shifted c series prove both sides summable. Their Cauchy products sum to (n+1)c_n. The matrix instance uses L_a=u^T A^a and R_b=A^b v. Preserve the explicit f/g arguments to summable_sum_mul_antidiagonal_of_summable_mul in the code: omitting them caused a diagnosed elaboration-inference hotspot on this fixed version.

Precise real validation: exit 0 at 2026-10-24T09:53:49.489377+00:00, 4.673376955091953 seconds, peak RSS 2290528 KiB; Lean 4.34.1, Mathlib pin d13f23b723b8a846827a245b89c10fc7d3f11612; original sealed identity 2d808da67c8ab8ad74458d8a53ecc2ee8da9c63a825e0429439ebf56a9a78c87. Invocation uses --threads=1 --memory=32768 -DautoImplicit=false -DmaxHeartbeats=0 -DmaxRecDepth=1000, with 32 GiB address space and one core, and no wall/CPU/invocation budget. Both printed theorem axiom sets are exactly propext, Classical.choice, Quot.sound. Final stdout has no error, warning or sorryAx; stderr is empty. This is local kernel evidence, not native host TaskProof acceptance. Full standalone source is 4970 bytes, SHA256 bae1606a1e3ad7675bdfa043f99d08d1e5a9fb7e822fb31612a19eec63eff33f. Host evidence index: validation/native-check-hotspot-20261024/honeycomb-finite-matrix-followup-20261024/validation-04-final-result.json.

Do not infer that a scalar Green series controls all entries of the untrimmed matrix: A=diag(1/2,2), u=v=(1,0) has summable scalar c_n=(1/2)^n but divergent second diagonal Green series 2^n. The supplied direct lemma avoids this false inference. The new theorem remains valid even with such invisible states or an empty state type.

Connection to the original goal: canonical bridgeFiniteBridgeSums_of_firstLengthWeight already reduces all six original clauses to firstLengthWeight summability. For each fixed h, an exact finite transfer encoding must identify c_k with the total original anchored BridgePath h mass of span k, and prove vertices.length <= 2*h*k. The uniform finite-box weight bound (still unproved) plus the previously delivered finite-box lemmas yields zeroth bridge mass. Exact grouping then gives summable c_k, this new lemma gives summable k*c_k, and the length bound controls finite-family firstLengthWeight sums. Root/terminal marks, cut connectivity, no cycles, no empty padding, exact multiplicity, and exact alpha^vertices.length weighting are still obligations; a model with arbitrary extra accepted walks does not suffice. Keep K_h arbitrary and unproved. No first-moment or original-goal completion should be claimed before these encoding/geometric inputs are proved.

The increment below is complete and inline. It can be inserted as its own namespace after imports and before namespace OAI in a solver's normal worktree, or placed after end OAI. The current Submission import Mathlib already contains its dependency APIs. Do not overwrite current Submission.lean from a reference snapshot. Keep existing definitions and source changes. Reuse this analysis step when useful, and spend the remaining proof work on the actual geometric/encoding inputs. Any native integration or proof acceptance must use the normal host workflow; do not start redundant standalone Lean/Lake loops merely to recheck this reference.

Increment SHA256: fa18397788fad96d9c54a45b51dc9f8aa338da30c5bd5108a0445c5437fd3fb6

```lean
namespace TheoremOS.FiniteMatrixFirstMoment

open scoped BigOperators Matrix

/-- A finite nonnegative factorization of `c (a+b)` is enough to upgrade its
zeroth moment to its first moment. States whose left or right sequence vanishes
contribute zero, so no reachability or trimming premise is required. -/
theorem summable_firstMoment_of_finite_nonneg_factorization
    {ι : Type*} [Fintype ι] {c : ℕ → ℝ} {L R : ℕ → ι → ℝ}
    (hL : ∀ n i, 0 ≤ L n i) (hR : ∀ n i, 0 ≤ R n i)
    (hfactor : ∀ a b, c (a + b) = ∑ i, L a i * R b i)
    (hc : Summable c) : Summable (fun n : ℕ => (n : ℝ) * c n) := by
  classical
  have hterm (a b : ℕ) (i : ι) : L a i * R b i ≤ c (a + b) := by
    rw [hfactor a b]
    exact Finset.single_le_sum (fun j _ => mul_nonneg (hL a j) (hR b j))
      (Finset.mem_univ i)
  have hprod (i : ι) : Summable (fun p : ℕ × ℕ => L p.1 i * R p.2 i) := by
    by_cases hzeroL : ∀ a, L a i = 0
    · simpa only [hzeroL, zero_mul] using
        (summable_zero : Summable (fun _ : ℕ × ℕ => (0 : ℝ)))
    by_cases hzeroR : ∀ b, R b i = 0
    · simpa only [hzeroR, mul_zero] using
        (summable_zero : Summable (fun _ : ℕ × ℕ => (0 : ℝ)))
    push Not at hzeroL hzeroR
    obtain ⟨a, ha⟩ := hzeroL
    obtain ⟨b, hb⟩ := hzeroR
    have hleftScaled : Summable (fun n : ℕ => L n i * R b i) :=
      Summable.of_nonneg_of_le
        (fun n => mul_nonneg (hL n i) (hR b i))
        (fun n => hterm n b i) ((summable_nat_add_iff b).2 hc)
    have hrightScaled : Summable (fun n : ℕ => L a i * R n i) := by
      refine Summable.of_nonneg_of_le
        (fun n => mul_nonneg (hL a i) (hR n i)) (fun n => hterm a n i) ?_
      simpa only [Nat.add_comm] using ((summable_nat_add_iff a).2 hc)
    have hleft : Summable (fun n : ℕ => L n i) :=
      (summable_mul_right_iff hb).1 hleftScaled
    have hright : Summable (fun n : ℕ => R n i) :=
      (summable_mul_left_iff ha).1 hrightScaled
    exact hleft.mul_of_nonneg hright (fun n => hL n i) (fun n => hR n i)
  have hconv (i : ι) :
      Summable (fun n : ℕ => ∑ p ∈ Finset.antidiagonal n, L p.1 i * R p.2 i) :=
    summable_sum_mul_antidiagonal_of_summable_mul
      (f := fun n : ℕ => L n i) (g := fun n : ℕ => R n i) (hprod i)
  have hsum : Summable
      (fun n : ℕ => ∑ i, ∑ p ∈ Finset.antidiagonal n, L p.1 i * R p.2 i) :=
    summable_sum (fun i _ => hconv i)
  have hweighted : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * c n) := by
    refine hsum.congr fun n => ?_
    rw [Finset.sum_comm]
    calc
      (∑ p ∈ Finset.antidiagonal n, ∑ i, L p.1 i * R p.2 i) =
          ∑ _p ∈ Finset.antidiagonal n, c n := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [← hfactor p.1 p.2, Finset.mem_antidiagonal.mp hp]
      _ = ((n + 1 : ℕ) : ℝ) * c n := by
        rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
  refine (hweighted.sub hc).congr fun n => ?_
  simp only [Nat.cast_add, Nat.cast_one]
  ring

/-- The scalar Green coefficients of a finite nonnegative transfer matrix. -/
def matrixMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (u v : ι → ℝ) (n : ℕ) : ℝ :=
  u ⬝ᵥ ((A ^ n) *ᵥ v)

/-- For a finite entrywise nonnegative matrix and nonnegative endpoint vectors,
summability of the single scalar Green series implies its first-moment
summability, even when invisible states have divergent matrix Green series. -/
theorem summable_matrix_firstMoment
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (u v : ι → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hc : Summable (matrixMass A u v)) :
    Summable (fun n : ℕ => (n : ℝ) * matrixMass A u v n) := by
  apply summable_firstMoment_of_finite_nonneg_factorization
    (L := fun n => u ᵥ* (A ^ n)) (R := fun n => (A ^ n) *ᵥ v)
    (hc := hc)
  · intro n i
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (hu j) (Matrix.pow_apply_nonneg hA n j i)
  · intro n i
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (Matrix.pow_apply_nonneg hA n i j) (hv j)
  · intro a b
    change u ⬝ᵥ ((A ^ (a + b)) *ᵥ v) =
      (u ᵥ* (A ^ a)) ⬝ᵥ ((A ^ b) *ᵥ v)
    rw [pow_add, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]


end TheoremOS.FiniteMatrixFirstMoment
```
