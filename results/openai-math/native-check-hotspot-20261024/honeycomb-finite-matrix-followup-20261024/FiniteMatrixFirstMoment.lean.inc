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
