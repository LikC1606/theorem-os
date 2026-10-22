import Mathlib

namespace OAI

/-! Cancellation of row ratios on a prescribed cubic fibre. -/

open scoped BigOperators Matrix

namespace HadamardSix

abbrev Index := Fin 6
abbrev Matrix6 := Matrix Index Index ℂ

def Unimodular (H : Matrix6) : Prop := ∀ i j, ‖H i j‖ = 1

def IsComplexHadamard (H : Matrix6) : Prop :=
  Unimodular H ∧ H.conjTranspose * H = (6 : ℂ) • (1 : Matrix6)

def entrywiseSquare (H : Matrix6) : Matrix6 := fun i j => H i j ^ 2

noncomputable def cubeFiber (v : Index → ℂ) (z : ℂ) : Finset Index := by
  classical
  exact Finset.univ.filter (fun i => v i ^ 3 = z)

noncomputable def rowRatio (H : Matrix6) (i j : Index) : Index → ℂ :=
  fun k => H i k * star (H j k)

lemma row_orthogonality {H : Matrix6} (hH : IsComplexHadamard H) :
    H * H.conjTranspose = (6 : ℂ) • (1 : Matrix6) := by
  have hl : ((6 : ℂ)⁻¹ • H.conjTranspose) * H = 1 := by
    rw [Matrix.smul_mul, hH.2, smul_smul]
    norm_num
  have hr := mul_eq_one_comm.mp hl
  have he := congrArg (fun M : Matrix6 ↦ (6 : ℂ) • M) hr
  simpa [Matrix.mul_smul, smul_smul] using he

lemma rowRatio_first_moment {H : Matrix6} (hH : IsComplexHadamard H)
    {i j : Index} (hij : i ≠ j) : ∑ k, rowRatio H i j k = 0 := by
  have h := congrArg (fun M : Matrix6 ↦ M i j) (row_orthogonality hH)
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, rowRatio, hij] using h

lemma rowRatio_second_moment {H : Matrix6}
    (hs : IsComplexHadamard (entrywiseSquare H))
    {i j : Index} (hij : i ≠ j) : ∑ k, rowRatio H i j k ^ 2 = 0 := by
  have h := rowRatio_first_moment hs hij
  simpa [rowRatio, entrywiseSquare, mul_pow, star_pow] using h

lemma ratio_mul_star {H : Matrix6} (hH : Unimodular H) (i j k : Index) :
    rowRatio H i j k * star (rowRatio H i j k) = 1 := by
  have hnorm : ‖rowRatio H i j k‖ = 1 := by
    simp [rowRatio, hH i k, hH j k]
  simpa [Complex.star_def, hnorm] using Complex.mul_conj' (rowRatio H i j k)

lemma cubic_star_square {z : ℂ} (hz : z * star z = 1) : z ^ 3 * (star z) ^ 2 = z := by
  calc
    z ^ 3 * (star z) ^ 2 = z * (z * star z) ^ 2 := by ring
    _ = z := by rw [hz]; ring

lemma cubic_fiber_sum_of_moments (v : Index → ℂ)
    (hu : ∀ k, v k * star (v k) = 1)
    (hfirst : ∑ k, v k = 0) (hsecond : ∑ k, v k ^ 2 = 0)
    (a b : ℂ) (hne : a ≠ b) (hab : ∀ k, v k ^ 3 = a ∨ v k ^ 3 = b) :
    ∑ k ∈ cubeFiber v a, v k = 0 := by
  classical
  have hstar : ∑ k, (star (v k)) ^ 2 = 0 := by
    simpa only [star_sum, star_pow, star_zero] using congrArg star hsecond
  have hpoint (k : Index) :
      (if v k ^ 3 = a then (a - b) * v k else 0) =
        a * (v k - b * (star (v k)) ^ 2) := by
    have hz := cubic_star_square (hu k)
    rcases hab k with ha | hb
    · rw [ite_eq_left ha]
      rw [ha] at hz
      linear_combination b * hz
    · have hna : v k ^ 3 ≠ a := by rw [hb]; exact Ne.symm hne
      rw [ite_eq_right hna]
      rw [hb] at hz
      linear_combination a * hz
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun k _ ↦ hpoint k)
  have hrhs : (∑ k, a * (v k - b * (star (v k)) ^ 2)) = 0 := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, hfirst, hstar]
    ring
  have hlhs : (a - b) * ∑ k ∈ cubeFiber v a, v k =
      ∑ k, if v k ^ 3 = a then (a - b) * v k else 0 := by
    rw [cubeFiber, Finset.mul_sum, Finset.sum_filter]
  have hmul : (a - b) * ∑ k ∈ cubeFiber v a, v k = 0 := by
    rw [hlhs, hsum, hrhs]
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hne)

lemma rowRatio_cubeFiber_sum_zero {H : Matrix6} (hH : IsComplexHadamard H)
    (hs : IsComplexHadamard (entrywiseSquare H)) {i j : Index} (hij : i ≠ j)
    (a b : ℂ) (hne : a ≠ b)
    (hab : ∀ k, rowRatio H i j k ^ 3 = a ∨ rowRatio H i j k ^ 3 = b) :
    ∑ k ∈ cubeFiber (rowRatio H i j) a, H i k * star (H j k) = 0 := by
  exact cubic_fiber_sum_of_moments (rowRatio H i j) (ratio_mul_star hH.1 i j)
    (rowRatio_first_moment hH hij) (rowRatio_second_moment hs hij) a b hne hab


end HadamardSix
end OAI
