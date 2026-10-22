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

lemma rowRatio_cubeFiber_sum_zero {H : Matrix6} (hH : IsComplexHadamard H)
    (hs : IsComplexHadamard (entrywiseSquare H)) {i j : Index} (hij : i ≠ j)
    (a b : ℂ) (hne : a ≠ b)
    (hab : ∀ k, rowRatio H i j k ^ 3 = a ∨ rowRatio H i j k ^ 3 = b) :
    ∑ k ∈ cubeFiber (rowRatio H i j) a, H i k * star (H j k) = 0 := by
  classical
  have hrow_orthogonality : H * H.conjTranspose = (6 : ℂ) • (1 : Matrix6) := by
    have hl : ((6 : ℂ)⁻¹ • H.conjTranspose) * H = 1 := by
      rw [Matrix.smul_mul, hH.2, smul_smul]
      norm_num
    have hr : H * ((6 : ℂ)⁻¹ • H.conjTranspose) = 1 := mul_eq_one_comm.mp hl
    calc
      H * H.conjTranspose =
          (6 : ℂ) • (H * ((6 : ℂ)⁻¹ • H.conjTranspose)) := by
        rw [Matrix.mul_smul, smul_smul]
        norm_num
      _ = (6 : ℂ) • (1 : Matrix6) := by rw [hr]
  have hfirst : ∑ k, rowRatio H i j k = 0 := by
    have h := congrArg (fun M : Matrix6 ↦ M i j) hrow_orthogonality
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul] at h
    simpa [rowRatio, hij] using h
  have hsecond : ∑ k, rowRatio H i j k ^ 2 = 0 := by
    -- The first moment for the entrywise square of `H`.
    have h' : ∑ k, entrywiseSquare H i k * star (entrywiseSquare H j k) = 0 := by
      have horth : entrywiseSquare H * (entrywiseSquare H).conjTranspose =
          (6 : ℂ) • (1 : Matrix6) := by
        have hl : ((6 : ℂ)⁻¹ • (entrywiseSquare H).conjTranspose) *
            entrywiseSquare H = 1 := by
          rw [Matrix.smul_mul, hs.2, smul_smul]
          norm_num
        have hr : entrywiseSquare H *
            ((6 : ℂ)⁻¹ • (entrywiseSquare H).conjTranspose) = 1 :=
          mul_eq_one_comm.mp hl
        calc
          entrywiseSquare H * (entrywiseSquare H).conjTranspose =
              (6 : ℂ) • (entrywiseSquare H *
                ((6 : ℂ)⁻¹ • (entrywiseSquare H).conjTranspose)) := by
            rw [Matrix.mul_smul, smul_smul]
            norm_num
          _ = (6 : ℂ) • (1 : Matrix6) := by rw [hr]
      have h := congrArg (fun M : Matrix6 ↦ M i j) horth
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul] at h
      simpa [rowRatio, hij] using h
    simpa [rowRatio, entrywiseSquare, mul_pow, star_pow] using h'
  have hu : ∀ k, rowRatio H i j k * star (rowRatio H i j k) = 1 := by
    intro k
    have hnorm : ‖rowRatio H i j k‖ = 1 := by
      simp [rowRatio, hH.1 i k, hH.1 j k]
    have hsq := Complex.mul_conj' (rowRatio H i j k)
    rw [Complex.star_def, hsq, hnorm]
    norm_num
  have hmain : ∀ (v : Index → ℂ), (∀ k, v k * star (v k) = 1) →
      (∑ k, v k = 0) → (∑ k, v k ^ 2 = 0) → ∀ (c d : ℂ), c ≠ d →
      (∀ k, v k ^ 3 = c ∨ v k ^ 3 = d) →
      ∑ k ∈ cubeFiber v c, v k = 0 := by
    intro v hu hfirst hsecond c d hne hab
    have hstar : ∑ k, (star (v k)) ^ 2 = 0 := by
      simpa only [star_sum, star_pow, star_zero] using congrArg star hsecond
    have hpoint (k : Index) :
        (if v k ^ 3 = c then (c - d) * v k else 0) =
          c * (v k - d * (star (v k)) ^ 2) := by
      have hz : v k ^ 3 * (star (v k)) ^ 2 = v k := by
        have h : v k ^ 3 * (star (v k)) ^ 2 =
            v k * (v k * star (v k)) ^ 2 := by ring
        rw [h, hu k]
        ring
      rcases hab k with ha | hb
      · rw [ha] at hz
        rw [ite_eq_left ha]
        linear_combination d * hz
      · have hna : v k ^ 3 ≠ c := by rw [hb]; exact Ne.symm hne
        rw [hb] at hz
        rw [ite_eq_right hna]
        linear_combination c * hz
    have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun k _ ↦ hpoint k)
    have hrhs : (∑ k, c * (v k - d * (star (v k)) ^ 2)) = 0 := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, hfirst, hstar]
      ring
    have hlhs : (c - d) * ∑ k ∈ cubeFiber v c, v k =
        ∑ k, if v k ^ 3 = c then (c - d) * v k else 0 := by
      rw [cubeFiber, Finset.mul_sum, Finset.sum_filter]
    have hmul : (c - d) * ∑ k ∈ cubeFiber v c, v k = 0 := by
      rw [hlhs, hsum, hrhs]
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hne)
  exact hmain (rowRatio H i j) hu hfirst hsecond a b hne hab
end HadamardSix

end OAI
