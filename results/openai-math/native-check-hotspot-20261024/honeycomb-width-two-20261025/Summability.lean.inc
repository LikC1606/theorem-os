
lemma sqrt_three_lt_mu : Real.sqrt 3 < 2 * Real.cos (Real.pi / 8) := by
  have hsq2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have h2 : (1 : ℝ) < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hroot : Real.sqrt 3 < Real.sqrt (2 + Real.sqrt 2) :=
    Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  rw [Real.cos_pi_div_eight]
  nlinarith

lemma path_card_real (n : ℕ) (s : Finset (BridgePath 2))
    (hlen : ∀ p ∈ s, p.vertices.length = n) :
    (s.card : ℝ) ≤ 4 * Real.sqrt 3 ^ n := by
  have hcard : (s.card : ℝ) ≤ 4 * (3 : ℝ) ^ (n/2) := by
    exact_mod_cast path_card n s hlen
  have hge : (1 : ℝ) ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  calc (s.card : ℝ) ≤ 4 * (3 : ℝ) ^ (n/2) := hcard
    _ = 4 * Real.sqrt 3 ^ (2*(n/2)) := by
        rw [pow_mul,Real.sq_sqrt (by norm_num)]
    _ ≤ 4 * Real.sqrt 3 ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hge (by omega)) (by norm_num)

theorem stripGrowthAtTwo :
    ∃ C β : ℝ, 0 ≤ C ∧ 0 ≤ β ∧ β < 2 * Real.cos (Real.pi / 8) ∧
      ∀ (n : ℕ) (s : Finset (BridgePath 2)),
        (∀ p ∈ s, p.vertices.length = n) → (s.card : ℝ) ≤ C * β ^ n := by
  exact ⟨4, Real.sqrt 3, by norm_num, Real.sqrt_nonneg 3,
    sqrt_three_lt_mu, path_card_real⟩
