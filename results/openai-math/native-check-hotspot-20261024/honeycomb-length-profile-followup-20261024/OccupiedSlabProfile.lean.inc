/-- The checked occupied-slab length estimate discharges every geometric
comparison premise. Only mass summability and the exact transfer encoding remain. -/
theorem bridgeFiniteBridgeSums_of_occupiedSlabMatrices
    (ι : ℕ → Type*) [∀ h, Fintype (ι h)] [∀ h, DecidableEq (ι h)]
    (A : ∀ h, Matrix (ι h) (ι h) ℝ) (u v : ∀ h, ι h → ℝ)
    (hw : ∀ h, 1 ≤ h → Summable (weight (h := h)))
    (hA : ∀ h, 1 ≤ h → ∀ i j, 0 ≤ A h i j)
    (hu : ∀ h, 1 ≤ h → ∀ i, 0 ≤ u h i)
    (hv : ∀ h, 1 ≤ h → ∀ i, 0 ≤ v h i)
    (hidentity : ∀ h, 1 ≤ h → ∀ n,
      bridgeProfileMass (fun p : BridgePath h => (bridgeOccupiedSlabs p).card) n =
        TheoremOS.FiniteMatrixFirstMoment.matrixMass (A h) (u h) (v h) n) :
    FiniteBridgeSums := by
  refine bridgeFiniteBridgeSums_of_matrixProfiles ι
    (fun h p => (bridgeOccupiedSlabs p).card) (fun h => 2 * (h : ℝ))
    A u v hw ?_ ?_ hA hu hv hidentity
  · intro h _hh
    positivity
  · intro h _hh p
    have hlength : (p.vertices.length : ℝ) ≤
        2 * (h : ℝ) * ((bridgeOccupiedSlabs p).card : ℝ) := by
      exact_mod_cast bridgeLength_le_occupiedSlabs p
    exact hlength.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right zero_le_one)
      (mul_nonneg zero_le_two (Nat.cast_nonneg h)))
