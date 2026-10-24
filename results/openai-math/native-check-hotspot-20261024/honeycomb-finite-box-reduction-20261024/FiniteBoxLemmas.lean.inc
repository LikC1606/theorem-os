open scoped BigOperators

/-- Integer column coordinate of the frozen honeycomb vertices. -/
def bridgeBoxColumn : Vertex → ℤ
  | .up i j => 2 * i + j
  | .down i j => 2 * i + j + 1

/-- A path lies in the two-column-slab box indexed by `-R, ..., R`. -/
def bridgeInColumnBox {h : ℕ} (R : ℕ) (p : BridgePath h) : Prop :=
  ∀ v ∈ p.vertices,
    -(2 * (R : ℤ)) ≤ bridgeBoxColumn v ∧
      bridgeBoxColumn v ≤ 2 * (R : ℤ) + 1

/-- Every finite family of finite bridge paths lies in one common column box. -/
theorem bridgeFiniteSet_commonColumnBox {h : ℕ} (s : Finset (BridgePath h)) :
    ∃ R : ℕ, ∀ p ∈ s, bridgeInColumnBox R p := by
  classical
  let radius : BridgePath h → ℕ := fun p =>
    p.vertices.toFinset.sup (fun v => (bridgeBoxColumn v).natAbs)
  let R : ℕ := s.sup radius
  refine ⟨R, ?_⟩
  intro p hp v hv
  have hpR : radius p ≤ R := Finset.le_sup hp
  have hvR : (bridgeBoxColumn v).natAbs ≤ radius p :=
    Finset.le_sup (f := fun v : Vertex => (bridgeBoxColumn v).natAbs)
      (List.mem_toFinset.mpr hv)
  have hnat : (bridgeBoxColumn v).natAbs ≤ R := hvR.trans hpR
  have hcast : ((bridgeBoxColumn v).natAbs : ℤ) ≤ (R : ℤ) := by
    exact_mod_cast hnat
  have habs : |bridgeBoxColumn v| ≤ (R : ℤ) := by
    simpa only [Int.natCast_natAbs] using hcast
  obtain ⟨hlo, hhi⟩ := abs_le.mp habs
  constructor <;> omega

/-- A bound uniform in the box radius bounds every finite bridge-family sum. -/
theorem bridgeFiniteSum_weight_le_of_uniformColumnBoxBound {h : ℕ} {K : ℝ}
    (H : ∀ (R : ℕ) (s : Finset (BridgePath h)),
      (∀ p ∈ s, bridgeInColumnBox R p) → ∑ p ∈ s, weight p ≤ K) :
    ∀ s : Finset (BridgePath h), ∑ p ∈ s, weight p ≤ K := by
  intro s
  obtain ⟨R, hR⟩ := bridgeFiniteSet_commonColumnBox s
  exact H R s hR

/-- Conditional zeroth-mass reduction. The uniform finite-box bound is an input;
this theorem does not establish that bound or any first length moment. -/
theorem bridgeSummable_weight_of_uniformColumnBoxBound {h : ℕ} {K : ℝ}
    (H : ∀ (R : ℕ) (s : Finset (BridgePath h)),
      (∀ p ∈ s, bridgeInColumnBox R p) → ∑ p ∈ s, weight p ≤ K) :
    Summable (weight (h := h)) := by
  exact summable_of_sum_le (fun p => bridgeWeight_nonneg p)
    (bridgeFiniteSum_weight_le_of_uniformColumnBoxBound H)

/-- The same still-unproved finite-box input also bounds the full bridge mass. -/
theorem bridgeMass_le_of_uniformColumnBoxBound {h : ℕ} {K : ℝ}
    (H : ∀ (R : ℕ) (s : Finset (BridgePath h)),
      (∀ p ∈ s, bridgeInColumnBox R p) → ∑ p ∈ s, weight p ≤ K) :
    bridgeMass h ≤ K := by
  exact (bridgeSummable_weight_of_uniformColumnBoxBound H).tsum_le_of_sum_le
    (bridgeFiniteSum_weight_le_of_uniformColumnBoxBound H)
