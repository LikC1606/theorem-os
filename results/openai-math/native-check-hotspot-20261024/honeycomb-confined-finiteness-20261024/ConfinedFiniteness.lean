import Mathlib

set_option Elab.async false
set_option stderrAsMessages false

namespace OAI.PolynomialVacuumBridge.Corridor

inductive Vertex where
  | up (i j : ℤ)
  | down (i j : ℤ)
  deriving DecidableEq

noncomputable def position : Vertex → ℝ × ℝ
  | .up i j => ((i : ℝ) + (j : ℝ) / 2,
      ((j : ℝ) + 1 / 3) * (Real.sqrt 3 / 2))
  | .down i j => ((i : ℝ) + (j : ℝ) / 2 + 1 / 2,
      ((j : ℝ) + 2 / 3) * (Real.sqrt 3 / 2))

def adjacent : Vertex → Vertex → Prop
  | .up i j, .down k l =>
      (k = i ∧ l = j - 1) ∨ (k = i ∧ l = j) ∨ (k = i - 1 ∧ l = j)
  | .down k l, .up i j =>
      (k = i ∧ l = j - 1) ∨ (k = i ∧ l = j) ∨ (k = i - 1 ∧ l = j)
  | _, _ => False

noncomputable def criticalActivity : ℝ := (2 * Real.cos (Real.pi / 8))⁻¹
noncomputable def layer (vertex : Vertex) : ℤ :=
  Vertex.rec (fun _ vertical => vertical) (fun _ vertical => vertical) vertex

structure BridgePath (h : ℕ) where
  vertices : List Vertex
  distinct : vertices.Nodup
  connected : vertices.IsChain adjacent
  source : vertices.head? = some (.up 0 0)
  terminal : ∃ i : ℤ, vertices.getLast? = some (.down i ((h : ℤ) - 1))
  inStrip : ∀ v ∈ vertices, 0 ≤ layer v ∧ layer v < (h : ℤ)

noncomputable def weight {h : ℕ} (p : BridgePath h) : ℝ :=
  criticalActivity ^ p.vertices.length

noncomputable def firstLengthWeight {h : ℕ} (p : BridgePath h) : ℝ :=
  (p.vertices.length : ℝ) * weight p

noncomputable def bridgeMass (h : ℕ) : ℝ := ∑' p : BridgePath h, weight p
noncomputable def InLogCorridor {h : ℕ} (p : BridgePath h) : Prop :=
  ∀ v ∈ p.vertices, |(position v).1| ≤ (h : ℝ) * (Real.log (h : ℝ)) ^ 2

def ConfinedBridgePath (h : ℕ) := {p : BridgePath h // InLogCorridor p}

noncomputable def confinedMass (h : ℕ) : ℝ :=
  ∑' p : ConfinedBridgePath h, weight p.val
def FiniteBridgeSums : Prop :=
  ∀ h : ℕ, 1 ≤ h →
    Summable (weight (h := h)) ∧ Summable (firstLengthWeight (h := h)) ∧
    Summable (fun p : BridgePath h => firstLengthWeight p / bridgeMass h) ∧
    Summable (fun p : ConfinedBridgePath h => weight p.val) ∧
    Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val) ∧
    Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val / confinedMass h)


/-- Integer column coordinate of the frozen honeycomb vertices. -/
def bridgeBoxColumn : Vertex → ℤ
  | .up i j => 2 * i + j
  | .down i j => 2 * i + j + 1

/-- The frozen layer and integer column identify a honeycomb vertex uniquely. -/
noncomputable def bridgeLayerColumnCode (v : Vertex) : ℤ × ℤ :=
  (layer v, bridgeBoxColumn v)

theorem bridgeLayerColumnCode_injective :
    Function.Injective bridgeLayerColumnCode := by
  intro v w h
  cases v <;> cases w <;>
    simp only [bridgeLayerColumnCode, layer, bridgeBoxColumn, Prod.mk.injEq] at h
  · congr 1 <;> omega
  · omega
  · omega
  · congr 1 <;> omega


/-- The integer column is twice the canonical horizontal coordinate. -/
theorem bridgeBoxColumn_eq_twice_position (v : Vertex) :
    (bridgeBoxColumn v : ℝ) = 2 * (position v).1 := by
  cases v <;> simp only [bridgeBoxColumn, position, Prod.fst] <;> push_cast <;> ring

/-- Layer confinement and a fixed horizontal bound leave only finitely many vertices. -/
theorem bridgeBoundedVertices_finite (h : ℕ) (B : ℝ) :
    Set.Finite {v : Vertex |
      0 ≤ layer v ∧ layer v < (h : ℤ) ∧ |(position v).1| ≤ B} := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * B)
  have hfinite : Set.Finite
      ((Set.Ico (0 : ℤ) (h : ℤ)) ×ˢ Set.Icc (-(N : ℤ)) (N : ℤ)) :=
    (Set.finite_Ico _ _).prod (Set.finite_Icc _ _)
  apply (Set.Finite.preimage bridgeLayerColumnCode_injective.injOn hfinite).subset
  intro v hv
  have hcol : |(bridgeBoxColumn v : ℝ)| ≤ 2 * B := by
    rw [bridgeBoxColumn_eq_twice_position, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left hv.2.2 (by norm_num)
  have hcol' := abs_le.mp hcol
  have hlow : -(N : ℝ) ≤ (bridgeBoxColumn v : ℝ) := by linarith
  have hhigh : (bridgeBoxColumn v : ℝ) ≤ (N : ℝ) := by linarith
  exact ⟨⟨hv.1, hv.2.1⟩, by exact_mod_cast hlow, by exact_mod_cast hhigh⟩

/-- The actual allowed vertex type for the canonical logarithmic corridor. -/
def ConfinedBridgeVertex (h : ℕ) :=
  {v : Vertex | 0 ≤ layer v ∧ layer v < (h : ℤ) ∧
    |(position v).1| ≤ (h : ℝ) * (Real.log (h : ℝ)) ^ 2}

theorem bridgeConfinedVertex_finite (h : ℕ) : Finite (ConfinedBridgeVertex h) :=
  (bridgeBoundedVertices_finite h ((h : ℝ) * (Real.log (h : ℝ)) ^ 2)).to_subtype

/-- Keep the canonical vertex order, with its already-proved confinement attached. -/
noncomputable def bridgeConfinedVertexList {h : ℕ} (p : ConfinedBridgePath h) :
    List (ConfinedBridgeVertex h) :=
  p.val.vertices.attachWith _ (fun v hv =>
    ⟨(p.val.inStrip v hv).1, (p.val.inStrip v hv).2, p.property v hv⟩)

theorem bridgeConfinedVertexList_map_val {h : ℕ} (p : ConfinedBridgePath h) :
    (bridgeConfinedVertexList p).map Subtype.val = p.val.vertices :=
  List.attachWith_map_subtype_val _

theorem bridgeConfinedVertexList_nodup {h : ℕ} (p : ConfinedBridgePath h) :
    (bridgeConfinedVertexList p).Nodup := by
  apply List.Nodup.of_map Subtype.val
  rw [bridgeConfinedVertexList_map_val]
  exact p.val.distinct

/-- A canonical confined path is determined by its ordered confined vertex list. -/
theorem bridgeConfinedVertexList_injective (h : ℕ) :
    Function.Injective (bridgeConfinedVertexList (h := h)) := by
  intro p q heq
  apply Subtype.ext
  have hvertices : p.val.vertices = q.val.vertices := by
    simpa only [bridgeConfinedVertexList_map_val] using
      congrArg (List.map Subtype.val) heq
  cases p with
  | mk p hp =>
    cases q with
    | mk q hq =>
      cases p
      cases q
      cases hvertices
      rfl

/-- For each height, there are finitely many canonical logarithmically confined bridges.
The proof uses only the fixed geometry, strip bounds, confinement and no repeated vertices. -/
theorem bridgeConfinedPath_finite (h : ℕ) : Finite (ConfinedBridgePath h) := by
  classical
  letI := bridgeConfinedVertex_finite h
  letI := Fintype.ofFinite (ConfinedBridgeVertex h)
  let encode : ConfinedBridgePath h →
      {vs : List (ConfinedBridgeVertex h) // vs.Nodup} :=
    fun p => ⟨bridgeConfinedVertexList p, bridgeConfinedVertexList_nodup p⟩
  exact Finite.of_injective encode (fun _ _ heq =>
    bridgeConfinedVertexList_injective h (congrArg Subtype.val heq))

/-- The confined weight sum is finite without any full-strip growth hypothesis. -/
theorem bridgeConfined_summable_weight (h : ℕ) :
    Summable (fun p : ConfinedBridgePath h => weight p.val) := by
  letI := bridgeConfinedPath_finite h
  exact summable_of_finite_support (Set.toFinite _)

/-- The confined first-length weight sum is finite without any growth hypothesis. -/
theorem bridgeConfined_summable_firstLengthWeight (h : ℕ) :
    Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val) := by
  letI := bridgeConfinedPath_finite h
  exact summable_of_finite_support (Set.toFinite _)

/-- Division by the canonical confined mass also leaves a summable finite family.
No positivity assumption is needed, including at heights whose confined family is empty. -/
theorem bridgeConfined_summable_normalizedFirstLengthWeight (h : ℕ) :
    Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val / confinedMass h) := by
  letI := bridgeConfinedPath_finite h
  exact summable_of_finite_support (Set.toFinite _)

/-- The last three clauses of the official six-clause target, unconditionally for every height. -/
theorem bridgeConfined_sums (h : ℕ) :
    Summable (fun p : ConfinedBridgePath h => weight p.val) ∧
    Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val) ∧
    Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val / confinedMass h) :=
  ⟨bridgeConfined_summable_weight h, bridgeConfined_summable_firstLengthWeight h,
    bridgeConfined_summable_normalizedFirstLengthWeight h⟩

#print axioms bridgeBoxColumn_eq_twice_position
#print axioms bridgeBoundedVertices_finite
#print axioms bridgeConfinedVertex_finite
#print axioms bridgeConfinedVertexList_map_val
#print axioms bridgeConfinedVertexList_nodup
#print axioms bridgeConfinedVertexList_injective
#print axioms bridgeConfinedPath_finite
#print axioms bridgeConfined_summable_weight
#print axioms bridgeConfined_summable_firstLengthWeight
#print axioms bridgeConfined_summable_normalizedFirstLengthWeight
#print axioms bridgeConfined_sums

end OAI.PolynomialVacuumBridge.Corridor
