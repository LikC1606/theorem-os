import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Chain

set_option Elab.async false
set_option stderrAsMessages false

namespace OAI.PolynomialVacuumBridge.Corridor

inductive Vertex where
  | up (i j : ℤ)
  | down (i j : ℤ)
  deriving DecidableEq

def adjacent : Vertex → Vertex → Prop
  | .up i j, .down k l =>
      (k = i ∧ l = j - 1) ∨ (k = i ∧ l = j) ∨ (k = i - 1 ∧ l = j)
  | .down k l, .up i j =>
      (k = i ∧ l = j - 1) ∨ (k = i ∧ l = j) ∨ (k = i - 1 ∧ l = j)
  | _, _ => False

noncomputable def layer (vertex : Vertex) : ℤ :=
  Vertex.rec (fun _ vertical => vertical) (fun _ vertical => vertical) vertex

structure BridgePath (h : ℕ) where
  vertices : List Vertex
  distinct : vertices.Nodup
  connected : vertices.IsChain adjacent
  source : vertices.head? = some (.up 0 0)
  terminal : ∃ i : ℤ, vertices.getLast? = some (.down i ((h : ℤ) - 1))
  inStrip : ∀ v ∈ vertices, 0 ≤ layer v ∧ layer v < (h : ℤ)

/-- Integer column coordinate of the frozen honeycomb vertices. -/
def bridgeBoxColumn : Vertex → ℤ
  | .up i j => 2 * i + j
  | .down i j => 2 * i + j + 1

/-- A path lies in the two-column-slab box indexed by `-R, ..., R`. -/
def bridgeInColumnBox {h : ℕ} (R : ℕ) (p : BridgePath h) : Prop :=
  ∀ v ∈ p.vertices,
    -(2 * (R : ℤ)) ≤ bridgeBoxColumn v ∧
      bridgeBoxColumn v ≤ 2 * (R : ℤ) + 1


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

/-- A nodup strip list has at most one vertex for each allowed layer-column pair.
No connectivity, source, terminal, or unproved counting estimate is used. -/
theorem bridgeVertexList_length_le_columnSet
    {h : ℕ} (vs : List Vertex) (hnodup : vs.Nodup)
    (hstrip : ∀ v ∈ vs, 0 ≤ layer v ∧ layer v < (h : ℤ))
    (columns : Finset ℤ)
    (hcolumns : ∀ v ∈ vs, bridgeBoxColumn v ∈ columns) :
    vs.length ≤ h * columns.card := by
  classical
  let image := vs.toFinset.image bridgeLayerColumnCode
  let box := (Finset.Ico (0 : ℤ) (h : ℤ)) ×ˢ columns
  have hsub : image ⊆ box := by
    intro pair hpair
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hpair
    have hvlist : v ∈ vs := List.mem_toFinset.mp hv
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Ico.mpr (hstrip v hvlist), hcolumns v hvlist⟩
  have hcard : image.card = vs.length := by
    rw [Finset.card_image_of_injective _ bridgeLayerColumnCode_injective]
    exact List.toFinset_card_of_nodup hnodup
  have hboxcard : box.card = h * columns.card := by
    simp only [box, Finset.card_product, Int.card_Ico, sub_zero, Int.toNat_natCast]
  calc
    vs.length = image.card := hcard.symm
    _ ≤ box.card := Finset.card_le_card hsub
    _ = h * columns.card := hboxcard

theorem bridgeLength_le_columnSet {h : ℕ} (p : BridgePath h)
    (columns : Finset ℤ)
    (hcolumns : ∀ v ∈ p.vertices, bridgeBoxColumn v ∈ columns) :
    p.vertices.length ≤ h * columns.card :=
  bridgeVertexList_length_le_columnSet p.vertices p.distinct p.inStrip columns hcolumns

/-- The interval may even be empty; its natural cardinality handles that case. -/
theorem bridgeLength_le_columnInterval {h : ℕ} (p : BridgePath h) (a b : ℤ)
    (hbox : ∀ v ∈ p.vertices, a ≤ bridgeBoxColumn v ∧ bridgeBoxColumn v ≤ b) :
    p.vertices.length ≤ h * (b + 1 - a).toNat := by
  have h := bridgeLength_le_columnSet p (Finset.Icc a b)
    (fun v hv => Finset.mem_Icc.mpr (hbox v hv))
  simpa only [Int.card_Icc] using h

/-- Exact geometric size bound for the already defined symmetric slab box. -/
theorem bridgeLength_le_columnBox {h : ℕ} (p : BridgePath h) (R : ℕ)
    (hbox : bridgeInColumnBox R p) :
    p.vertices.length ≤ h * (4 * R + 2) := by
  have hlength := bridgeLength_le_columnInterval p
    (-(2 * (R : ℤ))) (2 * (R : ℤ) + 1) hbox
  have hwidth : (2 * (R : ℤ) + 1 + 1 - -(2 * (R : ℤ))).toNat = 4 * R + 2 := by
    omega
  simpa only [hwidth] using hlength

/-- Index of the two-column slab containing a vertex, using integer floor division. -/
def bridgeBoxSlab (v : Vertex) : ℤ := bridgeBoxColumn v / 2

/-- A finite set of two-column slabs contains at most `2*h` vertices per slab. -/
theorem bridgeLength_le_slabSet {h : ℕ} (p : BridgePath h)
    (slabs : Finset ℤ)
    (hslabs : ∀ v ∈ p.vertices, bridgeBoxSlab v ∈ slabs) :
    p.vertices.length ≤ 2 * h * slabs.card := by
  classical
  let slots := slabs ×ˢ Finset.Ico (0 : ℤ) 2
  let columns := slots.image (fun q : ℤ × ℤ => 2 * q.1 + q.2)
  have hcolumns : ∀ v ∈ p.vertices, bridgeBoxColumn v ∈ columns := by
    intro v hv
    refine Finset.mem_image.mpr
      ⟨(bridgeBoxColumn v / 2, bridgeBoxColumn v % 2), ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨hslabs v hv, Finset.mem_Ico.mpr ⟨by omega, by omega⟩⟩
    · omega
  have hcard : columns.card ≤ slabs.card * 2 := by
    calc
      columns.card ≤ slots.card := Finset.card_image_le
      _ = slabs.card * 2 := by
        simp only [slots, Finset.card_product, Int.card_Ico]
        rfl
  calc
    p.vertices.length ≤ h * columns.card := bridgeLength_le_columnSet p columns hcolumns
    _ ≤ h * (slabs.card * 2) := Nat.mul_le_mul_left h hcard
    _ = 2 * h * slabs.card := by ac_rfl

def bridgeOccupiedSlabs {h : ℕ} (p : BridgePath h) : Finset ℤ :=
  p.vertices.toFinset.image bridgeBoxSlab

/-- In particular, a transfer encoding counting occupied slabs has this length bound. -/
theorem bridgeLength_le_occupiedSlabs {h : ℕ} (p : BridgePath h) :
    p.vertices.length ≤ 2 * h * (bridgeOccupiedSlabs p).card := by
  apply bridgeLength_le_slabSet
  intro v hv
  exact Finset.mem_image.mpr ⟨v, List.mem_toFinset.mpr hv, rfl⟩

/-- The actual maximum absolute column of a finite vertex list. -/
def bridgeColumnRadius {h : ℕ} (p : BridgePath h) : ℕ :=
  p.vertices.toFinset.sup (fun v => (bridgeBoxColumn v).natAbs)

theorem bridgeColumn_natAbs_le_radius {h : ℕ} (p : BridgePath h)
    (v : Vertex) (hv : v ∈ p.vertices) :
    (bridgeBoxColumn v).natAbs ≤ bridgeColumnRadius p :=
  Finset.le_sup (f := fun w : Vertex => (bridgeBoxColumn w).natAbs)
    (List.mem_toFinset.mpr hv)

/-- A length profile using the path's actual maximum absolute column. -/
theorem bridgeLength_le_columnRadius {h : ℕ} (p : BridgePath h) :
    p.vertices.length ≤ h * (2 * bridgeColumnRadius p + 1) := by
  have hbox : ∀ v ∈ p.vertices,
      -(bridgeColumnRadius p : ℤ) ≤ bridgeBoxColumn v ∧
        bridgeBoxColumn v ≤ (bridgeColumnRadius p : ℤ) := by
    intro v hv
    have hnat := bridgeColumn_natAbs_le_radius p v hv
    have hcast : ((bridgeBoxColumn v).natAbs : ℤ) ≤ (bridgeColumnRadius p : ℤ) := by
      omega
    have hhi := Int.le_natAbs (a := bridgeBoxColumn v)
    have hlo := Int.le_natAbs (a := -bridgeBoxColumn v)
    simp only [Int.natAbs_neg] at hlo
    constructor <;> omega
  have hlength := bridgeLength_le_columnInterval p
    (-(bridgeColumnRadius p : ℤ)) (bridgeColumnRadius p : ℤ) hbox
  have hwidth : ((bridgeColumnRadius p : ℤ) + 1 - -(bridgeColumnRadius p : ℤ)).toNat =
      2 * bridgeColumnRadius p + 1 := by omega
  simpa only [hwidth] using hlength

#print axioms bridgeLayerColumnCode_injective
#print axioms bridgeVertexList_length_le_columnSet
#print axioms bridgeLength_le_columnSet
#print axioms bridgeLength_le_columnInterval
#print axioms bridgeLength_le_columnBox
#print axioms bridgeLength_le_slabSet
#print axioms bridgeLength_le_occupiedSlabs
#print axioms bridgeColumn_natAbs_le_radius
#print axioms bridgeLength_le_columnRadius

end OAI.PolynomialVacuumBridge.Corridor
