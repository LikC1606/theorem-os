Shared geometry delta only; independent auxiliary theorems, not native TaskProof acceptance or an original-goal proof. Attribution: independently developed Codex proof from the frozen canonical statement and pinned Mathlib; no publisher solution or hidden reasoning was read.

The honeycomb geometry step is now locally kernel-verified. The pair (layer, integer column) uniquely determines a Vertex, including the cross up/down case by parity. Nodup and inStrip therefore give length <= h * number_of_allowed_columns. Consequences below include the exact transfer-facing bound length <= 2*h*number_of_occupied_two-column_slabs, with bridgeBoxSlab v = bridgeBoxColumn v / 2. This handles negative columns using integer floor division. No connectivity, source/terminal, finite mass, spectral estimate, or unproved encoding premise is used for this geometric result.

Consumer interface:
  bridgeLength_le_slabSet (p : BridgePath h) (slabs : Finset Int)
    (hslabs : forall v in p.vertices, bridgeBoxSlab v in slabs) :
    p.vertices.length <= 2*h*slabs.card
  bridgeLength_le_occupiedSlabs (p : BridgePath h) :
    p.vertices.length <= 2*h*(bridgeOccupiedSlabs p).card
Here bridgeOccupiedSlabs p is exactly p.vertices.toFinset.image bridgeBoxSlab. If a transfer word scans exactly these k slabs, substitute k=(bridgeOccupiedSlabs p).card; if it scans any finite covering slab set of cardinality k, use bridgeLength_le_slabSet. The correspondence from transfer words to canonical paths, multiplicities and weights still needs its own proof.

Other proved consequences: arbitrary interval a<=column<=b gives length<=h*(b+1-a).toNat; the already defined box [-2R,2R+1] gives length<=h*(4R+2); the actual NatAbs maximum radius gives length<=h*(2*bridgeColumnRadius p+1).

Local evidence: actual Lean exit code 0 at 2026-10-24T10:12:20.395376+00:00, elapsed 2.8644451410509646 seconds. Lean 4.34.1, Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, sealed environment 2d808da67c8ab8ad74458d8a53ecc2ee8da9c63a825e0429439ebf56a9a78c87. Single thread/core, 32 GiB address-space and 32768 MiB Lean memory; maxHeartbeats=0; no wall, CPU or invocation cap. All nine new theorem axiom outputs use only propext, Classical.choice, Quot.sound (the injectivity proof omits Classical.choice); none uses sorryAx. Standalone source SHA256 4b28aaf9a6976f4985dee98f98da3fb58aa11d4b850268ac675761ffc8588fe2 (8085 bytes). Increment SHA256 c67b5cf4dabbaf84a7b3158406e055fc63442a404c6b9c16657a063e2cf2987f (6180 bytes). Validation result SHA256 3e95a31d5b92302cbcfdfdef94e90adedfd833e9d7b227710d8e0e98af30aa5f.

The inline increment assumes the exact canonical Vertex/layer/BridgePath declarations and the already shared bridgeBoxColumn/bridgeInColumnBox definitions. Add it once inside OAI.PolynomialVacuumBridge.Corridor after those definitions, preserve existing source work, and check for name collisions. If the two box definitions have not yet been merged, reuse their exact definitions from the existing finite-box reference; do not duplicate declarations or replace Submission.lean with the standalone harness. Native formal integration/acceptance must follow the normal host workflow. Do not rerun standalone Lean/Lake loops just to recheck this identical advisory.

Current substantive gaps remain the uniform finite-box total-mass bound (or equivalent input) and exact finite-state/transfer encoding with the required count/weight identity; this delta closes only the geometric length inequality. Do not infer first-moment summability or the original theorem from this geometry alone. The previously checked matrix result remains a separate reusable theorem; no matrix code is repeated here.

```lean
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
```
