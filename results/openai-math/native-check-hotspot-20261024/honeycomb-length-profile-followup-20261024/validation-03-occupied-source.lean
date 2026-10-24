import VerifiedContext
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Int.Interval

set_option Elab.async false
set_option stderrAsMessages false

namespace TheoremOS.ProfileSummability

open scoped BigOperators

/-- The real mass of an exact profile fiber. Its use as a coefficient requires
fiber convergence; the theorems below derive it from whole-family summability
or request `HasSum`, rather than relying on a possibly divergent `tsum`. -/
noncomputable def fiberMass {α : Type*} (w : α → ℝ) (profile : α → ℕ) (n : ℕ) : ℝ :=
  ∑' a : {a : α // profile a = n}, w a.val

theorem summable_fiberMass_of_summable
    {α : Type*} {w : α → ℝ} (profile : α → ℕ) (hw : Summable w) :
    Summable (fiberMass w profile) := by
  exact (hw.hasSum.tsum_fiberwise profile).summable


/-- Exact convergent fiber sums may be lifted through any nonnegative profile
multiplier. Fibers may be infinite; each is required to have the stated sum. -/
theorem summable_profileScale_of_hasSum
    {α : Type*} {w : α → ℝ} {profile : α → ℕ} {c scale : ℕ → ℝ}
    (hw : ∀ a, 0 ≤ w a) (hscale : ∀ n, 0 ≤ scale n)
    (hfiber : ∀ n, HasSum (fun a : {a : α // profile a = n} => w a.val) (c n))
    (hc : Summable (fun n => scale n * c n)) :
    Summable (fun a => scale (profile a) * w a) := by
  let f : (Σ n : ℕ, {a : α // profile a = n}) → ℝ :=
    fun p => scale p.1 * w p.2.val
  have hscaled (n : ℕ) :
      HasSum (fun a : {a : α // profile a = n} => scale n * w a.val)
        (scale n * c n) := (hfiber n).mul_left (scale n)
  have hsigma : Summable f :=
    (summable_sigma_of_nonneg (f := f)
      (fun p => mul_nonneg (hscale p.1) (hw p.2.val))).2
      ⟨fun n => (hscaled n).summable,
        hc.congr (fun n => (hscaled n).tsum_eq.symm)⟩
  have hreindex : Summable
      (fun p : Σ n : ℕ, {a : α // profile a = n} =>
        scale (profile p.2.val) * w p.2.val) := by
    refine hsigma.congr fun p => ?_
    change scale p.1 * w p.2.val = scale (profile p.2.val) * w p.2.val
    rw [p.2.property]
  exact (Equiv.sigmaFiberEquiv profile).summable_iff.mp hreindex


/-- A first moment in an arbitrary natural profile dominates a size moment
whenever `size <= C * (profile+1)`. The shift handles zero/offset profiles. -/
theorem summable_sizeWeight_of_hasSum
    {α : Type*} {w : α → ℝ} {size profile : α → ℕ} {c : ℕ → ℝ} {C : ℝ}
    (hw : ∀ a, 0 ≤ w a) (hC : 0 ≤ C)
    (hsize : ∀ a, (size a : ℝ) ≤ C * ((profile a : ℝ) + 1))
    (hfiber : ∀ n, HasSum (fun a : {a : α // profile a = n} => w a.val) (c n))
    (hc : Summable c) (hmoment : Summable (fun n : ℕ => (n : ℝ) * c n)) :
    Summable (fun a => (size a : ℝ) * w a) := by
  have hshift : Summable (fun n : ℕ => C * ((n : ℝ) + 1) * c n) := by
    refine ((hmoment.add hc).mul_left C).congr fun n => ?_
    ring
  have hscale : ∀ n : ℕ, 0 ≤ C * ((n : ℝ) + 1) :=
    fun n => mul_nonneg hC (add_nonneg (Nat.cast_nonneg n) zero_le_one)
  have hdom : Summable (fun a => C * ((profile a : ℝ) + 1) * w a) :=
    summable_profileScale_of_hasSum (w := w) (profile := profile) (c := c)
      (scale := fun n => C * ((n : ℝ) + 1)) hw hscale hfiber hshift
  exact Summable.of_nonneg_of_le
    (fun a => mul_nonneg (Nat.cast_nonneg _) (hw a))
    (fun a => mul_le_mul_of_nonneg_right (hsize a) (hw a)) hdom


end TheoremOS.ProfileSummability

namespace OAI.PolynomialVacuumBridge.Corridor

open scoped BigOperators Matrix

/-- Exact bridge mass in a caller-chosen profile fiber; the transfer exponent
may be occupied slab span, rather than the path's vertex length. -/
noncomputable def bridgeProfileMass {h : ℕ}
    (profile : BridgePath h → ℕ) (n : ℕ) : ℝ :=
  TheoremOS.ProfileSummability.fiberMass (weight (h := h)) profile n

theorem bridgeSummable_firstLengthWeight_of_profileFirstMoment
    {h : ℕ} (profile : BridgePath h → ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hsize : ∀ p : BridgePath h,
      (p.vertices.length : ℝ) ≤ C * ((profile p : ℝ) + 1))
    (hw : Summable (weight (h := h)))
    (hmoment : Summable (fun n : ℕ => (n : ℝ) * bridgeProfileMass profile n)) :
    Summable (firstLengthWeight (h := h)) := by
  change Summable (fun p : BridgePath h => (p.vertices.length : ℝ) * weight p)
  refine TheoremOS.ProfileSummability.summable_sizeWeight_of_hasSum
    (w := weight (h := h)) (size := fun p => p.vertices.length)
    (profile := profile) (c := bridgeProfileMass profile)
    bridgeWeight_nonneg hC hsize ?_
    (TheoremOS.ProfileSummability.summable_fiberMass_of_summable profile hw) hmoment
  intro n
  exact (hw.subtype (fun p : BridgePath h => profile p = n)).hasSum


theorem bridgeSummable_firstLengthWeight_of_profileFactorization
    {h : ℕ} {ι : Type*} [Fintype ι]
    (profile : BridgePath h → ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hsize : ∀ p : BridgePath h,
      (p.vertices.length : ℝ) ≤ C * ((profile p : ℝ) + 1))
    (hw : Summable (weight (h := h))) (L R : ℕ → ι → ℝ)
    (hL : ∀ n i, 0 ≤ L n i) (hR : ∀ n i, 0 ≤ R n i)
    (hfactor : ∀ a b, bridgeProfileMass profile (a + b) = ∑ i, L a i * R b i) :
    Summable (firstLengthWeight (h := h)) := by
  apply bridgeSummable_firstLengthWeight_of_profileFirstMoment profile hC hsize hw
  exact TheoremOS.FiniteMatrixFirstMoment.summable_firstMoment_of_finite_nonneg_factorization
    (c := bridgeProfileMass profile) (L := L) (R := R) hL hR hfactor
    (TheoremOS.ProfileSummability.summable_fiberMass_of_summable profile hw)

theorem bridgeSummable_firstLengthWeight_of_matrixProfile
    {h : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (profile : BridgePath h → ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hsize : ∀ p : BridgePath h,
      (p.vertices.length : ℝ) ≤ C * ((profile p : ℝ) + 1))
    (hw : Summable (weight (h := h)))
    (A : Matrix ι ι ℝ) (u v : ι → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hidentity : ∀ n, bridgeProfileMass profile n =
      TheoremOS.FiniteMatrixFirstMoment.matrixMass A u v n) :
    Summable (firstLengthWeight (h := h)) := by
  have hc : Summable (TheoremOS.FiniteMatrixFirstMoment.matrixMass A u v) :=
    (TheoremOS.ProfileSummability.summable_fiberMass_of_summable profile hw).congr hidentity
  have hm := TheoremOS.FiniteMatrixFirstMoment.summable_matrix_firstMoment A u v hA hu hv hc
  apply bridgeSummable_firstLengthWeight_of_profileFirstMoment profile hC hsize hw
  refine hm.congr fun n => ?_
  rw [hidentity n]


/-- A special case only: this does not claim that a honeycomb transfer matrix
is naturally indexed by vertex length. -/
theorem bridgeSummable_firstLengthWeight_of_lengthProfileFactorization
    {h : ℕ} {ι : Type*} [Fintype ι]
    (hw : Summable (weight (h := h))) (L R : ℕ → ι → ℝ)
    (hL : ∀ n i, 0 ≤ L n i) (hR : ∀ n i, 0 ≤ R n i)
    (hfactor : ∀ a b,
      bridgeProfileMass (fun p : BridgePath h => p.vertices.length) (a + b) =
        ∑ i, L a i * R b i) : Summable (firstLengthWeight (h := h)) := by
  apply bridgeSummable_firstLengthWeight_of_profileFactorization
    (fun p : BridgePath h => p.vertices.length) (C := 1) zero_le_one ?_ hw L R hL hR hfactor
  intro p
  simp only [one_mul]
  linarith

/-- Composition with the accepted canonical six-clause reduction. Each width
may use its own finite state type, profile and comparison constant. -/
theorem bridgeFiniteBridgeSums_of_matrixProfiles
    (ι : ℕ → Type*) [∀ h, Fintype (ι h)] [∀ h, DecidableEq (ι h)]
    (profile : ∀ h, BridgePath h → ℕ) (C : ℕ → ℝ)
    (A : ∀ h, Matrix (ι h) (ι h) ℝ) (u v : ∀ h, ι h → ℝ)
    (hw : ∀ h, 1 ≤ h → Summable (weight (h := h)))
    (hC : ∀ h, 1 ≤ h → 0 ≤ C h)
    (hsize : ∀ h, 1 ≤ h → ∀ p : BridgePath h,
      (p.vertices.length : ℝ) ≤ C h * (((profile h) p : ℝ) + 1))
    (hA : ∀ h, 1 ≤ h → ∀ i j, 0 ≤ A h i j)
    (hu : ∀ h, 1 ≤ h → ∀ i, 0 ≤ u h i)
    (hv : ∀ h, 1 ≤ h → ∀ i, 0 ≤ v h i)
    (hidentity : ∀ h, 1 ≤ h → ∀ n, bridgeProfileMass (profile h) n =
      TheoremOS.FiniteMatrixFirstMoment.matrixMass (A h) (u h) (v h) n) :
    FiniteBridgeSums := by
  apply bridgeFiniteBridgeSums_of_firstLengthWeight
  intro h hh
  exact bridgeSummable_firstLengthWeight_of_matrixProfile (profile h)
    (hC h hh) (hsize h hh) (hw h hh) (A h) (u h) (v h)
    (hA h hh) (hu h hh) (hv h hh) (hidentity h hh)


end OAI.PolynomialVacuumBridge.Corridor


namespace OAI.PolynomialVacuumBridge.Corridor

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

end OAI.PolynomialVacuumBridge.Corridor

#print axioms OAI.PolynomialVacuumBridge.Corridor.bridgeFiniteBridgeSums_of_occupiedSlabMatrices
