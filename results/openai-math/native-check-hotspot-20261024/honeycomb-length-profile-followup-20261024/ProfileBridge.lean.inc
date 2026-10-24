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

