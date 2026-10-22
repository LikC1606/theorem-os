import Mathlib

namespace OAI

namespace SmallCM





lemma powerseries_ker_constantCoeff (R : Type*) [CommRing R] :
    RingHom.ker (PowerSeries.constantCoeff (R := R)) =
      Ideal.span ({PowerSeries.X} : Set (PowerSeries R)) := by
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]

noncomputable def quotientSpanXEquiv (R : Type*) [CommRing R] :
    (PowerSeries R ⧸ Ideal.span ({PowerSeries.X} : Set (PowerSeries R))) ≃+* R :=
  (Ideal.quotEquivOfEq (powerseries_ker_constantCoeff R).symm).trans
    (RingHom.quotientKerEquivOfSurjective PowerSeries.constantCoeff_surj)

lemma powerseries_dim (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    ringKrullDim (PowerSeries R) = ringKrullDim R + 1 := by
  have hx : (PowerSeries.X : PowerSeries R) ∈ IsLocalRing.maximalIdeal (PowerSeries R) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      PowerSeries.isUnit_iff_constantCoeff]
    simpa using (not_isUnit_zero (M₀ := R))
  have h := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    (R := PowerSeries R) (x := PowerSeries.X)
    MvPowerSeries.X_mem_nonzeroDivisors hx
  rw [ringKrullDim_eq_of_ringEquiv (quotientSpanXEquiv R)] at h
  exact h.symm

lemma mvPowerSeries_dim (n : ℕ) :
    ringKrullDim (MvPowerSeries (Fin n) ℂ) = n := by
  induction n with
  | zero =>
    rw [ringKrullDim_eq_of_ringEquiv (MvPowerSeries.isEmptyEquiv (Fin 0) ℂ).toRingEquiv]
    simp
  | succ n ih =>
    rw [ringKrullDim_eq_of_ringEquiv (MvPowerSeries.finSuccEquiv ℂ n).toRingEquiv,
      powerseries_dim, ih]
    simp

lemma mvPowerSeries_three_dim :
    ringKrullDim (MvPowerSeries (Fin 3) ℂ) = 3 := by
  simpa using mvPowerSeries_dim 3





lemma polynomial_vars_eq_ker (σ k : Type*) [Field k] :
    MvPolynomial.idealOfVars σ k = RingHom.ker (MvPolynomial.constantCoeff (σ := σ) (R := k)) := by
  ext p
  change p ∈ MvPolynomial.idealOfVars σ k ↔ p.constantCoeff = 0
  rw [← pow_one (MvPolynomial.idealOfVars σ k), MvPolynomial.mem_pow_idealOfVars_iff']
  constructor
  · intro h
    exact h 0 (by simp)
  · intro h x hx
    have hx0 : x = 0 := (Finsupp.degree_eq_zero_iff x).1 (by omega)
    subst x
    exact h

lemma IsLocalRing.maximalIdeal_eq_span_vars (σ k : Type*) [Finite σ] [Field k] :
    IsLocalRing.maximalIdeal (MvPowerSeries σ k) =
      Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := k))) := by
  let I : Ideal (MvPolynomial σ k) := MvPolynomial.idealOfVars σ k
  let e := (MvPowerSeries.toAdicCompletionAlgEquiv σ k).toRingEquiv
  have hI : I.IsMaximal := by
    change (MvPolynomial.idealOfVars σ k).IsMaximal
    rw [polynomial_vars_eq_ker]
    apply RingHom.ker_isMaximal_of_surjective
    exact fun x => ⟨MvPolynomial.C x, by simp⟩
  letI : I.IsMaximal := hI
  have hmap : Ideal.map e
      (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := k)))) =
      I.map (algebraMap (MvPolynomial σ k) (AdicCompletion I (MvPolynomial σ k))) := by
    dsimp only [I]
    simp_rw [MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp]
    congr 2
    ext i
    simp [e, I, AdicCompletion.algebraMap_apply, ← MvPolynomial.coe_X,
      MvPowerSeries.toAdicCompletion_coe]
  have hm : (Ideal.map e
      (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := k))))).IsMaximal := by
    rw [hmap]
    exact AdicCompletion.isMaximal_map_of_le I I le_rfl (MvPolynomial.idealOfVars_fg σ k)
  have hm' : (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := k)))).IsMaximal :=
    (Ideal.isMaximal_map_iff_of_bijective e e.bijective).1 hm
  exact (IsLocalRing.eq_maximalIdeal hm').symm

lemma mvPowerSeries_complete (σ k : Type*) [Finite σ] [Field k] :
    IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries σ k)) (MvPowerSeries σ k) := by
  rw [IsLocalRing.maximalIdeal_eq_span_vars]
  infer_instance

lemma mvPowerSeries_three_complete :
    IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 3) ℂ)) (MvPowerSeries (Fin 3) ℂ) :=
  mvPowerSeries_complete (Fin 3) ℂ




lemma mvPowerSeries_ker_constantCoeff_maximal (n : ℕ) :
    RingHom.ker (MvPowerSeries.constantCoeff (σ := Fin n) (R := ℂ)) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) ℂ) := by
  apply IsLocalRing.ker_eq_maximalIdeal
  intro c
  exact ⟨MvPowerSeries.C c, MvPowerSeries.constantCoeff_C c⟩

lemma mvPowerSeries_residue_bijective (n : ℕ) :
    Function.Bijective (algebraMap ℂ (IsLocalRing.ResidueField (MvPowerSeries (Fin n) ℂ))) := by
  constructor
  · exact (algebraMap ℂ (IsLocalRing.ResidueField (MvPowerSeries (Fin n) ℂ))).injective
  · intro z
    obtain ⟨f, rfl⟩ := IsLocalRing.residue_surjective z
    refine ⟨MvPowerSeries.constantCoeff f, ?_⟩
    change Ideal.Quotient.mk _ (MvPowerSeries.C (MvPowerSeries.constantCoeff f)) =
      Ideal.Quotient.mk _ f
    apply Ideal.Quotient.eq.mpr
    rw [← mvPowerSeries_ker_constantCoeff_maximal n, RingHom.mem_ker]
    simp






lemma constantCoeff_almost {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (f : (PowerSeries K)) (h : IsAlmostIntegral (PowerSeries R) f) :
    IsAlmostIntegral R (PowerSeries.constantCoeff f) := by
  obtain ⟨b, hb, hh⟩ := h
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨PowerSeries.coeff b.order.toNat b, ?_, fun n ↦ ?_⟩
  · exact mem_nonZeroDivisors_iff_ne_zero.mpr (PowerSeries.coeff_order hb0)
  obtain ⟨q, hq⟩ := hh n
  refine ⟨PowerSeries.coeff b.order.toNat q, ?_⟩
  change algebraMap R K _ = _
  have heq : PowerSeries.map (algebraMap R K) q =
      PowerSeries.map (algebraMap R K) b * f ^ n := by
    simpa [Algebra.smul_def, PowerSeries.algebraMap_apply''] using hq
  have hbFact : PowerSeries.map (algebraMap R K) b =
      PowerSeries.X ^ b.order.toNat * PowerSeries.map (algebraMap R K) b.divXPowOrder := by
    simpa only [map_mul, map_pow, PowerSeries.map_X] using
      congrArg (PowerSeries.map (algebraMap R K))
        (PowerSeries.X_pow_order_mul_divXPowOrder (f := b)).symm
  rw [hbFact, mul_assoc] at heq
  have hc := congrArg (PowerSeries.coeff b.order.toNat) heq
  rw [PowerSeries.coeff_map] at hc
  have hx := PowerSeries.coeff_X_pow_mul
    (PowerSeries.map (algebraMap R K) b.divXPowOrder * f ^ n) b.order.toNat 0
  simp only [zero_add] at hx
  rw [hx] at hc
  rw [PowerSeries.coeff_zero_eq_constantCoeff] at hc
  simp only [map_mul, map_pow] at hc
  have hcc : PowerSeries.constantCoeff (PowerSeries.map (algebraMap R K) b.divXPowOrder) =
      algebraMap R K (PowerSeries.coeff b.order.toNat b) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
      PowerSeries.coeff_divXPowOrder, zero_add]
  simpa only [hcc, Algebra.smul_def] using hc

lemma almost_div_X {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (f : (PowerSeries K))
    (h : IsAlmostIntegral (PowerSeries R) (PowerSeries.X * f)) : IsAlmostIntegral (PowerSeries R) f := by
  obtain ⟨b, hb, hh⟩ := h
  refine ⟨b, hb, fun n ↦ ?_⟩
  obtain ⟨q, hq⟩ := hh n
  have heq : PowerSeries.map (algebraMap R K) q =
      PowerSeries.X ^ n * (PowerSeries.map (algebraMap R K) b * f ^ n) := by
    simpa [Algebra.smul_def, PowerSeries.algebraMap_apply'', mul_pow, mul_left_comm, mul_assoc]
      using hq
  have hqd : PowerSeries.X ^ n ∣ q := PowerSeries.X_pow_dvd_iff.mpr <| by
    intro i hi
    apply IsFractionRing.injective R K
    rw [map_zero, ← PowerSeries.coeff_map, heq, PowerSeries.coeff_X_pow_mul', if_neg]
    omega
  obtain ⟨q', hq'⟩ := hqd
  refine ⟨q', ?_⟩
  change PowerSeries.map (algebraMap R K) q' =
      PowerSeries.map (algebraMap R K) b * f ^ n
  rw [hq', map_mul, map_pow, PowerSeries.map_X] at heq
  exact PowerSeries.X_pow_mul_cancel heq

lemma coeff_mem_of_almost {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (f : (PowerSeries K)) (h : IsAlmostIntegral (PowerSeries R) f) (i : ℕ) :
    ∃ a : R, algebraMap R K a = PowerSeries.coeff i f := by
  induction i generalizing f with
  | zero =>
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      (IsIntegrallyClosed.isIntegral_iff.mp ((constantCoeff_almost f h).isIntegral))
  | succ i ih =>
    have hc := IsIntegrallyClosed.isIntegral_iff.mp ((constantCoeff_almost f h).isIntegral)
    obtain ⟨a, ha⟩ := hc
    let g : (PowerSeries K) := PowerSeries.mk (fun n ↦ PowerSeries.coeff (n + 1) f)
    have hg : IsAlmostIntegral (PowerSeries R) (PowerSeries.X * g) := by
      have heq : PowerSeries.X * g = f - algebraMap (PowerSeries R) (PowerSeries K) (PowerSeries.C a) := by
        simpa [g, ha, PowerSeries.algebraMap_apply''] using
          (PowerSeries.sub_const_eq_X_mul_shift f).symm
      rw [heq]
      exact sub_mem h (algebraMap_mem (completeIntegralClosure (PowerSeries R) (PowerSeries K)) _)
    simpa [g] using ih g (almost_div_X g hg)

lemma mem_range_of_almost {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (f : (PowerSeries K)) (h : IsAlmostIntegral (PowerSeries R) f) :
    ∃ a : (PowerSeries R), algebraMap (PowerSeries R) (PowerSeries K) a = f := by
  choose a ha using coeff_mem_of_almost f h
  refine ⟨PowerSeries.mk a, ?_⟩
  ext i
  simpa only [PowerSeries.algebraMap_apply'', PowerSeries.coeff_map, PowerSeries.coeff_mk] using ha i

lemma powerSeries_isIntegrallyClosed {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] :
    IsIntegrallyClosed (PowerSeries R) := by
  let K := FractionRing R
  let B := (PowerSeries K)
  let L := FractionRing B
  let F := FractionRing (PowerSeries R)
  let g : (PowerSeries R) →+* L := (algebraMap B L).comp (algebraMap (PowerSeries R) B)
  have hg : Function.Injective g :=
    (IsFractionRing.injective B L).comp
      (PowerSeries.map_injective (algebraMap R K) (IsFractionRing.injective R K))
  haveI : IsScalarTower (PowerSeries R) B L := inferInstance
  let φ : F →ₐ[(PowerSeries R)] L := IsFractionRing.liftAlgHom (g := Algebra.ofId _ _) hg
  apply (isIntegrallyClosed_iff F).mpr
  intro x hx
  have hy : IsIntegral B (φ x) := (hx.map φ).tower_top
  obtain ⟨f, hf⟩ := IsIntegrallyClosed.isIntegral_iff.mp hy
  have hfa : IsAlmostIntegral (PowerSeries R) f := by
    obtain ⟨b, hb, hh⟩ := hx.isAlmostIntegral
    refine ⟨b, hb, fun n ↦ ?_⟩
    obtain ⟨q, hq⟩ := hh n
    refine ⟨q, ?_⟩
    apply IsFractionRing.injective B L
    have heq := congrArg φ hq
    simpa [Algebra.smul_def, hf, map_mul, map_pow, IsScalarTower.algebraMap_apply (PowerSeries R) B L]
      using heq
  obtain ⟨a, ha⟩ := mem_range_of_almost f hfa
  refine ⟨a, φ.injective ?_⟩
  change φ (algebraMap (PowerSeries R) F a) = φ x
  rw [φ.commutes, ← hf, ← ha, IsScalarTower.algebraMap_apply (PowerSeries R) B L]

lemma mvPowerSeries_fin_integrallyClosed {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (n : ℕ) : IsIntegrallyClosed (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero => exact IsIntegrallyClosed.of_equiv (MvPowerSeries.isEmptyEquiv (Fin 0) R).toRingEquiv.symm
  | succ n ih =>
    letI := ih
    haveI : IsDomain (MvPowerSeries (Fin n) R) := NoZeroDivisors.to_isDomain _
    letI : IsIntegrallyClosed (PowerSeries (MvPowerSeries (Fin n) R)) := powerSeries_isIntegrallyClosed
    exact IsIntegrallyClosed.of_equiv (MvPowerSeries.finSuccEquiv R n).toRingEquiv.symm

lemma complex_fin_three_integrallyClosed : IsIntegrallyClosed (MvPowerSeries (Fin 3) ℂ) :=
  mvPowerSeries_fin_integrallyClosed 3



/-- Ring-theoretic properties of the completed surface cone. -/
theorem candidate_ring_properties :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsNoetherianRing R)
      (_ : IsIntegrallyClosed R) (_ : IsLocalRing R) (_ : Algebra ℂ R),
      IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧
      ringKrullDim R = 3 ∧
      Function.Bijective (algebraMap ℂ (IsLocalRing.ResidueField R)) := by
  let R := MvPowerSeries (Fin 3) ℂ
  letI : IsDomain R := NoZeroDivisors.to_isDomain _
  letI : IsIntegrallyClosed R := complex_fin_three_integrallyClosed
  refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, ?_, ?_⟩
  · exact mvPowerSeries_three_complete
  · exact mvPowerSeries_three_dim
  · exact mvPowerSeries_residue_bijective 3
end SmallCM


end OAI
