import ParentWrapFlagAlgebra
import OAI.AlgebraicGeometry.CharacterVarieties.Seams.ProducedEquations
set_option maxHeartbeats 0
namespace OAI.IntegralCharacterVarieties
noncomputable section
open scoped Classical Matrix
variable {K α β : Type*} [Field K] [Fintype β] [DecidableEq β]

lemma parent_wrapUnitFlag (a : α → ℕ)
    (f l : (α → K) ≃ₗ[K] (β → K))
    (P J T : (Matrix β β K)ˣ)
    (h : SameFramedFlag a l
      ((f.trans (MatrixIso.unit P).linearEquiv).trans (MatrixIso.unit J).linearEquiv.symm)) :
    SameFramedFlag a
      ((f.trans (MatrixIso.unit T).linearEquiv.symm).trans
        (MatrixIso.unit (T⁻¹*J⁻¹*P*T)).linearEquiv)
      (l.trans (MatrixIso.unit T).linearEquiv.symm) := by
  have hy : (MatrixIso.unit (T⁻¹*J⁻¹*P*T)).linearEquiv =
      (((MatrixIso.unit T).linearEquiv.trans (MatrixIso.unit P).linearEquiv).trans
        (MatrixIso.unit J).linearEquiv.symm).trans (MatrixIso.unit T).linearEquiv.symm := by
    simp only [MatrixIso.unit_mul, MatrixIso.unit_inv]
    apply LinearEquiv.ext
    intro v
    simp only [MatrixIso.linearEquiv_trans_apply, LinearEquiv.trans_apply]
    rfl
  rw [hy]
  exact parent_wrapFlag_algebra a (MatrixIso.unit P).linearEquiv
    (MatrixIso.unit J).linearEquiv (MatrixIso.unit T).linearEquiv h
end
end OAI.IntegralCharacterVarieties
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K] [Algebra R K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (hg : 0 < D.genus (D.bandCutParent q))
    (P : D.Punctures R) (x : D.Solution P K)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
local notation "w" => D.producedCutBand q hg P x b0 i0
local notation "g" => D.producedCutSeed q hg P x b0
local notation "J" => D.producedCutJ q hg P x b0 i0
local notation "T" => D.producedCutT q hg P x b0 i0
lemma parent_producedWrapFlag :
    SameFramedFlag (fun i : (j : Fin (arity q)) × Fin (D.childDim q j) => i.1.val)
      (((w).firstFrame.trans (MatrixIso.unit T).linearEquiv.symm).trans
        (MatrixIso.unit (T⁻¹*J⁻¹*(show (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
          (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ from g (.side ⟨q,none⟩))*T)).linearEquiv)
      ((w).lastFrame.trans (MatrixIso.unit T).linearEquiv.symm) := by
  have h := (w).lastFrame_holds
  have hf := (w).firstFrame_holds
  have hh := parent_sameFramedFlag_post _ hf (D.namedParentLinear q g)
  have hh' := parent_sameFramedFlag_post _ hh (MatrixIso.unit J).linearEquiv.symm
  have hsym : SameFramedFlag (fun i : (j : Fin (arity q)) × Fin (D.childDim q j) => i.1.val)
      (((D.namedSeamFrame q (g (.frame q false))).trans
          (D.namedParentLinear q g)).trans (MatrixIso.unit J).linearEquiv.symm)
      (((w).firstFrame.trans (D.namedParentLinear q g)).trans
          (MatrixIso.unit J).linearEquiv.symm) := by
    refine ⟨fun k => (hh'.1 k).symm, ?_⟩
    intro k v hv
    exact (hh'.2 k v (by rw [hh'.1 (k+1)]; exact hv)).symm
  exact parent_wrapUnitFlag _ (w).firstFrame (w).lastFrame
    ((show (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
          (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ from g (.side ⟨q,none⟩))) J T (parent_sameFramedFlag_trans _ h hsym)
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
#print axioms OAI.IntegralCharacterVarieties.parent_wrapUnitFlag
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_producedWrapFlag
