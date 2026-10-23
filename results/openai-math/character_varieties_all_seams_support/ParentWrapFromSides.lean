import ParentWrapSeam
import ParentWrapSideEndpointCoordinates
set_option autoImplicit false
set_option maxHeartbeats 0
set_option quotPrecheck false
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "ss" => BandGraft.mirrorOutput A q B (Fin.last (B).length)
lemma parent_wrapSeam_fromSides
    {R : Type} [CommRing R] (φ : R →+* K)
    (v : (z : (C).Generator) →
      (Matrix (Fin ((C).generatorRank z)) (Fin ((C).generatorRank z)) K)ˣ)
    (g : (z : D.Generator) →
      (Matrix (Fin (D.generatorRank z)) (Fin (D.generatorRank z)) K)ˣ)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
    (hframes : ∀ p,(C).portFrame v p=D.namedCutPortFrames q w (D.portFrame g) T p)
    (hside : ∀ a, v (.side a)=D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks
      (fun a => g (.side a)) J Y a)
    (hflag : SameFramedFlag (fun i : (j : Fin (arity q)) × Fin (D.childDim q j) => i.1.val)
      ((w.firstFrame.trans T.linearEquiv.symm).trans (MatrixIso.unit Y).linearEquiv)
      (w.lastFrame.trans T.linearEquiv.symm)) :
    SameFramedFlag ((C).seamGrade ss)
      (matrixUnitEquiv (((C).seamLeft ss).eval φ v))
      (matrixUnitEquiv (((C).seamRight ss).eval φ v)) := by
  apply D.parent_wrapSeam q w φ v (D.portFrame g) T Y hframes
  · rw [hside]
    rw [← D.parent_wrapSideParent_eq q w]
    exact D.parent_wrapParentTransport q w.shape rfl w.rowRanks w.colRanks
      (fun a => g (.side a)) J Y
  · simp only [hside]
    exact D.parent_wrapChildIdentity q w (fun a => g (.side a)) J Y
  · exact hflag
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_wrapSeam_fromSides
