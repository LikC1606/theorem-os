import FirstCommonEqualityV3
import FrameIndexBridge
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.MarkedFrames
set_option autoImplicit false
set_option maxHeartbeats 0

namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
    (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))


end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
    (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))

local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "s0" => BandGraft.originalPort A q B 0 true

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity)

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
    (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))

local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "s0" => BandGraft.originalPort A q B 0 true
local notation "p0" => (Subtype.val (BandGraft.originalPort A q B 0 true))

lemma external_firstPortFrame_eq :
    ((D.namedCutPortFrames q w old T p0).reindex
      (D.external_firstPortColumns q w).symm
      (finCongr (D.external_firstPortParentRank q w)).symm).linearEquiv = w.firstFrame := by
  have ec : w.firstColumns.symm.trans
      (Equiv.sigmaCongr (Equiv.refl ((w.shape.atomicBand.kind 0).table.Child (w.shape.atomicBand.kind 0).input))
        (fun c => finCongr (congrArg (fun d => d.rank (w.shape.atomicBand.kind 0).input (some c))
          (D.namedCut_orig_localRanks q w 0)))) =
      (D.external_firstPortColumns q w).symm := by
    apply Equiv.ext
    intro i
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Fin.ext
      rfl
  have ep : (finCongr w.firstParent_rank).symm.trans
      (finCongr (congrArg (fun d => d.rank (w.shape.atomicBand.kind 0).input none)
        (D.namedCut_orig_localRanks q w 0))) =
      (finCongr (D.external_firstPortParentRank q w)).symm := by
    ext i
    rfl
  have hh := LocalRanks.external_transportFrames_reindex (D.namedCut_orig_localRanks q w 0)
    (w.vertexFrames 0) (w.shape.atomicBand.kind 0).input
  have hh2 := congrArg (fun u => (u.reindex w.firstColumns.symm (finCongr w.firstParent_rank).symm).linearEquiv) hh
  erw [MatrixIso.reindex_reindex_eq, ec, ep] at hh2
  exact hh2

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram

#check OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_firstPortFrame_eq
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_firstPortFrame_eq
