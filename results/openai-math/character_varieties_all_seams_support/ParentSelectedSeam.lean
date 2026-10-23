import ParentSelectedEndpointsModular
import SeamCoordinateBridge
import EndpointActualMatrix
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
local notation "ss" => BandGraft.oldPort A q B q true
local notation "pp" => Subtype.val (BandGraft.oldPort A q B q true)
local notation "nn" => Subtype.val (BandGraft.originalPort A q B (Fin.last (B).length) false)
local notation "e" => D.parent_selectedCommonColumns q w
local notation "f0" => D.parent_selectedCommonParent q w
lemma parent_selectedSeam
    {R : Type} [CommRing R] (φ : R →+* K)
    (v : (z : (C).Generator) →
      (Matrix (Fin ((C).generatorRank z)) (Fin ((C).generatorRank z)) K)ˣ)
    (g : (z : D.Generator) →
      (Matrix (Fin (D.generatorRank z)) (Fin (D.generatorRank z)) K)ˣ)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
    (J : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
    (hframes : ∀ p,(C).portFrame v p=D.namedCutPortFrames q w (D.portFrame g) T p)
    (hparent : (MatrixIso.unit (v (.side ⟨ss,none⟩))).reindex f0 f0=MatrixIso.unit J)
    (hchild : ((MatrixIso.block (fun j : Fin ((BandGraft.wiring A q B).seamArity ss) =>
      MatrixIso.unit (v (.side ⟨ss,some j⟩))⁻¹)).reindex e e).linearEquiv=
      D.namedChildInverse q g)
    (hflag : SameFramedFlag (fun i : (j : Fin (arity q)) × Fin (D.childDim q j) => i.1.val)
      (w.lastFrame.trans (MatrixIso.unit J).linearEquiv)
      ((D.namedChildInverse q g).trans (D.namedSeamFrame q (g (.frame q true))))) :
    SameFramedFlag ((C).seamGrade ss)
      (matrixUnitEquiv (((C).seamLeft ss).eval φ v))
      (matrixUnitEquiv (((C).seamRight ss).eval φ v)) := by
  have nframe : (((MatrixIso.unit (v (.frame ss false))).reindex
      (blockIndex ((C).childDim ss)).symm (finCongr ((C).seamRank ss))).reindex e f0).linearEquiv =
      w.lastFrame := by
    rw [← (C).external_endpointActualMatrix v _ hframes nn ss false
      (D.parent_selectedNegativeAttach q w)]
    exact D.parent_selectedNegativeEndpoint_eq q w g T
  have pframe : (((MatrixIso.unit (v (.frame ss true))).reindex
      (blockIndex ((C).childDim ss)).symm (finCongr ((C).seamRank ss))).reindex e f0).linearEquiv =
      D.namedSeamFrame q (g (.frame q true)) := by
    rw [← (C).external_endpointActualMatrix v _ hframes pp ss true
      (D.parent_selectedPositiveAttach q w)]
    exact D.parent_selectedPositiveEndpoint_eq q w g T
  apply (C).external_seam_of_commonCoordinates ss φ v e f0
  erw [nframe,pframe,hparent,hchild]
  have hgrade : (fun i => (e i).1.val)=(fun i => i.1.val) := by
    funext i
    exact D.parent_selectedCommonColumns_grade q w i
  rw [hgrade]
  exact hflag
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_selectedSeam
