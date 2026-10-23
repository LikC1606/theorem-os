import ParentWrapEndpoints
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
local notation "ss" => BandGraft.mirrorOutput A q B (Fin.last (B).length)
local notation "pp" => Subtype.val (BandGraft.mirrorOutput A q B (Fin.last (B).length))
local notation "nn" => Subtype.val (BandGraft.mirrorInput A q B 0)
local notation "e" => D.parent_wrapFirstNamedColumns q w
local notation "f0" => D.parent_wrapCommonParent q w
lemma parent_wrapSeam
    {R : Type} [CommRing R] (φ : R →+* K)
    (g : (z : (C).Generator) →
      (Matrix (Fin ((C).generatorRank z)) (Fin ((C).generatorRank z)) K)ˣ)
    (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
    (Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
    (hframes : ∀ p,(C).portFrame g p=D.namedCutPortFrames q w old T p)
    (hparent : (MatrixIso.unit (g (.side ⟨ss,none⟩))).reindex f0 f0=MatrixIso.unit Y)
    (hchild : ((MatrixIso.block (fun j : Fin ((BandGraft.wiring A q B).seamArity ss) =>
      MatrixIso.unit (g (.side ⟨ss,some j⟩))⁻¹)).reindex e e).linearEquiv=
      LinearEquiv.refl K _)
    (hflag : SameFramedFlag (fun i : (j : Fin (arity q)) × Fin (D.childDim q j) => i.1.val)
      ((w.firstFrame.trans T.linearEquiv.symm).trans (MatrixIso.unit Y).linearEquiv)
      (w.lastFrame.trans T.linearEquiv.symm)) :
    SameFramedFlag ((C).seamGrade ss)
      (matrixUnitEquiv (((C).seamLeft ss).eval φ g))
      (matrixUnitEquiv (((C).seamRight ss).eval φ g)) := by
  have nframe : (((MatrixIso.unit (g (.frame ss false))).reindex
      (blockIndex ((C).childDim ss)).symm (finCongr ((C).seamRank ss))).reindex e f0).linearEquiv =
      w.firstFrame.trans T.linearEquiv.symm := by
    rw [← (C).external_endpointActualMatrix g _ hframes nn ss false
      (D.parent_wrapNegativeAttach q w)]
    exact D.parent_wrapNegativeEndpoint q w old T
  have pframe : (((MatrixIso.unit (g (.frame ss true))).reindex
      (blockIndex ((C).childDim ss)).symm (finCongr ((C).seamRank ss))).reindex e f0).linearEquiv =
      w.lastFrame.trans T.linearEquiv.symm := by
    rw [← (C).external_endpointActualMatrix g _ hframes pp ss true
      (D.parent_wrapPositiveAttach q w)]
    exact D.parent_wrapPositiveEndpoint q w old T
  apply (C).external_seam_of_commonCoordinates ss φ g e f0
  erw [nframe,pframe,hparent,hchild]
  have hgrade : (fun i => (e i).1.val)=(fun i => i.1.val) := by
    funext i
    exact D.parent_wrapFirstNamedColumns_grade q w i
  rw [hgrade]
  simpa only [LinearEquiv.refl_trans] using hflag
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_wrapSeam
