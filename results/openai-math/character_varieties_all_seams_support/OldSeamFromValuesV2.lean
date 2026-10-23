import OldEndpointAssemblyShared
import ParentSelectedSideTransport
import SeamCoordinateBridge
import EndpointActualMatrix
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
variable (s : S) (hs : s≠q)
local notation "ss" => BandGraft.oldPort A q B s true
local notation "pp" => Subtype.val (BandGraft.oldPort A q B s true)
local notation "nn" => Subtype.val (BandGraft.oldPort A q B s false)
lemma external_oldSeamFromValues (hs : s≠q)
    {R : Type} [CommRing R] (φ : R →+* K)
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
    (z : (e : (C).Generator) → (Matrix (Fin ((C).generatorRank e)) (Fin ((C).generatorRank e)) K)ˣ)
    (hframes : ∀ p,(C).portFrame z p=D.namedCutPortFrames q w (D.portFrame g) T p)
    (hparent : (MatrixIso.unit (z (.side ⟨ss,none⟩))).reindex
      (D.external_oldSideParent q w.shape rfl w.rowRanks w.colRanks s)
      (D.external_oldSideParent q w.shape rfl w.rowRanks w.colRanks s)=
      MatrixIso.unit (g (.side ⟨s,none⟩)))
    (hchild : (MatrixIso.block (fun ii : Fin ((BandGraft.wiring A q B).seamArity ss) =>
      MatrixIso.unit (z (.side ⟨ss,some ii⟩))⁻¹)).reindex
      (D.external_oldSideColumns q w.shape rfl w.rowRanks w.colRanks s)
      (D.external_oldSideColumns q w.shape rfl w.rowRanks w.colRanks s)=
      MatrixIso.block (fun ii : Fin (arity s) => MatrixIso.unit (g (.side ⟨s,some ii⟩))⁻¹))
    (hold : SameFramedFlag (fun i : (j : Fin (arity s)) × Fin (D.childDim s j) => i.1.val)
      ((D.namedSeamFrame s (g (.frame s false))).trans (D.namedParentLinear s g))
      ((D.namedChildInverse s g).trans (D.namedSeamFrame s (g (.frame s true))))) :
    SameFramedFlag ((C).seamGrade ss)
      (matrixUnitEquiv (((C).seamLeft ss).eval φ z))
      (matrixUnitEquiv (((C).seamRight ss).eval φ z)) := by
  let e := D.external_oldSideColumns q w.shape rfl w.rowRanks w.colRanks s
  let f := D.external_oldSideParent q w.shape rfl w.rowRanks w.colRanks s
  have he : e=D.external_oldCommonColumns q w s hs := by
    apply Equiv.ext
    intro i
    have hgrade := D.external_oldCommonColumns_grade q w s hs i
    have hfst : (e i).1=(D.external_oldCommonColumns q w s hs i).1 := by
      apply Fin.ext
      exact hgrade.symm
    apply Sigma.ext hfst
    apply (Fin.heq_ext_iff (congrArg ((C).childDim ss) hfst)).2
    have h1 := (C).external_seamColumnsTransport_snd
      (congrArg Prod.fst (D.external_oldNegativeAttach q w s hs))
      (D.external_oldEndpointNamedColumns q w s false i)
    have h2 := D.external_oldEndpointNamedColumns_snd q w s false i
    exact (h1.trans h2).symm
  have hf : f=D.external_oldCommonParent q w s hs := by
    apply Equiv.ext
    intro i
    rfl
  have hneg' := D.external_oldNegativeEndpoint_eq q w s hs g T
  have hpos' := D.external_oldPositiveEndpoint_eq q w s hs g T
  have nframe : (((MatrixIso.unit (z (.frame ss false))).reindex
      (blockIndex ((C).childDim ss)).symm (finCongr ((C).seamRank ss))).reindex e f).linearEquiv =
      D.namedSeamFrame s (g (.frame s false)) := by
    rw [← (C).external_endpointActualMatrix z _ hframes nn ss false
      (D.external_oldNegativeAttach q w s hs),he,hf]
    exact hneg'
  have pframe : (((MatrixIso.unit (z (.frame ss true))).reindex
      (blockIndex ((C).childDim ss)).symm (finCongr ((C).seamRank ss))).reindex e f).linearEquiv =
      D.namedSeamFrame s (g (.frame s true)) := by
    rw [← (C).external_endpointActualMatrix z _ hframes pp ss true
      (D.external_oldPositiveAttach q w s),he,hf]
    exact hpos'
  apply (C).external_seam_of_commonCoordinates ss φ z e f
  erw [nframe,pframe,hparent,hchild]
  have hgrade : (fun i => (e i).1.val)=(fun i => i.1.val) := by
    funext i
    rfl
  rw [hgrade]
  exact hold

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram

#check OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_oldSeamFromValues
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_oldSeamFromValues
