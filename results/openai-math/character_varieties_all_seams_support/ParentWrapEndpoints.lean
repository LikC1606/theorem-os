import ParentWrapPortFrames
import SigmaFinCoordinates
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.MarkedFrames
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

def parent_wrapFirstNamedColumns : ((i : Fin (arity q)) × Fin (D.childDim q i)) ≃
    ((i : Fin ((BandGraft.wiring A q B).seamArity ss)) × Fin ((C).childDim ss i)) :=
  ((D.parent_wrapFirstPortColumns q w).trans ((C).external_portColumns nn)).trans
    ((C).external_seamColumnsTransport (congrArg Prod.fst (D.parent_wrapNegativeAttach q w)))
lemma parent_wrapFirstNamedColumns_grade
    (i : (j : Fin (arity q)) × Fin (D.childDim q j)) :
    (D.parent_wrapFirstNamedColumns q w i).1.val = i.1.val := by
  change (((w.shape.atomicBand.kind 0).mirror.childEnumeration
      ((w.shape.atomicBand.kind 0).mirrorPort (w.shape.atomicBand.kind 0).input))
      (((w.shape.atomicBand.kind 0).mirrorChild _) (w.firstChild.symm i.1))).val = _
  rw [Kind.mirror_childEnumeration]
  change (w.firstChild (w.firstChild.symm i.1)).val = i.1.val
  rw [Equiv.apply_symm_apply]
lemma parent_wrapFirstNamedColumns_snd
    (i : (j : Fin (arity q)) × Fin (D.childDim q j)) :
    (D.parent_wrapFirstNamedColumns q w i).2.val = i.2.val := by
  change (w.firstColumns.symm i).2.val = i.2.val
  exact external_sigmaFinCongr_symm_snd w.firstChild _ _ (w.firstChild_rank) i

def parent_wrapLastNamedColumns : ((i : Fin (arity q)) × Fin (D.childDim q i)) ≃
    ((i : Fin ((BandGraft.wiring A q B).seamArity ss)) × Fin ((C).childDim ss i)) :=
  ((D.parent_wrapLastPortColumns q w).trans ((C).external_portColumns pp)).trans
    ((C).external_seamColumnsTransport (congrArg Prod.fst (D.parent_wrapPositiveAttach q w)))
lemma parent_wrapLastNamedColumns_grade
    (i : (j : Fin (arity q)) × Fin (D.childDim q j)) :
    (D.parent_wrapLastNamedColumns q w i).1.val = i.1.val := by
  change (((w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).mirror.childEnumeration
      ((w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).mirrorPort (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output))
      (((w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).mirrorChild _) (w.lastChild.symm i.1))).val = _
  rw [Kind.mirror_childEnumeration]
  change (w.lastChild (w.lastChild.symm i.1)).val = i.1.val
  rw [Equiv.apply_symm_apply]
lemma parent_wrapLastNamedColumns_snd
    (i : (j : Fin (arity q)) × Fin (D.childDim q j)) :
    (D.parent_wrapLastNamedColumns q w i).2.val = i.2.val := by
  change (w.lastColumns.symm i).2.val = i.2.val
  exact external_sigmaFinCongr_symm_snd w.lastChild _ _ (w.lastChild_rank) i

def parent_wrapCommonParent :=
  (D.parent_wrapFirstPortParent q w).trans
    (finCongr (congrArg (fun z => (C).rank ((C).ports.facet ⟨z,none⟩))
      (congrArg Prod.fst (D.parent_wrapNegativeAttach q w))))
lemma parent_wrapNamedColumns_eq :
    D.parent_wrapFirstNamedColumns q w=D.parent_wrapLastNamedColumns q w := by
  apply Equiv.ext
  intro i
  have he : (D.parent_wrapFirstNamedColumns q w i).1=(D.parent_wrapLastNamedColumns q w i).1 := by
    apply Fin.ext
    exact (D.parent_wrapFirstNamedColumns_grade q w i).trans
      (D.parent_wrapLastNamedColumns_grade q w i).symm
  apply Sigma.ext he
  apply (Fin.heq_ext_iff (congrArg ((C).childDim ss) he)).2
  exact (D.parent_wrapFirstNamedColumns_snd q w i).trans
    (D.parent_wrapLastNamedColumns_snd q w i).symm
lemma parent_wrapCommonParent_positive :
    D.parent_wrapCommonParent q w =
      (D.parent_wrapLastPortParent q w).trans
        (finCongr (congrArg (fun z => (C).rank ((C).ports.facet ⟨z,none⟩))
          (congrArg Prod.fst (D.parent_wrapPositiveAttach q w)))) := by
  apply Equiv.ext
  intro i
  rfl

lemma parent_wrapNegativeEndpoint (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    (((C).external_endpointNamedMatrix (D.namedCutPortFrames q w old T)
      nn ss false (D.parent_wrapNegativeAttach q w)).reindex
      (D.parent_wrapFirstNamedColumns q w) (D.parent_wrapCommonParent q w)).linearEquiv =
      w.firstFrame.trans T.linearEquiv.symm := by
  have hh := (C).external_endpointNamedMatrix_normalized
    (D.namedCutPortFrames q w old T) nn ss false (D.parent_wrapNegativeAttach q w)
    (D.parent_wrapFirstPortColumns q w) (D.parent_wrapFirstPortParent q w)
  exact (congrArg MatrixIso.linearEquiv hh).trans (D.parent_wrapFirstPortFrame q w old T)

lemma parent_wrapPositiveEndpoint (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    (((C).external_endpointNamedMatrix (D.namedCutPortFrames q w old T)
      pp ss true (D.parent_wrapPositiveAttach q w)).reindex
      (D.parent_wrapFirstNamedColumns q w) (D.parent_wrapCommonParent q w)).linearEquiv =
      w.lastFrame.trans T.linearEquiv.symm := by
  erw [D.parent_wrapNamedColumns_eq q w,D.parent_wrapCommonParent_positive q w]
  have hh := (C).external_endpointNamedMatrix_normalized
    (D.namedCutPortFrames q w old T) pp ss true (D.parent_wrapPositiveAttach q w)
    (D.parent_wrapLastPortColumns q w) (D.parent_wrapLastPortParent q w)
  exact (congrArg MatrixIso.linearEquiv hh).trans (D.parent_wrapLastPortFrame q w old T)

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_wrapNegativeEndpoint
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_wrapPositiveEndpoint
