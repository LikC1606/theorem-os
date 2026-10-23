import ParentSelectedOldPort
import ParentSelectedLastPortFixed
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
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "ss" => BandGraft.oldPort A q B q true
local notation "pp" => (Subtype.val (BandGraft.oldPort A q B q true))
local notation "nn" => (Subtype.val (BandGraft.originalPort A q B (Fin.last (B).length) false))

lemma parent_selectedPositiveAttach : (C).ports.attach pp=(ss,true) := by
  exact (BandGraft.wiring A q B).endOf_portAt (ss,true)

lemma parent_selectedNegativeAttach : (C).ports.attach nn=(ss,false) := by
  have hh := (BandGraft.wiring A q B).endOf_portAt (ss,false)
  change (BandGraft.wiring A q B).endOf ((BandGraft.wiring A q B).wire ss).val = _ at hh
  erw [BandGraft.wire_last] at hh
  exact hh

lemma parent_selectedPositivePortParentRank :
    ((C).vertexRanks (pp).1).rank (pp).2 none = D.rank (D.ports.facet ⟨q,none⟩) := by
  have hh := congrArg (fun d => d.rank (Subtype.val (D.ports.portAt true q)).2 none)
    (D.refinedCut_old_vertexRanks q w.shape rfl w.rowRanks w.colRanks
      (Subtype.val (D.ports.portAt true q)).1)
  exact hh.trans (congrArg (fun e : S × Bool => D.rank (D.ports.facet ⟨e.1,none⟩))
    (D.ports.attach_portAt q true))

def parent_selectedCommonColumns :=
    (D.external_oldEndpointNamedColumns q w q true).trans
      ((C).external_seamColumnsTransport (congrArg Prod.fst (D.parent_selectedPositiveAttach q w)))

def parent_selectedCommonParent :=
  (finCongr (D.parent_selectedPositivePortParentRank q w)).symm.trans
    (finCongr (congrArg (fun z => (C).rank ((C).ports.facet ⟨z,none⟩))
      (congrArg Prod.fst (D.parent_selectedPositiveAttach q w))))

lemma parent_selectedCommonColumns_grade
    (i : (j : Fin (arity q)) × Fin (D.childDim q j)) :
    (D.parent_selectedCommonColumns q w i).1.val = i.1.val := by
  exact D.external_oldEndpointNamedColumns_grade q w q true i

lemma parent_selectedPositiveEndpoint_eq
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    (((C).external_endpointNamedMatrix (D.namedCutPortFrames q w (D.portFrame g) T)
      pp ss true (D.parent_selectedPositiveAttach q w)).reindex
      (D.parent_selectedCommonColumns q w) (D.parent_selectedCommonParent q w)).linearEquiv =
        D.namedSeamFrame q (g (.frame q true)) := by
  have hh := (C).external_endpointNamedMatrix_normalized
    (D.namedCutPortFrames q w (D.portFrame g) T) pp ss true
    (D.parent_selectedPositiveAttach q w) (D.external_oldEndpointPortColumns q w q true).symm
    (finCongr (D.parent_selectedPositivePortParentRank q w)).symm
  exact (congrArg MatrixIso.linearEquiv hh).trans (D.external_oldEndpointPortFrame_eq q w q true g T)

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
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
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "ss" => BandGraft.oldPort A q B q true
local notation "pp" => (Subtype.val (BandGraft.oldPort A q B q true))
local notation "nn" => (Subtype.val (BandGraft.originalPort A q B (Fin.last (B).length) false))


lemma parent_selectedLastNamedColumns_snd
    (i : (j : Fin (arity q)) × Fin (D.childDim q j)) :
    (D.parent_selectedLastNamedColumns q w i).2.val = i.2.val := by
  unfold parent_selectedLastNamedColumns
  change ((C).external_portColumns nn ((D.parent_selectedLastPortColumns q w).symm i)).2.val = _
  rw [(C).external_portColumns_snd]
  exact external_sigmaFinCongr_symm_snd w.lastChild
    (fun c => ((C).vertexRanks (nn).1).rank (nn).2 (some c))
    (D.childDim q) (D.parent_selectedLastColumnRank q w) i

lemma parent_selectedPositiveNamedColumns_snd
    (i : (j : Fin (arity q)) × Fin (D.childDim q j)) :
    (D.external_oldEndpointNamedColumns q w q true i).2.val = i.2.val := by
  unfold external_oldEndpointNamedColumns
  change ((C).external_portColumns pp ((D.external_oldEndpointPortColumns q w q true).symm i)).2.val = _
  rw [(C).external_portColumns_snd]
  exact external_sigmaFinCongr_symm_snd (D.external_oldEndpointChild q true)
    (fun c => ((C).vertexRanks (pp).1).rank (pp).2 (some c))
    (D.childDim q) (D.external_oldEndpointChildRank q w q true) i

lemma parent_selectedCommonColumns_negative :
    D.parent_selectedCommonColumns q w =
      (D.parent_selectedLastNamedColumns q w).trans
        ((C).external_seamColumnsTransport
          (congrArg Prod.fst (D.parent_selectedNegativeAttach q w))) := by
  apply Equiv.ext
  intro i
  have hp := D.parent_selectedCommonColumns_grade q w i
  have hn := D.parent_selectedLastNamedColumns_grade q w i
  have he : (D.parent_selectedCommonColumns q w i).1 =
      (((D.parent_selectedLastNamedColumns q w).trans
        ((C).external_seamColumnsTransport
          (congrArg Prod.fst (D.parent_selectedNegativeAttach q w)))) i).1 := by
    apply Fin.ext
    exact hp.trans hn.symm
  apply Sigma.ext he
  apply (Fin.heq_ext_iff (congrArg ((C).childDim ss) he)).2
  have hp2 := D.parent_selectedPositiveNamedColumns_snd q w i
  have hn2 := D.parent_selectedLastNamedColumns_snd q w i
  have hpt := (C).external_seamColumnsTransport_snd
    (congrArg Prod.fst (D.parent_selectedPositiveAttach q w))
    (D.external_oldEndpointNamedColumns q w q true i)
  have hnt := (C).external_seamColumnsTransport_snd
    (congrArg Prod.fst (D.parent_selectedNegativeAttach q w))
      (D.parent_selectedLastNamedColumns q w i)
  exact (hpt.trans hp2).trans (hnt.trans hn2).symm

lemma parent_selectedNegativeEndpoint_eq
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    (((C).external_endpointNamedMatrix (D.namedCutPortFrames q w (D.portFrame g) T)
      nn ss false (D.parent_selectedNegativeAttach q w)).reindex
      (D.parent_selectedCommonColumns q w) (D.parent_selectedCommonParent q w)).linearEquiv =
        w.lastFrame := by
  have hp : D.parent_selectedCommonParent q w =
      (finCongr (D.parent_selectedLastPortParentRank q w)).symm.trans
        (finCongr (congrArg (fun z => (C).rank ((C).ports.facet ⟨z,none⟩))
          (congrArg Prod.fst (D.parent_selectedNegativeAttach q w)))) := by
    apply Equiv.ext
    intro i
    rfl
  have hh := (C).external_endpointNamedMatrix_normalized
    (D.namedCutPortFrames q w (D.portFrame g) T) nn ss false
    (D.parent_selectedNegativeAttach q w) (D.parent_selectedLastPortColumns q w).symm
    (finCongr (D.parent_selectedLastPortParentRank q w)).symm
  have hc := D.parent_selectedCommonColumns_negative q w
  have h1 := congrArg MatrixIso.linearEquiv hh
  erw [← hc,← hp] at h1
  exact h1.trans (D.parent_selectedLastPortFrame_eq q w (D.portFrame g) T)

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram

#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_selectedPositiveEndpoint_eq
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_selectedNegativeEndpoint_eq
