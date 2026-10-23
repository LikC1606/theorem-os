import ParentSelectedOldPort
import EndpointNormalization
import SigmaFinCoordinates
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
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "B" => D.ports.refinedBandForSeam q w.shape
variable (s : S) (b : Bool)
local notation "pold" => (Subtype.val (D.ports.portAt b s))
local notation "pn" => (Subtype.val (BandGraft.oldPort A q B s b))
lemma external_oldEndpointPortParentRank :
    ((C).vertexRanks (pn).1).rank (pn).2 none = D.rank (D.ports.facet ⟨s,none⟩) := by
  have hh := congrArg (fun d => d.rank (pold).2 none)
    (D.refinedCut_old_vertexRanks q w.shape rfl w.rowRanks w.colRanks (pold).1)
  exact hh.trans (congrArg (fun e : S × Bool => D.rank (D.ports.facet ⟨e.1,none⟩))
    (D.ports.attach_portAt s b))


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
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "B" => D.ports.refinedBandForSeam q w.shape
variable (s : S) (hs : s≠q)
local notation "ss" => BandGraft.oldPort A q B s true
local notation "pp" => (Subtype.val (BandGraft.oldPort A q B s true))
local notation "nn" => (Subtype.val (BandGraft.oldPort A q B s false))

lemma external_oldPositiveAttach : (C).ports.attach pp=(ss,true) := by
  exact (BandGraft.wiring A q B).endOf_portAt (ss,true)

lemma external_oldNegativeAttach (hs : s≠q) : (C).ports.attach nn=(ss,false) := by
  have hh := (BandGraft.wiring A q B).endOf_portAt (ss,false)
  change (BandGraft.wiring A q B).endOf ((BandGraft.wiring A q B).wire ss).val = _ at hh
  erw [BandGraft.wire_old A q B s hs] at hh
  exact hh

lemma external_oldEndpointNamedColumns_snd (b : Bool)
    (i : (j : Fin (arity s)) × Fin (D.childDim s j)) :
    (D.external_oldEndpointNamedColumns q w s b i).2.val = i.2.val := by
  unfold external_oldEndpointNamedColumns
  change ((C).external_portColumns
    (Subtype.val (BandGraft.oldPort A q B s b))
    ((D.external_oldEndpointPortColumns q w s b).symm i)).2.val = _
  rw [(C).external_portColumns_snd]
  exact external_sigmaFinCongr_symm_snd (D.external_oldEndpointChild s b)
    (fun c => ((C).vertexRanks (.inl (Subtype.val (D.ports.portAt b s)).1)).rank
      (Subtype.val (D.ports.portAt b s)).2 (some c))
    (D.childDim s) (D.external_oldEndpointChildRank q w s b) i

def external_oldCommonColumns := (D.external_oldEndpointNamedColumns q w s false).trans
  ((C).external_seamColumnsTransport (congrArg Prod.fst (D.external_oldNegativeAttach q w s hs)))

def external_oldCommonParent :=
  (finCongr (D.external_oldEndpointPortParentRank q w s false)).symm.trans
    (finCongr (congrArg (fun z => (C).rank ((C).ports.facet ⟨z,none⟩))
      (congrArg Prod.fst (D.external_oldNegativeAttach q w s hs))))

lemma external_oldCommonColumns_grade
    (i : (j : Fin (arity s)) × Fin (D.childDim s j)) :
    (D.external_oldCommonColumns q w s hs i).1.val = i.1.val := by
  exact D.external_oldEndpointNamedColumns_grade q w s false i

lemma external_oldCommonColumns_positive :
    D.external_oldCommonColumns q w s hs =
      (D.external_oldEndpointNamedColumns q w s true).trans
        ((C).external_seamColumnsTransport
          (congrArg Prod.fst (D.external_oldPositiveAttach q w s))) := by
  apply Equiv.ext
  intro i
  have hp := D.external_oldEndpointNamedColumns_grade q w s true i
  have hn := D.external_oldCommonColumns_grade q w s hs i
  have he : (D.external_oldCommonColumns q w s hs i).1 =
      (((D.external_oldEndpointNamedColumns q w s true).trans
        ((C).external_seamColumnsTransport
          (congrArg Prod.fst (D.external_oldPositiveAttach q w s)))) i).1 := by
    apply Fin.ext
    exact hn.trans hp.symm
  apply Sigma.ext he
  apply (Fin.heq_ext_iff (congrArg ((C).childDim ss) he)).2
  have hp2 := D.external_oldEndpointNamedColumns_snd q w s true i
  have hn2 := D.external_oldEndpointNamedColumns_snd q w s false i
  have hpt := (C).external_seamColumnsTransport_snd
    (congrArg Prod.fst (D.external_oldPositiveAttach q w s))
    (D.external_oldEndpointNamedColumns q w s true i)
  have hnt := (C).external_seamColumnsTransport_snd
    (congrArg Prod.fst (D.external_oldNegativeAttach q w s hs))
      (D.external_oldEndpointNamedColumns q w s false i)
  exact (hnt.trans hn2).trans (hpt.trans hp2).symm

lemma external_oldNegativeEndpoint_eq
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    (((C).external_endpointNamedMatrix (D.namedCutPortFrames q w (D.portFrame g) T)
      nn ss false (D.external_oldNegativeAttach q w s hs)).reindex
      (D.external_oldCommonColumns q w s hs) (D.external_oldCommonParent q w s hs)).linearEquiv =
        D.namedSeamFrame s (g (.frame s false)) := by
  have hh := (C).external_endpointNamedMatrix_normalized
    (D.namedCutPortFrames q w (D.portFrame g) T) nn ss false
    (D.external_oldNegativeAttach q w s hs) (D.external_oldEndpointPortColumns q w s false).symm
    (finCongr (D.external_oldEndpointPortParentRank q w s false)).symm
  exact (congrArg MatrixIso.linearEquiv hh).trans (D.external_oldEndpointPortFrame_eq q w s false g T)

lemma external_oldPositiveEndpoint_eq
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    (((C).external_endpointNamedMatrix (D.namedCutPortFrames q w (D.portFrame g) T)
      pp ss true (D.external_oldPositiveAttach q w s)).reindex
      (D.external_oldCommonColumns q w s hs) (D.external_oldCommonParent q w s hs)).linearEquiv =
        D.namedSeamFrame s (g (.frame s true)) := by
  have hp : D.external_oldCommonParent q w s hs =
      (finCongr (D.external_oldEndpointPortParentRank q w s true)).symm.trans
        (finCongr (congrArg (fun z => (C).rank ((C).ports.facet ⟨z,none⟩))
          (congrArg Prod.fst (D.external_oldPositiveAttach q w s)))) := by
    apply Equiv.ext
    intro i
    rfl
  have hh := (C).external_endpointNamedMatrix_normalized
    (D.namedCutPortFrames q w (D.portFrame g) T) pp ss true
    (D.external_oldPositiveAttach q w s) (D.external_oldEndpointPortColumns q w s true).symm
    (finCongr (D.external_oldEndpointPortParentRank q w s true)).symm
  have hc := D.external_oldCommonColumns_positive q w s hs
  have h1 := congrArg MatrixIso.linearEquiv hh
  erw [← hc,← hp] at h1
  exact h1.trans (D.external_oldEndpointPortFrame_eq q w s true g T)

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram

#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_oldNegativeEndpoint_eq
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_oldPositiveEndpoint_eq
