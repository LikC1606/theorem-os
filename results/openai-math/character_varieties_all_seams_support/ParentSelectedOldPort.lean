import TransportedFrameNamed
import NamedFramePortAt
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.MarkedFrames
import EndpointNormalization
import SigmaFinCoordinates
set_option quotPrecheck false
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
local notation "s0" => BandGraft.originalPort A q B 0 true
variable (s : S) (b : Bool)
local notation "pold" => (Subtype.val (D.ports.portAt b s))
local notation "pn" => (Subtype.val (BandGraft.oldPort A q B s b))

lemma external_oldEndpointChildRank
    (c : (D.ports.kind (pold).1).table.Child (pold).2) :
    ((C).vertexRanks (pn).1).rank (pn).2 (some c) =
      D.childDim s ((finCongr (congrArg (fun e => arity e.1)
        (D.ports.attach_portAt s b))) (D.ports.childEquiv pold c)) := by
  have hh := congrArg (fun d => d.rank (pold).2 (some c))
    (D.refinedCut_old_vertexRanks q w.shape rfl w.rowRanks w.colRanks (pold).1)
  change ((C).vertexRanks (.inl (pold).1)).rank (pold).2 (some c) = _
  rw [hh]
  change D.rank (D.ports.facet ⟨(D.ports.attach pold).1,some (D.ports.childEquiv pold c)⟩) = _
  have aux {s t : S} (he : s=t) (i : Fin (arity s)) :
      D.rank (D.ports.facet ⟨s,some i⟩) =
      D.rank (D.ports.facet ⟨t,some (finCongr (congrArg arity he) i)⟩) := by
    subst t
    rfl
  exact aux (congrArg Prod.fst (D.ports.attach_portAt s b)) _


def external_oldEndpointChild := (D.ports.childEquiv pold).trans
  (finCongr (congrArg (fun e => arity e.1) (D.ports.attach_portAt s b)))

def external_oldEndpointPortColumns :
    ((C).vertexRanks (pn).1).Columns (pn).2 ≃ ((i : Fin (arity s)) × Fin (D.childDim s i)) :=
  Equiv.sigmaCongr (D.external_oldEndpointChild s b) (fun c =>
    finCongr (D.external_oldEndpointChildRank q w s b c))

def external_oldEndpointNamedColumns :=
  (D.external_oldEndpointPortColumns q w s b).symm.trans ((C).external_portColumns pn)

lemma external_oldEndpointNamedColumns_grade
    (i : (j : Fin (arity s)) × Fin (D.childDim s j)) :
    (D.external_oldEndpointNamedColumns q w s b i).1.val = i.1.val := by
  change ((D.external_oldEndpointChild s b)
    ((D.external_oldEndpointChild s b).symm i.1)).val = i.1.val
  rw [Equiv.apply_symm_apply]


lemma external_oldEndpointPortFrame_eq
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    ((D.namedCutPortFrames q w (D.portFrame g) T pn).reindex
      (D.external_oldEndpointPortColumns q w s b).symm
      (finCongr (show ((C).vertexRanks (pn).1).rank (pn).2 none = D.rank (D.ports.facet ⟨s,none⟩) from by
        have hh := congrArg (fun d => d.rank (pold).2 none)
          (D.refinedCut_old_vertexRanks q w.shape rfl w.rowRanks w.colRanks (pold).1)
        exact hh.trans (congrArg (fun e : S × Bool => D.rank (D.ports.facet ⟨e.1,none⟩))
          (D.ports.attach_portAt s b)))).symm).linearEquiv =
      D.namedSeamFrame s (g (.frame s b)) := by
  have hh := LocalRanks.external_transportFrames_reindex
    (D.refinedCut_old_vertexRanks q w.shape rfl w.rowRanks w.colRanks (pold).1).symm
    (fun z => D.portFrame g ⟨(pold).1,z⟩) (pold).2
  have ho := D.external_namedFrame_port_at g pold s b (D.ports.attach_portAt s b)
  have hh2 := congrArg (fun u => ((u.reindex (D.external_portColumns pold).symm (Equiv.refl _)).reindex
    (D.external_seamColumnsTransport (congrArg Prod.fst (D.ports.attach_portAt s b))).symm
    (finCongr (congrArg (fun z => D.rank (D.ports.facet ⟨z,none⟩))
      (congrArg Prod.fst (D.ports.attach_portAt s b)))).symm).linearEquiv) hh
  have ec : (((D.external_seamColumnsTransport (congrArg Prod.fst (D.ports.attach_portAt s b))).symm.trans
      (D.external_portColumns pold).symm).trans
      (Equiv.sigmaCongr (Equiv.refl ((D.ports.kind (pold).1).table.Child (pold).2)) (fun c =>
        finCongr (congrArg (fun d => d.rank (pold).2 (some c))
          (D.refinedCut_old_vertexRanks q w.shape rfl w.rowRanks w.colRanks (pold).1).symm)))) =
      (D.external_oldEndpointPortColumns q w s b).symm := by
    have aux {α β : Type} (e f : α ≃ β) (h : e.symm=f.symm) : e=f := by
      have hh := congrArg Equiv.symm h
      exact hh
    apply aux
    apply Equiv.ext
    intro i
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Fin.ext
      rfl
  erw [MatrixIso.reindex_reindex_eq,MatrixIso.reindex_reindex_eq] at hh2
  have hfinal := hh2.trans ho
  convert hfinal using 1
  · congr 2
    exact ec.symm

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_oldEndpointPortFrame_eq
