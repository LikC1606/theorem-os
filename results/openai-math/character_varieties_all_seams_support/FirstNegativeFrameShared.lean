import FirstCommonEqualityV3
import TransportedFrameNamed
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
local notation "s0" => BandGraft.originalPort A q B 0 true
local notation "pold" => (Subtype.val (D.ports.portAt false q))
local notation "pn" => (Subtype.val (BandGraft.oldPort A q B q false))

lemma external_firstNegativePortFrame_eq
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    ((D.namedCutPortFrames q w (D.portFrame g) T pn).reindex
      (D.external_firstNegativePortColumns q w).symm
      (finCongr (show ((C).vertexRanks (pn).1).rank (pn).2 none = D.rank (D.ports.facet ⟨q,none⟩) from by
        have hh := congrArg (fun d => d.rank (pold).2 none)
          (D.refinedCut_old_vertexRanks q w.shape rfl w.rowRanks w.colRanks (pold).1)
        exact hh.trans (congrArg (fun e : S × Bool => D.rank (D.ports.facet ⟨e.1,none⟩))
          (D.ports.attach_portAt q false)))).symm).linearEquiv =
      D.namedSeamFrame q (g (.frame q false)) := by
  have hh := LocalRanks.external_transportFrames_reindex
    (D.refinedCut_old_vertexRanks q w.shape rfl w.rowRanks w.colRanks (pold).1).symm
    (fun z => D.portFrame g ⟨(pold).1,z⟩) (pold).2
  have ho := D.external_namedFrame_port_at g pold q false (D.ports.attach_portAt q false)
  have hh2 := congrArg (fun u => ((u.reindex (D.external_portColumns pold).symm (Equiv.refl _)).reindex
    (D.external_seamColumnsTransport (congrArg Prod.fst (D.ports.attach_portAt q false))).symm
    (finCongr (congrArg (fun z => D.rank (D.ports.facet ⟨z,none⟩))
      (congrArg Prod.fst (D.ports.attach_portAt q false)))).symm).linearEquiv) hh
  have ec : (((D.external_seamColumnsTransport (congrArg Prod.fst (D.ports.attach_portAt q false))).symm.trans
      (D.external_portColumns pold).symm).trans
      (Equiv.sigmaCongr (Equiv.refl ((D.ports.kind (pold).1).table.Child (pold).2)) (fun c =>
        finCongr (congrArg (fun d => d.rank (pold).2 (some c))
          (D.refinedCut_old_vertexRanks q w.shape rfl w.rowRanks w.colRanks (pold).1).symm)))) =
      (D.external_firstNegativePortColumns q w).symm := by
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

#check OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_firstNegativePortFrame_eq
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_firstNegativePortFrame_eq
