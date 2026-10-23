import ParentSelectedEndpointsModular
import ParentSelectedSideTransport
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
lemma parent_selectedSideColumns_eq :
    D.external_oldSideColumns q w.shape rfl w.rowRanks w.colRanks q =
      D.parent_selectedCommonColumns q w := by
  apply Equiv.ext
  intro i
  have he : (D.external_oldSideColumns q w.shape rfl w.rowRanks w.colRanks q i).1 =
      (D.parent_selectedCommonColumns q w i).1 := by
    apply Fin.ext
    exact (D.parent_selectedCommonColumns_grade q w i).symm
  apply Sigma.ext he
  apply (Fin.heq_ext_iff (congrArg ((C).childDim ss) he)).2
  have h1 := (C).external_seamColumnsTransport_snd
    (congrArg Prod.fst (D.parent_selectedPositiveAttach q w))
    (D.external_oldEndpointNamedColumns q w q true i)
  have h2 := D.parent_selectedPositiveNamedColumns_snd q w i
  exact (h1.trans h2).symm
lemma parent_selectedSideParent_eq :
    D.external_oldSideParent q w.shape rfl w.rowRanks w.colRanks q =
      D.parent_selectedCommonParent q w := by
  apply Equiv.ext
  intro i
  rfl
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_selectedSideColumns_eq
