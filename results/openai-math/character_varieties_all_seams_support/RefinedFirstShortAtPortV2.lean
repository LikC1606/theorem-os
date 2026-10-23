import OAI.AlgebraicGeometry.CharacterVarieties.Seams.ProducedDiagram
import BandFirstShortValues
set_option maxHeartbeats 0
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {r : ℕ} (d : TwoFlagBand.RankShape (arity q) (arity q) r)
    (hp : D.rank (D.ports.facet ⟨q,none⟩)=r)
    (hc : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.row i))
    (hc' : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.col i))
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q d)
local notation "B" => D.ports.refinedBandForSeam q d
local notation "C" => D.refinedCutDiagram q d hp hc hc'
local notation "s0" => BandGraft.originalSide A q B 0

lemma external_refinedFirstShortSideValuesAtPortV2 (old : D.SideValues (R:=K))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
    (i : Option (Fin ((BandGraft.wiring A q B).seamArity
      (BandGraft.originalPort A q B 0 true)))) :
    D.refinedCutSideValues q d hp hc hc' old J Y
      ⟨BandGraft.originalPort A q B 0 true,i⟩=1 := by
  exact BandGraft.external_bandValues_first_one A q B
    (D.ports.refinedRank q d D.rank) (D.cutOldSideValues q old J) (D.cutShortSideValues q Y)
    (by intro j; cases j <;> rfl) i

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_refinedFirstShortSideValuesAtPortV2
