import ParentProducedValueDataInferredV1
import ParentSelectedFromSides
import ParentSelectedSideEndpointCoordinates
import ParentSelectedBandFlag
set_option autoImplicit false
set_option maxHeartbeats 0
set_option quotPrecheck false
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable TwoFlagBand MatrixExpression HomTransport NamedBandGrades
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K] [Algebra R K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (hg : 0<D.genus (D.bandCutParent q))
    (P : D.Punctures R) (x : D.Solution P K)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
local notation "w" => D.producedCutBand q hg P x b0 i0
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q (w).shape)
local notation "B" => D.ports.refinedBandForSeam q (w).shape
local notation "CC" => D.refinedCutDiagram q (w).shape rfl (w).rowRanks (w).colRanks
local notation "MM" => D.producedMarkedDiagram q hproper hmax hg P x b0 i0
local notation "z" => D.producedMarkedValues q hproper hmax hg P x b0 i0
local notation "seed" => D.producedCutSeed q hg P x b0
local notation "cv" => D.external_markedAsCutValues q (w).shape rfl (w).rowRanks (w).colRanks hproper hmax z
local notation "J" => D.producedCutJ q hg P x b0 i0
local notation "T" => D.producedCutT q hg P x b0 i0
local notation "Y" => (T⁻¹*J⁻¹*(show (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
  (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ from seed (.side ⟨q,none⟩))*T)
local notation "ss" => BandGraft.oldPort A q B q true
def parent_producedSelectedSeamComplete :=
  D.external_markedSeam_of_cut q (w).shape rfl (w).rowRanks (w).colRanks
    hproper hmax z (algebraMap R K) ss
    (D.parent_selectedSeam_fromSides q w (algebraMap R K) cv seed (MatrixIso.unit T) J Y
      (D.parent_producedCutPortFrame q hproper hmax hg P x b0 i0)
      (D.parent_producedMarkedSideValue q hproper hmax hg P x b0 i0)
      (D.parent_selectedBandFlag q hg P x b0 i0))
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_producedSelectedSeamComplete
