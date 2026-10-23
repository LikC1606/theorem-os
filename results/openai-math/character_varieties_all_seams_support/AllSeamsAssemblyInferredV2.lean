import AllSeamsFromBranchesInferredV1
import ProducedOldSeamDataInferredV3
import ProducedOriginalInternalSeamDataInferredV2
import ProducedMirrorInternalSeamDataInferredV2
import ProducedTransverseSeamsDataInferredV2
import ProducedFirstShortSharedInferredV2
import ParentProducedSelectedSeamInferredV2
import ParentProducedWrapSeamInferredV2
set_option autoImplicit false
set_option maxHeartbeats 0
set_option quotPrecheck false
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
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
local notation "C" => D.producedMarkedDiagram q hproper hmax hg P x b0 i0
local notation "v" => D.producedMarkedValues q hproper hmax hg P x b0 i0
local notation "ss" => BandGraft.originalPort A q B 0 true
local notation "CC" => D.refinedCutDiagram q (w).shape rfl (w).rowRanks (w).colRanks
local notation "cv" => D.external_markedAsCutValues q (w).shape rfl (w).rowRanks (w).colRanks hproper hmax v
local notation "g" => D.producedCutSeed q hg P x b0

theorem producedMarkedValues_allSeams :
    D.ProducedMarkedSeamEquations q hproper hmax hg P x b0 i0 := by
  dsimp only [ProducedMarkedSeamEquations]
  exact D.external_allSeamsFromBranches q hproper hmax hg P x b0 i0
    (D.external_producedOldSeam_dataV2 q hproper hmax hg P x b0 i0)
    (D.parent_producedSelectedSeamComplete q hproper hmax hg P x b0 i0)
    (D.external_producedOriginalInternalSeam_data q hproper hmax hg P x b0 i0)
    (D.external_producedMirrorInternalSeam_data q hproper hmax hg P x b0 i0)
    (D.external_producedTransversePlus_dataSeam q hproper hmax hg P x b0 i0)
    (D.external_producedTransverseMinus_dataSeam q hproper hmax hg P x b0 i0)
    (D.external_producedFirstShortEquation_shared q hproper hmax hg P x b0 i0)
    (D.parent_producedWrapSeamComplete q hproper hmax hg P x b0 i0)
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
#check OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.producedMarkedValues_allSeams
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.producedMarkedValues_allSeams
