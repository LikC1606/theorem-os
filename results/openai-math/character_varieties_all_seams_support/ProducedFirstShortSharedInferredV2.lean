import FirstSeamShared
import ParentProducedValueDataInferredV1
import MarkedLiftFirstSide
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

local notation "J" => D.producedCutJ q hg P x b0 i0
local notation "T" => D.producedCutT q hg P x b0 i0
local notation "Y" => (T⁻¹ * J⁻¹ *
  (show (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
    (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ from g (.side ⟨q,none⟩)) * T)

def external_producedFirstSide_one_shared
    (ii : Option (Fin ((BandGraft.wiring A q B).seamArity ss))) :=
  D.external_markedLiftFirstSide_one q (w).shape rfl (w).rowRanks (w).colRanks
    hproper hmax (algebraMap R K) x.val.val b0 i0
    (D.bandCutHandleT q hg P x) (D.bandCutHandleA q hg P x)
    (D.producedMarkedFrames q hproper hmax hg P x b0 i0) ii

def external_producedFirstShortEquation_shared :=
  D.external_markedSeam_of_cut q (w).shape rfl (w).rowRanks (w).colRanks
    hproper hmax v (algebraMap R K) ss
    ((CC).external_unitSideSeam ss (algebraMap R K) cv
      (fun ii => D.external_producedFirstSide_one_shared q hproper hmax hg P x b0 i0 ii)
      (D.external_firstActualFlagFromPortFrames_shared q w g (MatrixIso.unit T) cv
        (D.parent_producedCutPortFrame q hproper hmax hg P x b0 i0) rfl))
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_producedFirstSide_one_shared
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_producedFirstShortEquation_shared
