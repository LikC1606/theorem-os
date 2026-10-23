import OriginalInternalSeam
import ParentProducedValueDataInferredV1
import InternalSideValues
import OAI.AlgebraicGeometry.CharacterVarieties.Seams.ProducedEquations
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
local notation "g" => D.producedCutSeed q hg P x b0

local notation "J" => D.producedCutJ q hg P x b0 i0
local notation "T" => D.producedCutT q hg P x b0 i0
local notation "Y" => (T⁻¹ * J⁻¹ *
  (show (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
    (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ from g (.side ⟨q,none⟩)) * T)
local notation "cv" => D.external_markedAsCutValues q (w).shape rfl (w).rowRanks (w).colRanks hproper hmax v

def external_producedOriginalInternalSide_one_data (jj : Fin (w).shape.atomicBand.length)
    (ii : Option (Fin ((BandGraft.wiring A q B).seamArity (BandGraft.originalPort A q B jj.succ true)))) :=
  (D.parent_producedMarkedSideValue q hproper hmax hg P x b0 i0 ⟨BandGraft.originalPort A q B jj.succ true,ii⟩).trans
    (D.external_originalInternalSide_one q (w).shape rfl (w).rowRanks (w).colRanks
      (fun a => g (.side a)) J Y jj ii)

def external_producedOriginalInternalSeam_data (jj : Fin (w).shape.atomicBand.length) :=
  D.external_markedSeam_of_cut q (w).shape rfl (w).rowRanks (w).colRanks
    hproper hmax v (algebraMap R K) (BandGraft.originalPort A q B jj.succ true)
    (D.external_originalInternalSeam q w jj (algebraMap R K) cv
      (D.portFrame g) (MatrixIso.unit T)
      (D.parent_producedCutPortFrame q hproper hmax hg P x b0 i0)
      (fun ii => D.external_producedOriginalInternalSide_one_data q hproper hmax hg P x b0 i0 jj ii))
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_producedOriginalInternalSide_one_data
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_producedOriginalInternalSeam_data
