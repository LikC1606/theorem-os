import TransverseSeamV2
import TransverseSideAttachGeneric
import TransverseNonprincipal
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

def external_producedTransversePlus_dataSide_one (aa : {a : {p : PortAt (B).kind true // p∉Set.range (VariableGallery.internalPlus (B).kind)} // a≠(B).shortFirst})
    (ii : Option (Fin ((BandGraft.wiring A q B).seamArity (graftPlus A (B).doublePatch (.inr (.inl (.inr (.inl aa)))))))) :=
  (D.parent_producedMarkedSideValue q hproper hmax hg P x b0 i0 ⟨graftPlus A (B).doublePatch (.inr (.inl (.inr (.inl aa)))),ii⟩).trans
    (BandGraft.external_transversePlusSide_generic A q B aa
      (D.ports.refinedRank q (w).shape D.rank)
      (D.cutOldSideValues q (fun a => g (.side a)) J)
      (D.cutShortSideValues q Y) ii)

def external_producedTransversePlus_dataSeam (aa : {a : {p : PortAt (B).kind true // p∉Set.range (VariableGallery.internalPlus (B).kind)} // a≠(B).shortFirst}) :=
  D.external_markedSeam_of_cut q (w).shape rfl (w).rowRanks (w).colRanks
    hproper hmax v (algebraMap R K) (graftPlus A (B).doublePatch (.inr (.inl (.inr (.inl aa)))))
    (D.external_transverseSeam q w (aa.val.val.val.1) (aa.val.val.val.2)
      (graftPlus A (B).doublePatch (.inr (.inl (.inr (.inl aa))))) true
      (BandGraft.external_transversePlusOrigAttach_generic A q B aa)
      (BandGraft.external_transversePlusMirrorAttach_generic A q B aa)
      (algebraMap R K) cv (D.portFrame g) (MatrixIso.unit T)
      (VariableGallery.external_positive_ne_input (B).kind aa.val aa.property) (VariableGallery.external_positive_ne_output (B).kind aa.val)
      (D.parent_producedCutPortFrame q hproper hmax hg P x b0 i0)
      (fun ii => D.external_producedTransversePlus_dataSide_one q hproper hmax hg P x b0 i0 aa ii))

def external_producedTransverseMinus_dataSide_one (bb : {a : {p : PortAt (B).kind false // p∉Set.range (VariableGallery.internalMinus (B).kind)} // a≠(B).shortLast})
    (ii : Option (Fin ((BandGraft.wiring A q B).seamArity (graftPlus A (B).doublePatch (.inr (.inl (.inr (.inr bb)))))))) :=
  (D.parent_producedMarkedSideValue q hproper hmax hg P x b0 i0 ⟨graftPlus A (B).doublePatch (.inr (.inl (.inr (.inr bb)))),ii⟩).trans
    (BandGraft.external_transverseMinusSide_generic A q B bb
      (D.ports.refinedRank q (w).shape D.rank)
      (D.cutOldSideValues q (fun a => g (.side a)) J)
      (D.cutShortSideValues q Y) ii)

def external_producedTransverseMinus_dataSeam (bb : {a : {p : PortAt (B).kind false // p∉Set.range (VariableGallery.internalMinus (B).kind)} // a≠(B).shortLast}) :=
  D.external_markedSeam_of_cut q (w).shape rfl (w).rowRanks (w).colRanks
    hproper hmax v (algebraMap R K) (graftPlus A (B).doublePatch (.inr (.inl (.inr (.inr bb)))))
    (D.external_transverseSeam q w (bb.val.val.val.1) (bb.val.val.val.2)
      (graftPlus A (B).doublePatch (.inr (.inl (.inr (.inr bb))))) false
      (BandGraft.external_transverseMinusOrigAttach_generic A q B bb)
      (BandGraft.external_transverseMinusMirrorAttach_generic A q B bb)
      (algebraMap R K) cv (D.portFrame g) (MatrixIso.unit T)
      (VariableGallery.external_negative_ne_input (B).kind bb.val) (VariableGallery.external_negative_ne_output (B).kind bb.val bb.property)
      (D.parent_producedCutPortFrame q hproper hmax hg P x b0 i0)
      (fun ii => D.external_producedTransverseMinus_dataSide_one q hproper hmax hg P x b0 i0 bb ii))
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_producedTransversePlus_dataSide_one
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_producedTransversePlus_dataSeam
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_producedTransverseMinus_dataSide_one
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_producedTransverseMinus_dataSeam
