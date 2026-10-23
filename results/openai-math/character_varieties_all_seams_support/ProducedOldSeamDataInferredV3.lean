import OldSeamFromValuesV2
import ParentProducedValueDataInferredV1
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
local notation "CC" => D.refinedCutDiagram q (w).shape rfl (w).rowRanks (w).colRanks
local notation "cv" => D.external_markedAsCutValues q (w).shape rfl (w).rowRanks (w).colRanks hproper hmax v
local notation "g" => D.producedCutSeed q hg P x b0

variable (s : S)
local notation "ss" => BandGraft.oldPort A q B s true
local notation "Y" => ((D.producedCutT q hg P x b0 i0)⁻¹ * (D.producedCutJ q hg P x b0 i0)⁻¹ *
  (show (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
    (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ from g (.side ⟨q,none⟩)) *
    D.producedCutT q hg P x b0 i0)

local notation "J" => D.producedCutJ q hg P x b0 i0
local notation "T" => D.producedCutT q hg P x b0 i0

def external_producedOldParent_dataInferred (hs : s≠q) :=
  (congrArg (fun U => (MatrixIso.unit U).reindex
    (D.external_oldSideParent q (w).shape rfl (w).rowRanks (w).colRanks s)
    (D.external_oldSideParent q (w).shape rfl (w).rowRanks (w).colRanks s))
    (D.parent_producedMarkedSideValue q hproper hmax hg P x b0 i0 ⟨ss,none⟩)).trans
    (D.external_oldParentTransport q (w).shape rfl (w).rowRanks (w).colRanks s
      (fun a => g (.side a)) J Y hs)

def external_producedOldChild_dataInferred :=
  (congrArg (fun ds : (j : Fin ((BandGraft.wiring A q B).seamArity ss)) →
      MatrixIso K (Fin ((CC).childDim ss j)) (Fin ((CC).childDim ss j)) =>
      (MatrixIso.block ds).reindex
        (D.external_oldSideColumns q (w).shape rfl (w).rowRanks (w).colRanks s)
        (D.external_oldSideColumns q (w).shape rfl (w).rowRanks (w).colRanks s))
    (funext (fun ii => congrArg (fun U => MatrixIso.unit U⁻¹)
      (D.parent_producedMarkedSideValue q hproper hmax hg P x b0 i0 ⟨ss,some ii⟩)))).trans
    (D.external_oldChildInverseTransport q (w).shape rfl (w).rowRanks (w).colRanks s
      (fun a => g (.side a)) J Y)

def external_producedOldSeam_dataV2 (hs : s≠q) :=
  D.external_markedSeam_of_cut q (w).shape rfl (w).rowRanks (w).colRanks
    hproper hmax v (algebraMap R K) ss
    (D.external_oldSeamFromValues q w s hs (algebraMap R K) g (MatrixIso.unit T) cv
      (D.parent_producedCutPortFrame q hproper hmax hg P x b0 i0)
      (D.external_producedOldParent_dataInferred q hproper hmax hg P x b0 i0 s hs)
      (D.external_producedOldChild_dataInferred q hproper hmax hg P x b0 i0 s)
      (D.producedCutSeed_namedSeam q hg P x b0 s))
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_producedOldParent_dataInferred
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_producedOldChild_dataInferred
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_producedOldSeam_dataV2
