import ParentMarkedCutLiftData
set_option autoImplicit false
set_option maxHeartbeats 0
set_option quotPrecheck false
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable TwoFlagBand MatrixExpression HomTransport
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K] [Algebra R K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (hg : 0<D.genus (D.bandCutParent q))
    (P : D.Punctures R) (x : D.Solution P K)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
local notation "w" => D.producedCutBand q hg P x b0 i0

-- Infer the proposition from the checked generic interface, preserving its sharing.
def parent_producedMarkedSideValue :=
  D.parent_markedLiftSide_rebased q (w).shape rfl (w).rowRanks (w).colRanks
    hproper hmax (algebraMap R K) x.val.val b0 i0
    (D.bandCutHandleT q hg P x) (D.bandCutHandleA q hg P x)
    (D.producedMarkedFrames q hproper hmax hg P x b0 i0)

def parent_producedMarkedPortFrame :=
  D.parent_markedLiftPortFrame q (w).shape rfl (w).rowRanks (w).colRanks
    hproper hmax (algebraMap R K) x.val.val b0 i0
    (D.bandCutHandleT q hg P x) (D.bandCutHandleA q hg P x)
    (D.producedMarkedFrames q hproper hmax hg P x b0 i0)

def parent_producedCutPortFrame :=
  D.parent_markedLiftCutPortFrame q (w).shape rfl (w).rowRanks (w).colRanks
    hproper hmax (algebraMap R K) x.val.val b0 i0
    (D.bandCutHandleT q hg P x) (D.bandCutHandleA q hg P x)
    (D.producedMarkedFrames q hproper hmax hg P x b0 i0)
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
#check OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_producedMarkedSideValue
#check OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_producedMarkedPortFrame
#check OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_producedCutPortFrame
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_producedMarkedSideValue
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_producedMarkedPortFrame
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_producedCutPortFrame
