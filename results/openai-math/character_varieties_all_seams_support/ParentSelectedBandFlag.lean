import ParentSelectedFlagAlgebra
import OAI.AlgebraicGeometry.CharacterVarieties.Seams.ProducedEquations
set_option maxHeartbeats 0
set_option quotPrecheck false
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K] [Algebra R K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (hg : 0 < D.genus (D.bandCutParent q))
    (P : D.Punctures R) (x : D.Solution P K)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
local notation "w" => D.producedCutBand q hg P x b0 i0
local notation "seed" => D.producedCutSeed q hg P x b0

lemma parent_selectedBandFlag :
    SameFramedFlag (fun i : (j : Fin (arity q)) × Fin (D.childDim q j) => i.1.val)
      ((w).lastFrame.trans (MatrixIso.unit (D.producedCutJ q hg P x b0 i0)).linearEquiv)
      ((D.namedChildInverse q seed).trans
        (D.namedSeamFrame q (seed (.frame q true)))) := by
  exact parent_selectedFlag_algebra _
    (MatrixIso.unit (D.producedCutJ q hg P x b0 i0)).linearEquiv
    (w).lastFrame_holds (D.producedCutSeed_namedSeam q hg P x b0 q)

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
