import NamedEndpointFlagFromFrames
set_option maxHeartbeats 0
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity)
lemma external_endpointActualMatrix
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (frames : D.PortFrames (R:=K)) (he : ∀ p,D.portFrame g p=frames p)
    (p : LocalPort V D.ports.kind) (s : S) (b : Bool) (hp : D.ports.attach p=(s,b)) :
    D.external_endpointNamedMatrix frames p s b hp =
      (MatrixIso.unit (g (.frame s b))).reindex
        (blockIndex (D.childDim s)).symm (finCongr (D.seamRank s)) := by
  have hh := D.external_namedFrame_port_at g p s b hp
  rw [he p] at hh
  have hm := congrArg MatrixIso.ofLinearEquiv hh
  erw [MatrixIso.external_ofLinearEquiv_linearEquiv,MatrixIso.external_ofLinearEquiv_linearEquiv] at hm
  exact hm
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
