import NamedEndpointFlag

namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity)

lemma external_endpointNamedMatrix_reindex_cancel
    (frames : D.PortFrames (R:=K))
    (p : LocalPort V D.ports.kind) (s : S) (b : Bool)
    (hp : D.ports.attach p=(s,b))
    {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ ((i : Fin (arity (D.ports.attach p).1)) ×
      Fin (D.childDim (D.ports.attach p).1 i)))
    (f : β ≃ Fin (D.rank (D.ports.facet ⟨(D.ports.attach p).1,none⟩))) :
    (D.external_endpointNamedMatrix frames p s b hp).reindex
      (e.trans (D.external_seamColumnsTransport (congrArg Prod.fst hp)))
      (f.trans (finCongr (congrArg (fun z => D.rank (D.ports.facet ⟨z,none⟩))
        (congrArg Prod.fst hp)))) =
      ((frames p).reindex (D.external_portColumns p).symm (Equiv.refl _)).reindex e f := by
  unfold external_endpointNamedMatrix
  erw [MatrixIso.reindex_reindex_eq]

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
