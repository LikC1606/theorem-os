import MatrixReindexCancel
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity)

lemma external_endpointNamedMatrix_normalized
    (frames : D.PortFrames (R:=K)) (p : LocalPort V D.ports.kind)
    (s : S) (b : Bool) (hp : D.ports.attach p=(s,b))
    {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ (D.vertexRanks p.1).Columns p.2)
    (f : β ≃ (D.vertexRanks p.1).Parent p.2) :
    (D.external_endpointNamedMatrix frames p s b hp).reindex
      ((e.trans (D.external_portColumns p)).trans
        (D.external_seamColumnsTransport (congrArg Prod.fst hp)))
      (f.trans (finCongr (congrArg (fun z => D.rank (D.ports.facet ⟨z,none⟩))
        (congrArg Prod.fst hp)))) = (frames p).reindex e f := by
  erw [D.external_endpointNamedMatrix_reindex_cancel]
  erw [MatrixIso.reindex_reindex_eq]
  have he : (e.trans (D.external_portColumns p)).trans
      (D.external_portColumns p).symm=e := by
    apply Equiv.ext
    intro i
    exact (D.external_portColumns p).symm_apply_apply _
  erw [he]
  rfl

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
