import EndpointNormalization
namespace OAI.IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
noncomputable section
open scoped Classical Matrix
variable {R : Type} [CommRing R] {k : Kind} {d e : LocalRanks k}

lemma external_transportFrames_reindex_extra (h : d=e)
    (f : (p : k.table.Port) → MatrixIso R (d.Columns p) (d.Parent p))
    (p : k.table.Port) {α β : Type*} [Fintype α] [Fintype β]
    (a : α ≃ d.Columns p) (b : β ≃ d.Parent p) :
    (transportFrames h f p).reindex
      (a.trans (Equiv.sigmaCongr (Equiv.refl _) (fun c =>
        finCongr (congrArg (fun z : LocalRanks k => z.rank p (some c)) h))))
      (b.trans (finCongr (congrArg (fun z : LocalRanks k => z.rank p none) h))) =
      (f p).reindex a b := by
  have hh := external_transportFrames_reindex h f p
  have hh' := congrArg (fun u => u.reindex a b) hh
  rw [MatrixIso.reindex_reindex_eq] at hh'
  exact hh'

end
end OAI.IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
