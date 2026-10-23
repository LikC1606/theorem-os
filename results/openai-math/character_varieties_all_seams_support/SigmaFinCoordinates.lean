import NamedEndpointCancel

namespace OAI.IntegralCharacterVarieties
noncomputable section
open scoped Classical

lemma external_sigmaFinCongr_snd {α β : Type*} (e : α ≃ β)
    (d : α → ℕ) (f : β → ℕ) (h : ∀ a, d a = f (e a))
    (i : (a : α) × Fin (d a)) :
    (((Equiv.sigmaCongr e (fun a => finCongr (h a)) : ((a : α) × Fin (d a)) ≃ ((b : β) × Fin (f b)))) i).2.val = i.2.val := rfl

lemma external_sigmaFinCongr_symm_snd {α β : Type*} (e : α ≃ β)
    (d : α → ℕ) (f : β → ℕ) (h : ∀ a, d a = f (e a))
    (i : (b : β) × Fin (f b)) :
    (((Equiv.sigmaCongr e (fun a => finCongr (h a)) : ((a : α) × Fin (d a)) ≃ ((b : β) × Fin (f b)))).symm i).2.val = i.2.val := by
  obtain ⟨j, rfl⟩ := ((Equiv.sigmaCongr e (fun a => finCongr (h a)) : ((a : α) × Fin (d a)) ≃ ((b : β) × Fin (f b)))).surjective i
  rw [Equiv.symm_apply_apply]
  rfl

end
end OAI.IntegralCharacterVarieties

namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity)

lemma external_seamColumnsTransport_snd {s t : S} (he : s=t)
    (i : (j : Fin (arity s)) × Fin (D.childDim s j)) :
    (D.external_seamColumnsTransport he i).2.val = i.2.val := rfl

lemma external_portColumns_snd (p : LocalPort V D.ports.kind)
    (i : (D.vertexRanks p.1).Columns p.2) :
    (D.external_portColumns p i).2.val = i.2.val := rfl

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
