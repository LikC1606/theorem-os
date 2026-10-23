import SigmaFinCoordinates
namespace OAI.IntegralCharacterVarieties.MatrixIso
noncomputable section
open scoped Classical Matrix
variable {R α β γ δ ε : Type*} [CommRing R]
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ε]

lemma external_reindex_column_cancel (x : MatrixIso R α β)
    (a : α ≃ γ) (b : α ≃ δ) (f : ε ≃ β) :
    (x.reindex a.symm (Equiv.refl β)).reindex (b.symm.trans a) f =
      x.reindex b.symm f := by
  rw [reindex_reindex_eq]
  have he : (b.symm.trans a).trans a.symm=b.symm := by
    apply Equiv.ext
    intro i
    exact a.symm_apply_apply _
  rw [he]
  rfl

end
end OAI.IntegralCharacterVarieties.MatrixIso
