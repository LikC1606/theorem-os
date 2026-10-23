import ParentSelectedFlagAlgebra
namespace OAI.IntegralCharacterVarieties
noncomputable section
variable {R α V : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] (a : α → ℕ)

lemma parent_wrapFlag_algebra
    {f l : (α → R) ≃ₗ[R] V} (p j t : V ≃ₗ[R] V)
    (h : SameFramedFlag a l ((f.trans p).trans j.symm)) :
    SameFramedFlag a
      ((f.trans t.symm).trans (((t.trans p).trans j.symm).trans t.symm))
      (l.trans t.symm) := by
  have hs : SameFramedFlag a ((f.trans p).trans j.symm) l := by
    refine ⟨fun k => (h.1 k).symm, ?_⟩
    intro k v hv
    exact (h.2 k v (by rw [h.1 (k+1)]; exact hv)).symm
  have hp := parent_sameFramedFlag_post a hs t.symm
  have he : (f.trans t.symm).trans (((t.trans p).trans j.symm).trans t.symm) =
      ((f.trans p).trans j.symm).trans t.symm := by
    apply LinearEquiv.ext
    intro v
    simp
  rw [he]
  exact hp
end
end OAI.IntegralCharacterVarieties
#print axioms OAI.IntegralCharacterVarieties.parent_wrapFlag_algebra
