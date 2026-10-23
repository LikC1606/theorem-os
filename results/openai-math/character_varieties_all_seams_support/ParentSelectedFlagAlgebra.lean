import OAI.AlgebraicGeometry.CharacterVarieties.Frames.Endpoints
namespace OAI.IntegralCharacterVarieties
noncomputable section
variable {R α V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  (a : α → ℕ)

lemma parent_sameFramedFlag_trans {e f g : (α → R) ≃ₗ[R] V}
    (h1 : SameFramedFlag a e f) (h2 : SameFramedFlag a f g) : SameFramedFlag a e g := by
  refine ⟨fun k => (h1.1 k).trans (h2.1 k), ?_⟩
  intro k v hv
  exact (h1.2 k v hv).trans (h2.2 k v (by rw [← h1.1 (k+1)]; exact hv))

lemma parent_sameFramedFlag_post {e f : (α → R) ≃ₗ[R] V}
    (h : SameFramedFlag a e f) (t : V ≃ₗ[R] W) :
    SameFramedFlag a (e.trans t) (f.trans t) := by
  apply (sameFramedFlag_iff a _ _).mpr
  have he : (e.trans t).trans (f.trans t).symm = e.trans f.symm := by
    apply LinearEquiv.ext
    intro v
    simp
  rw [he]
  exact (sameFramedFlag_iff a e f).mp h

lemma parent_selectedFlag_algebra
    {e f p : (α → R) ≃ₗ[R] V} (j : V ≃ₗ[R] V)
    (hfirst : SameFramedFlag a e (f.trans j.symm))
    (hseed : SameFramedFlag a f p) :
    SameFramedFlag a (e.trans j) p := by
  have hh := parent_sameFramedFlag_post a hfirst j
  have he : (f.trans j.symm).trans j = f := by
    apply LinearEquiv.ext
    intro v
    simp
  rw [he] at hh
  exact parent_sameFramedFlag_trans a hh hseed
end
end OAI.IntegralCharacterVarieties
