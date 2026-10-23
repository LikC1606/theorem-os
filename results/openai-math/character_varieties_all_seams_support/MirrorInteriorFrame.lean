import OAI.AlgebraicGeometry.CharacterVarieties.Frames.Mirror
set_option maxHeartbeats 0
namespace OAI.IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
noncomputable section
open scoped Classical
open TwoFlagBand OccurrenceIncidence VertexTable
variable {K : Type} [Field K] {n r : ℕ} {s : Fin n → ℕ}
    {f h : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K)}
    (w : IdentifiedBand s f h)

lemma external_mirror_color (v : Fin (w.shape.atomicBand.length+1))
    (p : (w.shape.atomicBand.kind v).table.Port)
    (a : Option ((w.shape.atomicBand.kind v).table.Child p)) :
    (w.shape.atomicBand.decoration v).mirror.color
      ⟨(w.shape.atomicBand.kind v).mirrorPort p,a.map ((w.shape.atomicBand.kind v).mirrorChild p)⟩=
      (w.shape.atomicBand.decoration v).color ⟨p,a⟩ := by
  change (w.shape.atomicBand.decoration v).color
    ((w.shape.atomicBand.kind v).mirrorEnd.symm ((w.shape.atomicBand.kind v).mirrorEnd ⟨p,a⟩))=_
  rw [Equiv.symm_apply_apply]

def external_mirrorInteriorChild (j : Fin w.shape.atomicBand.length) :
    (w.shape.atomicBand.kind j.castSucc).mirror.table.Child
      ((w.shape.atomicBand.kind j.castSucc).mirrorPort (w.shape.atomicBand.kind j.castSucc).output) ≃
    (w.shape.atomicBand.kind j.succ).mirror.table.Child
      ((w.shape.atomicBand.kind j.succ).mirrorPort (w.shape.atomicBand.kind j.succ).input) :=
  ((w.shape.atomicBand.kind j.castSucc).mirrorChild _).symm.trans
    ((w.interiorChild j).trans ((w.shape.atomicBand.kind j.succ).mirrorChild _))

lemma external_mirrorInteriorParent (j : Fin w.shape.atomicBand.length) :
    (w.shape.atomicBand.decoration j.castSucc).mirror.color
      ⟨(w.shape.atomicBand.kind j.castSucc).mirrorPort (w.shape.atomicBand.kind j.castSucc).output,none⟩=
    (w.shape.atomicBand.decoration j.succ).mirror.color
      ⟨(w.shape.atomicBand.kind j.succ).mirrorPort (w.shape.atomicBand.kind j.succ).input,none⟩ := by
  have h1 := w.external_mirror_color j.castSucc (w.shape.atomicBand.kind j.castSucc).output none
  have h2 := w.external_mirror_color j.succ (w.shape.atomicBand.kind j.succ).input none
  simp only [Option.map_none] at h1 h2
  exact h1.trans ((w.interior_parent j).trans h2.symm)

lemma external_mirrorInteriorChildColor (j : Fin w.shape.atomicBand.length) (a) :
    (w.shape.atomicBand.decoration j.castSucc).mirror.color
      ⟨(w.shape.atomicBand.kind j.castSucc).mirrorPort (w.shape.atomicBand.kind j.castSucc).output,some a⟩=
    (w.shape.atomicBand.decoration j.succ).mirror.color
      ⟨(w.shape.atomicBand.kind j.succ).mirrorPort (w.shape.atomicBand.kind j.succ).input,
        some (w.external_mirrorInteriorChild j a)⟩ := by
  obtain ⟨b,rfl⟩ := ((w.shape.atomicBand.kind j.castSucc).mirrorChild
    (w.shape.atomicBand.kind j.castSucc).output).surjective a
  have hi : w.external_mirrorInteriorChild j
      (((w.shape.atomicBand.kind j.castSucc).mirrorChild _) b)=
      ((w.shape.atomicBand.kind j.succ).mirrorChild _) (w.interiorChild j b) := by
    simp only [external_mirrorInteriorChild,Equiv.trans_apply,Equiv.symm_apply_apply]
  rw [hi]
  have h1 := w.external_mirror_color j.castSucc (w.shape.atomicBand.kind j.castSucc).output (some b)
  have h2 := w.external_mirror_color j.succ (w.shape.atomicBand.kind j.succ).input (some (w.interiorChild j b))
  simp only [Option.map_some] at h1 h2
  exact h1.trans ((w.interior_child j b).trans h2.symm)

lemma external_mirrorInteriorFrame (T : MatrixIso K (Fin r) (Fin r))
    (j : Fin w.shape.atomicBand.length) :
    (w.mirrorVertexFrames T j.succ
      ((w.shape.atomicBand.kind j.succ).mirrorPort (w.shape.atomicBand.kind j.succ).input)).reindex
      ((w.shape.vertexAtoms j.castSucc).mirror.seamColumns (w.shape.vertexAtoms j.succ).mirror
        _ _ (w.external_mirrorInteriorChild j)
        (fun a => congrArg w.shape.facetAtoms (w.external_mirrorInteriorChildColor j a)))
      (finCongr ((w.shape.vertexAtoms j.castSucc).mirror.rank_of_atoms (w.shape.vertexAtoms j.succ).mirror
        (congrArg w.shape.facetAtoms (w.external_mirrorInteriorParent j))))=
    w.mirrorVertexFrames T j.castSucc
      ((w.shape.atomicBand.kind j.castSucc).mirrorPort (w.shape.atomicBand.kind j.castSucc).output) := by
  apply (w.shape.vertexAtoms j.castSucc).mirror.reframe_seam (w.shape.vertexAtoms j.succ).mirror
    (w.mirrorVertexBases T j.castSucc) (w.mirrorVertexBases T j.succ) _ _
    (w.external_mirrorInteriorChild j)
    (congrArg w.shape.facetAtoms (w.external_mirrorInteriorParent j))
    (fun a => congrArg w.shape.facetAtoms (w.external_mirrorInteriorChildColor j a))
  · exact MatrixIso.finite_basis_transport _ (w.mirrorColorGauge T) _ _ _ _ _ _
      (w.external_mirrorInteriorParent j) _
  · intro a
    exact MatrixIso.finite_basis_transport _ (w.mirrorColorGauge T) _ _ _ _ _ _
      (w.external_mirrorInteriorChildColor j a) _
end
end OAI.IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
