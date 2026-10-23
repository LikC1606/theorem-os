import OAI.AlgebraicGeometry.CharacterVarieties.Frames.Mirror
set_option maxHeartbeats 0

namespace OAI.IntegralCharacterVarieties.MatrixIso
noncomputable section
open scoped Classical
variable {R α β γ δ : Type*} [CommRing R] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
lemma external_reindex_injective (a : γ ≃ α) (b : δ ≃ β) :
    Function.Injective (fun x : MatrixIso R α β => x.reindex a b) := by
  intro x y h
  have hh := congrArg (fun z => z.reindex a.symm b.symm) h
  simpa only [reindex_reindex_eq, Equiv.symm_trans_self, reindex_refl_eq] using hh
end
end OAI.IntegralCharacterVarieties.MatrixIso

namespace OAI.IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
noncomputable section
open scoped Classical
open TwoFlagBand OccurrenceIncidence VertexTable
variable {K : Type} [Field K] {n r : ℕ} {s : Fin n → ℕ}
    {f h : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K)}
    (w : IdentifiedBand s f h)

lemma external_principal_color (v : Fin (w.shape.atomicBand.length+1))
    (p : (w.shape.atomicBand.kind v).table.Port)
    (hp : p=(w.shape.atomicBand.kind v).input ∨ p=(w.shape.atomicBand.kind v).output) :
    (w.shape.atomicBand.decoration v).color ⟨p,none⟩=none := by
  rcases hp with rfl|rfl
  · exact w.shape.atomicBand.parent_input v
  · exact w.shape.atomicBand.parent_output v

lemma external_principal_rank (v : Fin (w.shape.atomicBand.length+1))
    (p : (w.shape.atomicBand.kind v).table.Port)
    (hp : p=(w.shape.atomicBand.kind v).input ∨ p=(w.shape.atomicBand.kind v).output) :
    (w.shape.vertexAtoms v).rank ⟨p,none⟩=r :=
  (w.shape.vertexAtoms_rank v _).trans
    (congrArg (freshRank r w.shape.secondaryRank) (w.external_principal_color v p hp))

lemma external_mirror_basis_normalized (T : MatrixIso K (Fin r) (Fin r))
    (v : Fin (w.shape.atomicBand.length+1))
    (z : (p : (w.shape.atomicBand.kind v).table.Port) × Option ((w.shape.atomicBand.kind v).table.Child p))
    (hz : (w.shape.atomicBand.decoration v).color z=none)
    (hr : (w.shape.vertexAtoms v).mirror.rank ((w.shape.atomicBand.kind v).mirrorEnd z)=r) :
    ((w.mirrorVertexBases T v).basis ((w.shape.atomicBand.kind v).mirrorEnd z).1
      ((w.shape.atomicBand.kind v).mirrorEnd z).2).reindex
        (finCongr hr).symm (finCongr hr).symm =
      (w.colorGauge none).trans T.symm := by
  let e := (w.shape.atomicBand.kind v).mirrorEnd
  have hc : (w.shape.atomicBand.decoration v).color (e.symm (e z))=none :=
    (congrArg (w.shape.atomicBand.decoration v).color (e.symm_apply_apply z)).trans hz
  have hh := MatrixIso.finite_basis_transport (freshRank r w.shape.secondaryRank) (w.mirrorColorGauge T)
    none ((w.shape.atomicBand.decoration v).color (e.symm (e z)))
    r ((w.shape.vertexAtoms v).mirror.rank (e z))
    rfl (w.shape.vertexAtoms_rank v (e.symm (e z))) hc.symm hr.symm
  change (((w.mirrorColorGauge T ((w.shape.atomicBand.decoration v).color (e.symm (e z)))).reindex
    (finCongr (w.shape.vertexAtoms_rank v (e.symm (e z))))
    (finCongr (w.shape.vertexAtoms_rank v (e.symm (e z))))).reindex
    (finCongr hr.symm) (finCongr hr.symm))=(w.mirrorColorGauge T none)
  exact hh.trans (by apply MatrixIso.ext <;> rfl)

lemma external_mirror_principal_basis (T : MatrixIso K (Fin r) (Fin r))
    (v : Fin (w.shape.atomicBand.length+1))
    (p : (w.shape.atomicBand.kind v).table.Port)
    (hp : p=(w.shape.atomicBand.kind v).input ∨ p=(w.shape.atomicBand.kind v).output) :
    let ep := finCongr ((w.shape.vertexAtoms v).rank_of_atoms (w.shape.vertexAtoms v).mirror
      ((w.shape.vertexAtoms v).mirror_atoms ⟨p,none⟩).symm)
    ((w.mirrorVertexBases T v).basis ((w.shape.atomicBand.kind v).mirrorPort p) none).reindex ep ep =
      ((w.vertexBases v).basis p none).trans
        (T.symm.reindex (finCongr (w.external_principal_rank v p hp))
          (finCongr (w.external_principal_rank v p hp))) := by
  dsimp only
  let atom := w.shape.vertexAtoms v
  let k := w.shape.atomicBand.kind v
  let rankP := w.external_principal_rank v p hp
  let rankM := atom.rank_of_atoms atom.mirror (atom.mirror_atoms ⟨p,none⟩).symm
  let ep := finCongr rankM
  let er := finCongr rankP
  have hr : atom.mirror.rank (k.mirrorEnd ⟨p,none⟩)=r := rankM.symm.trans rankP
  have hn := w.external_mirror_basis_normalized T v ⟨p,none⟩
    (w.external_principal_color v p hp) hr
  have hb := w.basis_at_color v p none none (w.external_principal_color v p hp) rankP
  have tnorm : (T.symm.reindex er er).reindex er.symm er.symm=T.symm := by
    apply MatrixIso.ext <;> rfl
  have rhsNorm := MatrixIso.reindex_trans ((w.vertexBases v).basis p none)
    (T.symm.reindex er er) er.symm er.symm er.symm
  have rhsSimple : (((w.vertexBases v).basis p none).trans
      (T.symm.reindex er er)).reindex er.symm er.symm =
      (w.colorGauge none).trans T.symm :=
    rhsNorm.trans (congrArg₂ MatrixIso.trans hb tnorm)
  exact MatrixIso.external_reindex_injective er.symm er.symm (hn.trans rhsSimple.symm)

lemma external_mirror_principal_frame (T : MatrixIso K (Fin r) (Fin r))
    (v : Fin (w.shape.atomicBand.length+1))
    (p : (w.shape.atomicBand.kind v).table.Port)
    (hp : p=(w.shape.atomicBand.kind v).input ∨ p=(w.shape.atomicBand.kind v).output) :
    (w.mirrorVertexFrames T v ((w.shape.atomicBand.kind v).mirrorPort p)).reindex
      ((w.shape.vertexAtoms v).seamColumns (w.shape.vertexAtoms v).mirror
        p ((w.shape.atomicBand.kind v).mirrorPort p) ((w.shape.atomicBand.kind v).mirrorChild p)
        (fun a => ((w.shape.vertexAtoms v).mirror_atoms ⟨p,some a⟩).symm))
      (finCongr ((w.shape.vertexAtoms v).rank_of_atoms (w.shape.vertexAtoms v).mirror
        ((w.shape.vertexAtoms v).mirror_atoms ⟨p,none⟩).symm))=
      (w.vertexFrames v p).trans
        (T.symm.reindex (finCongr (w.external_principal_rank v p hp))
          (finCongr (w.external_principal_rank v p hp))) := by
  let D := w.shape.vertexAtoms v
  let E := D.mirror
  let G := w.vertexBases v
  let H := w.mirrorVertexBases T v
  let q := (w.shape.atomicBand.kind v).mirrorPort p
  let c := (w.shape.atomicBand.kind v).mirrorChild p
  let hc := fun a => (D.mirror_atoms ⟨p,some a⟩).symm
  let ec := D.seamColumns E p q c hc
  have hb : (H.columns q).reindex ec ec=G.columns p := by
    change (MatrixIso.block _).reindex (Equiv.sigmaCongr _ _) (Equiv.sigmaCongr _ _)=_
    rw [MatrixIso.block_reindex_sigma]
    apply congrArg MatrixIso.block
    funext a
    exact w.mirror_basis T v ⟨p,some a⟩ (w.child_color_ne v p a)
  change ((H.columns q).symm.trans (E.frame q) |>.trans (H.basis q none)).reindex _ _=_
  rw [MatrixIso.bases_reindex, hb,
    D.frame_reindex E p q c (D.mirror_atoms ⟨p,none⟩).symm hc]
  have hpB := w.external_mirror_principal_basis T v p hp
  dsimp only at hpB
  exact (congrArg (fun b => ((G.columns p).symm.trans (D.frame p)).trans b) hpB).trans
    (MatrixIso.trans_assoc _ _ _).symm

end
end OAI.IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
#print axioms OAI.IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand.external_mirror_basis_normalized

#print axioms OAI.IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand.external_mirror_principal_frame
