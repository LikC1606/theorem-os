import MirrorPrincipalBridge
import TransportedFrameNamed
set_option maxHeartbeats 0
namespace OAI.IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
noncomputable section
open scoped Classical Matrix
open TwoFlagBand OccurrenceIncidence VertexTable
variable {K : Type} [Field K] {n r : ℕ} {s : Fin n → ℕ}
    {f h : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K)}
    (w : IdentifiedBand s f h)

lemma parent_mirrorPrincipalNormalized
    (T : MatrixIso K (Fin r) (Fin r))
    (v : Fin (w.shape.atomicBand.length+1))
    (p : (w.shape.atomicBand.kind v).table.Port)
    (hp : p=(w.shape.atomicBand.kind v).input ∨ p=(w.shape.atomicBand.kind v).output)
    (e : (w.shape.vertexAtoms v).localRanks.Columns p ≃ ((i : Fin n) × Fin (s i))) :
    (((w.mirrorVertexFrames T v ((w.shape.atomicBand.kind v).mirrorPort p)).reindex
      (e.symm.trans ((w.shape.vertexAtoms v).seamColumns (w.shape.vertexAtoms v).mirror
        p ((w.shape.atomicBand.kind v).mirrorPort p) ((w.shape.atomicBand.kind v).mirrorChild p)
        (fun a => ((w.shape.vertexAtoms v).mirror_atoms ⟨p,some a⟩).symm)))
      ((finCongr (w.external_principal_rank v p hp)).symm.trans
        (finCongr ((w.shape.vertexAtoms v).rank_of_atoms (w.shape.vertexAtoms v).mirror
          ((w.shape.vertexAtoms v).mirror_atoms ⟨p,none⟩).symm)))).linearEquiv) =
    (((w.vertexFrames v p).reindex e.symm
      (finCongr (w.external_principal_rank v p hp)).symm).linearEquiv).trans
      T.linearEquiv.symm := by
  letI : Fintype ((w.shape.vertexAtoms v).localRanks.Columns p) :=
    (w.shape.vertexAtoms v).localRanks.fintypeColumns p
  have hh := w.external_mirror_principal_frame T v p hp
  have hz := congrArg (fun M => (M.reindex e.symm
    (finCongr (w.external_principal_rank v p hp)).symm).linearEquiv) hh
  rw [MatrixIso.reindex_reindex_eq] at hz
  have hr := MatrixIso.reindex_trans (w.vertexFrames v p)
    (T.symm.reindex (finCongr (w.external_principal_rank v p hp))
      (finCongr (w.external_principal_rank v p hp))) e.symm
    (finCongr (w.external_principal_rank v p hp)).symm
    (finCongr (w.external_principal_rank v p hp)).symm
  have ht : (T.symm.reindex (finCongr (w.external_principal_rank v p hp))
      (finCongr (w.external_principal_rank v p hp))).reindex
        (finCongr (w.external_principal_rank v p hp)).symm
        (finCongr (w.external_principal_rank v p hp)).symm = T.symm := by
    rw [MatrixIso.reindex_reindex_eq, Equiv.symm_trans_self, MatrixIso.reindex_refl_eq]
  have hlin : T.symm.linearEquiv=T.linearEquiv.symm := by rfl
  erw [hr,ht] at hz
  have hcomp : ((w.vertexFrames v p).reindex e.symm
      (finCongr (w.external_principal_rank v p hp)).symm |>.trans T.symm).linearEquiv =
      (((w.vertexFrames v p).reindex e.symm
        (finCongr (w.external_principal_rank v p hp)).symm).linearEquiv).trans T.linearEquiv.symm := by
    apply LinearEquiv.ext
    intro x
    exact MatrixIso.linearEquiv_trans_apply _ _ x
  exact hz.trans hcomp
end
end OAI.IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
#print axioms OAI.IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand.parent_mirrorPrincipalNormalized
