import ParentMirrorPrincipalNormalizedV2
set_option maxHeartbeats 0
namespace OAI.IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
noncomputable section
open scoped Classical Matrix
open TwoFlagBand OccurrenceIncidence VertexTable
variable {K : Type} [Field K] {n r : ℕ} {s : Fin n → ℕ}
    {f h : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K)}
    (w : IdentifiedBand s f h)

def parent_mirrorFirstColumns : ((i : Fin n) × Fin (s i)) ≃
    (w.shape.vertexAtoms 0).mirror.localRanks.Columns
      ((w.shape.atomicBand.kind 0).mirrorPort (w.shape.atomicBand.kind 0).input) :=
  w.firstColumns.symm.trans ((w.shape.vertexAtoms 0).seamColumns (w.shape.vertexAtoms 0).mirror
    (w.shape.atomicBand.kind 0).input
    ((w.shape.atomicBand.kind 0).mirrorPort (w.shape.atomicBand.kind 0).input)
    ((w.shape.atomicBand.kind 0).mirrorChild _)
    (fun a => ((w.shape.vertexAtoms 0).mirror_atoms ⟨(w.shape.atomicBand.kind 0).input,some a⟩).symm))
def parent_mirrorFirstParent : Fin r ≃
    (w.shape.vertexAtoms 0).mirror.localRanks.Parent
      ((w.shape.atomicBand.kind 0).mirrorPort (w.shape.atomicBand.kind 0).input) :=
  (finCongr w.firstParent_rank).symm.trans
    (finCongr ((w.shape.vertexAtoms 0).rank_of_atoms (w.shape.vertexAtoms 0).mirror
      ((w.shape.vertexAtoms 0).mirror_atoms ⟨(w.shape.atomicBand.kind 0).input,none⟩).symm))
lemma parent_mirrorFirstFrame (T : MatrixIso K (Fin r) (Fin r)) :
    ((w.mirrorVertexFrames T 0
      ((w.shape.atomicBand.kind 0).mirrorPort (w.shape.atomicBand.kind 0).input)).reindex
      (w.parent_mirrorFirstColumns) (w.parent_mirrorFirstParent)).linearEquiv =
      w.firstFrame.trans T.linearEquiv.symm := by
  exact w.parent_mirrorPrincipalNormalized T 0 (w.shape.atomicBand.kind 0).input
    (Or.inl rfl) w.firstColumns

def parent_mirrorLastColumns : ((i : Fin n) × Fin (s i)) ≃
    (w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).mirror.localRanks.Columns
      ((w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).mirrorPort (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output) :=
  w.lastColumns.symm.trans ((w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).seamColumns (w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).mirror
    (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output
    ((w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).mirrorPort (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output)
    ((w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).mirrorChild _)
    (fun a => ((w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).mirror_atoms ⟨(w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output,some a⟩).symm))
def parent_mirrorLastParent : Fin r ≃
    (w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).mirror.localRanks.Parent
      ((w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).mirrorPort (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output) :=
  (finCongr w.lastParent_rank).symm.trans
    (finCongr ((w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).rank_of_atoms (w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).mirror
      ((w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).mirror_atoms ⟨(w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output,none⟩).symm))
lemma parent_mirrorLastFrame (T : MatrixIso K (Fin r) (Fin r)) :
    ((w.mirrorVertexFrames T (Fin.last w.shape.atomicBand.length)
      ((w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).mirrorPort (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output)).reindex
      (w.parent_mirrorLastColumns) (w.parent_mirrorLastParent)).linearEquiv =
      w.lastFrame.trans T.linearEquiv.symm := by
  exact w.parent_mirrorPrincipalNormalized T (Fin.last w.shape.atomicBand.length) (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output
    (Or.inr rfl) w.lastColumns

end
end OAI.IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
#print axioms OAI.IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand.parent_mirrorFirstFrame
#print axioms OAI.IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand.parent_mirrorLastFrame
