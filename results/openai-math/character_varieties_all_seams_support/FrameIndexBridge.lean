import OAI.AlgebraicGeometry.CharacterVarieties.Frames.NamedSeams
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.CutFrames

namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity)

def external_portColumns (p : LocalPort V D.ports.kind) :
    (D.vertexRanks p.1).Columns p.2 ≃
      ((i : Fin (arity (D.ports.attach p).1)) × Fin (D.childDim (D.ports.attach p).1 i)) :=
  Equiv.sigmaCongr (D.ports.childEquiv p) (fun _ => Equiv.refl _)

lemma external_namedFrame_port
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (p : LocalPort V D.ports.kind) :
    D.namedSeamFrame (D.ports.attach p).1
        (g (.frame (D.ports.attach p).1 (D.ports.attach p).2)) =
      ((D.portFrame g p).reindex (D.external_portColumns p).symm (Equiv.refl _)).linearEquiv := by
  unfold namedSeamFrame portFrame
  erw [MatrixIso.reindex_reindex_eq]
  have he : (D.external_portColumns p).symm.trans (D.portColumnIndex p) =
      (blockIndex (D.childDim (D.ports.attach p).1)).symm := by
    change (D.external_portColumns p).symm.trans
      ((D.external_portColumns p).trans (blockIndex (D.childDim (D.ports.attach p).1)).symm) = _
    ext i
    exact congrArg (fun z => ((blockIndex (D.childDim (D.ports.attach p).1)).symm z).val)
      ((D.external_portColumns p).apply_symm_apply i)
  erw [he]
  rfl

lemma external_namedFrame_valuesFromPorts
    (frames : D.PortFrames (R:=K)) (side : D.SideValues (R:=K))
    (handle : D.HandleValues (R:=K)) (p : LocalPort V D.ports.kind) :
    D.namedSeamFrame (D.ports.attach p).1
      ((D.valuesFromPorts frames side handle)
        (.frame (D.ports.attach p).1 (D.ports.attach p).2)) =
      ((frames p).reindex (D.external_portColumns p).symm (Equiv.refl _)).linearEquiv := by
  rw [external_namedFrame_port, portFrame_valuesFromPorts]

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace OAI.IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
noncomputable section
open scoped Classical
variable {R : Type} [CommRing R] {k : Kind} {d e : LocalRanks k}

lemma external_transportFrames_eq_reindex (h : d=e)
    (f : (p : k.table.Port) → MatrixIso R (d.Columns p) (d.Parent p))
    (p : k.table.Port) :
    transportFrames h f p = (f p).reindex
      (Equiv.sigmaCongr (Equiv.refl _) (fun c =>
        finCongr (congrArg (fun z : LocalRanks k => z.rank p (some c)) h.symm)))
      (finCongr (congrArg (fun z : LocalRanks k => z.rank p none) h.symm)) := by
  subst e
  have ec : (Equiv.sigmaCongr (Equiv.refl (k.table.Child p)) (fun c =>
      finCongr (congrArg (fun z : LocalRanks k => z.rank p (some c)) (rfl : d=d)))) =
      Equiv.refl (d.Columns p) := by
    apply Equiv.ext
    rintro ⟨c,i⟩
    rfl
  change f p = (f p).reindex _ (Equiv.refl _)
  erw [ec]
  exact (MatrixIso.reindex_refl_eq _).symm

lemma external_transportFrames_reindex (h : d=e)
    (f : (p : k.table.Port) → MatrixIso R (d.Columns p) (d.Parent p))
    (p : k.table.Port) :
    ((transportFrames h f p).reindex
      (Equiv.sigmaCongr (Equiv.refl _) (fun c =>
        finCongr (congrArg (fun z : LocalRanks k => z.rank p (some c)) h)))
      (finCongr (congrArg (fun z : LocalRanks k => z.rank p none) h))) = f p := by
  subst e
  have ec : (Equiv.sigmaCongr (Equiv.refl (k.table.Child p)) (fun c =>
      finCongr (congrArg (fun z : LocalRanks k => z.rank p (some c)) (rfl : d=d)))) =
      Equiv.refl (d.Columns p) := by
    apply Equiv.ext
    rintro ⟨c,i⟩
    rfl
  change (f p).reindex _ (Equiv.refl _) = f p
  erw [ec]
  exact MatrixIso.reindex_refl_eq _

end
end OAI.IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
