import OAI.AlgebraicGeometry.CharacterVarieties.Seams.ProducedEquations
set_option maxHeartbeats 0
namespace OAI.IntegralCharacterVarieties.MatrixIso
noncomputable section
open scoped Classical Matrix
variable {K α β γ : Type*} [Field K] [Fintype α] [Fintype β] [Fintype γ]
lemma external_linearEquiv_trans (x : MatrixIso K α β) (y : MatrixIso K β γ) :
    (x.trans y).linearEquiv=x.linearEquiv.trans y.linearEquiv := by
  apply LinearEquiv.ext
  intro v
  exact linearEquiv_trans_apply x y v
end
end OAI.IntegralCharacterVarieties.MatrixIso
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K]
    (D : Diagram F S V arity) (s : S)
    (φ : R →+* K)
    (v : (g : D.Generator) → (Matrix (Fin (D.generatorRank g)) (Fin (D.generatorRank g)) K)ˣ)
lemma external_seam_of_commonCoordinates
    {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ ((i : Fin (arity s)) × Fin (D.childDim s i)))
    (f : β ≃ Fin (D.rank (D.ports.facet ⟨s,none⟩)))
    (h : SameFramedFlag (fun i => (e i).1.val)
      ((((MatrixIso.unit (v (.frame s false))).reindex
        (blockIndex (D.childDim s)).symm (finCongr (D.seamRank s))).reindex e f).linearEquiv.trans
        (((MatrixIso.unit (v (.side ⟨s,none⟩))).reindex f f).linearEquiv))
      ((((MatrixIso.block (fun i : Fin (arity s) =>
        MatrixIso.unit (v (.side ⟨s,some i⟩))⁻¹)).reindex e e).linearEquiv).trans
        ((((MatrixIso.unit (v (.frame s true))).reindex
          (blockIndex (D.childDim s)).symm (finCongr (D.seamRank s))).reindex e f).linearEquiv))) :
    SameFramedFlag (D.seamGrade s)
      (matrixUnitEquiv ((D.seamLeft s).eval φ v))
      (matrixUnitEquiv ((D.seamRight s).eval φ v)) := by
  apply (D.named_seam_iff s φ v).mpr
  have hh := (MatrixIso.sameFramedFlag_reindex_iff (fun i => i.1.val)
    (((MatrixIso.unit (v (.frame s false))).reindex
      (blockIndex (D.childDim s)).symm (finCongr (D.seamRank s))).trans
      (MatrixIso.unit (v (.side ⟨s,none⟩))))
    ((MatrixIso.block (fun i : Fin (arity s) =>
      MatrixIso.unit (v (.side ⟨s,some i⟩))⁻¹)).trans
      ((MatrixIso.unit (v (.frame s true))).reindex
        (blockIndex (D.childDim s)).symm (finCongr (D.seamRank s)))) e f).mp
  have hz := hh (by
    erw [MatrixIso.reindex_trans _ _ e f f, MatrixIso.reindex_trans _ _ e e f,
      MatrixIso.external_linearEquiv_trans, MatrixIso.external_linearEquiv_trans]
    exact h)
  erw [MatrixIso.external_linearEquiv_trans, MatrixIso.external_linearEquiv_trans] at hz
  exact hz
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
