import OAI.AlgebraicGeometry.CharacterVarieties.Frames.NamedSeams
set_option maxHeartbeats 0
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S)
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)

lemma external_namedParentLinear_one (hone : g (.side ⟨q,none⟩)=1) :
    D.namedParentLinear q g=LinearEquiv.refl K _ := by
  unfold namedParentLinear
  rw [hone]
  apply LinearEquiv.ext
  intro v
  exact Matrix.one_mulVec v

lemma external_namedChildInverse_one (hone : ∀ i,g (.side ⟨q,some i⟩)=1) :
    D.namedChildInverse q g=LinearEquiv.refl K _ := by
  have hv : (MatrixIso.block (fun i : Fin (arity q) =>
      MatrixIso.unit (g (.side ⟨q,some i⟩))⁻¹)).val=1 := by
    simp only [MatrixIso.block, MatrixIso.unit, hone, inv_one, Units.val_one]
    ext ⟨i,j⟩ ⟨k,l⟩
    by_cases h : i=k
    · subst k; simp [Matrix.blockDiagonal', Matrix.one_apply]
    · simp [Matrix.blockDiagonal', Matrix.one_apply, h]
  apply LinearEquiv.ext
  intro v
  exact (congrArg (fun M : Matrix _ _ K => M *ᵥ v) hv).trans (Matrix.one_mulVec v)

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_namedParentLinear_one
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_namedChildInverse_one
