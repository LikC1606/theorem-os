import OAI.AlgebraicGeometry.CharacterVarieties.Seams.ProducedEquations
set_option maxHeartbeats 0
namespace OAI.IntegralCharacterVarieties.MatrixIso
noncomputable section
open scoped Classical Matrix
variable {K ι : Type*} [Field K] [Fintype ι] {d : ι → Type*} [∀ i,Fintype (d i)] [∀ i,DecidableEq (d i)]
lemma parent_blockUnitOne_linear :
    (MatrixIso.block (fun i : ι =>
      MatrixIso.unit (1 : (Matrix (d i) (d i) K)ˣ))).linearEquiv =
      LinearEquiv.refl K _ := by
  have hv : (MatrixIso.block (fun i : ι =>
      MatrixIso.unit (1 : (Matrix (d i) (d i) K)ˣ))).val=1 := by
    simp only [MatrixIso.block, MatrixIso.unit, Units.val_one]
    exact Matrix.blockDiagonal'_one
  apply LinearEquiv.ext
  intro v
  exact (congrArg (fun M : Matrix _ _ K => M *ᵥ v) hv).trans (Matrix.one_mulVec v)
end
end OAI.IntegralCharacterVarieties.MatrixIso
#print axioms OAI.IntegralCharacterVarieties.MatrixIso.parent_blockUnitOne_linear
