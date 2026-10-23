import OAI.AlgebraicGeometry.CharacterVarieties.Frames.Mirror
set_option maxHeartbeats 0
namespace OAI.IntegralCharacterVarieties.OccurrenceIncidence.VariableGallery
noncomputable section
open scoped Classical
open VertexTable
variable {l : ℕ} (kind : Fin (l+1) → Kind)

def ExternalPositive := {p : PortAt kind true // p∉Set.range (internalPlus kind)}
def ExternalNegative := {p : PortAt kind false // p∉Set.range (internalMinus kind)}
lemma external_positive_ne_input (a : ExternalPositive kind)
    (ha : a ≠ ⟨input kind 0,first_exposed kind⟩) : a.val.val.2≠(kind a.val.val.1).input := by
  intro he
  let v := a.val.val.1
  have hp : a.val=input kind v := by
    apply Subtype.ext
    exact Sigma.ext rfl (heq_of_eq he)
  have hv : v=0 := by
    by_contra hn
    let j : Fin l := ⟨v.val-1,by have := v.isLt;have hv0 : v.val≠0 := fun h => hn (Fin.ext h);have : 0<v.val := Nat.pos_of_ne_zero hv0;omega⟩
    have hj : j.succ=v := by apply Fin.ext;have hv0 : v.val≠0 := fun h => hn (Fin.ext h);have : 0<v.val := Nat.pos_of_ne_zero hv0;dsimp [j];omega
    apply a.property
    exact ⟨j,by change input kind j.succ=a.val;rw [hj,hp]⟩
  apply ha
  apply Subtype.ext
  exact hp.trans (congrArg (input kind) hv)

lemma external_positive_ne_output (a : ExternalPositive kind) : a.val.val.2≠(kind a.val.val.1).output := by
  intro he
  have hh := a.val.property
  rw [he,Kind.output_endpoint] at hh
  cases hh

lemma external_negative_ne_output (a : ExternalNegative kind)
    (ha : a ≠ ⟨output kind (Fin.last l),last_exposed kind⟩) : a.val.val.2≠(kind a.val.val.1).output := by
  intro he
  let v := a.val.val.1
  have hp : a.val=output kind v := by
    apply Subtype.ext
    exact Sigma.ext rfl (heq_of_eq he)
  have hv : v=Fin.last l := by
    by_contra hn
    let j : Fin l := ⟨v.val,by have := v.isLt;have : v.val≠l := fun h => hn (Fin.ext h);omega⟩
    have hj : j.castSucc=v := Fin.ext rfl
    apply a.property
    exact ⟨j,by change output kind j.castSucc=a.val;rw [hj,hp]⟩
  apply ha
  apply Subtype.ext
  exact hp.trans (congrArg (output kind) hv)

lemma external_negative_ne_input (a : ExternalNegative kind) : a.val.val.2≠(kind a.val.val.1).input := by
  intro he
  have hh := a.val.property
  rw [he,Kind.input_endpoint] at hh
  cases hh
end
end OAI.IntegralCharacterVarieties.OccurrenceIncidence.VariableGallery
