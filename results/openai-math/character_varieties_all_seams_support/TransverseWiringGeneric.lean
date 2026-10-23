import OAI.AlgebraicGeometry.CharacterVarieties.Cutting.GraftValues
set_option maxHeartbeats 0
set_option quotPrecheck false
set_option autoImplicit false
namespace OAI.IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
noncomputable section
open scoped Classical
open VertexTable
variable {F S V : Type} {arity : S → ℕ}
    (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
variable (a : {a : {p : PortAt B.kind true // p∉Set.range (VariableGallery.internalPlus B.kind)} // a≠B.shortFirst})
local notation "ps" => graftPlus A B.doublePatch (.inr (.inl (.inr (.inl a))))
lemma external_transversePlusPort :
    (ps).val=(⟨.inr (.inl a.val.val.val.1),a.val.val.val.2⟩ : LocalPort _ (kind A q B)) := rfl
lemma external_transversePlusWire :
    (wiring A q B).wire ps=
      graftMinus A B.doublePatch (.inr (.inl (.inr (.inl a)))) := by
  have hh := graft_wire_plus A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus];cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus];cases i <;> rfl)
    (.inr (.inl (.inr (.inl a))))
  rw [graftCycle_internal] at hh
  exact hh
lemma external_transversePlusNegativePort :
    (graftMinus A B.doublePatch (.inr (.inl (.inr (.inl a))))).val=
      (⟨.inr (.inr a.val.val.val.1),(B.kind a.val.val.val.1).mirrorPort a.val.val.val.2⟩ :
        LocalPort _ (kind A q B)) := rfl
variable (b : {b : {p : PortAt B.kind false // p∉Set.range (VariableGallery.internalMinus B.kind)} // b≠B.shortLast})
local notation "ms" => graftPlus A B.doublePatch (.inr (.inl (.inr (.inr b))))
lemma external_transverseMinusPort :
    (ms).val=(⟨.inr (.inr b.val.val.val.1),(B.kind b.val.val.val.1).mirrorPort b.val.val.val.2⟩ :
      LocalPort _ (kind A q B)) := rfl
lemma external_transverseMinusWire :
    (wiring A q B).wire ms=
      graftMinus A B.doublePatch (.inr (.inl (.inr (.inr b)))) := by
  have hh := graft_wire_plus A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus];cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus];cases i <;> rfl)
    (.inr (.inl (.inr (.inr b))))
  rw [graftCycle_internal] at hh
  exact hh
lemma external_transverseMinusNegativePort :
    (graftMinus A B.doublePatch (.inr (.inl (.inr (.inr b))))).val=
      (⟨.inr (.inl b.val.val.val.1),b.val.val.val.2⟩ : LocalPort _ (kind A q B)) := rfl
end
end OAI.IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
