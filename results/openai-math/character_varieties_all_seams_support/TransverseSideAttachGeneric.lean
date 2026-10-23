import TransverseWiringGeneric
set_option autoImplicit false
set_option maxHeartbeats 0
set_option quotPrecheck false
namespace OAI.IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
noncomputable section
open scoped Classical Matrix
open VertexTable
variable {F S V R : Type} [CommRing R] {arity : S → ℕ}
    (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
variable (a : {a : {p : PortAt B.kind true // p∉Set.range (VariableGallery.internalPlus B.kind)} // a≠B.shortFirst})
local notation "ps" => graftPlus A B.doublePatch (.inr (.inl (.inr (.inl a))))
variable (b : {b : {p : PortAt B.kind false // p∉Set.range (VariableGallery.internalMinus B.kind)} // b≠B.shortLast})
local notation "ms" => graftPlus A B.doublePatch (.inr (.inl (.inr (.inr b))))

lemma external_transversePlusOrigAttach_generic :
    (wiring A q B).endOf
      (⟨.inr (.inl a.val.val.val.1),a.val.val.val.2⟩ : LocalPort _ (kind A q B))=(ps,true) :=
  (wiring A q B).endOf_portAt (ps,true)
lemma external_transversePlusMirrorAttach_generic :
    (wiring A q B).endOf
      (⟨.inr (.inr a.val.val.val.1),(B.kind a.val.val.val.1).mirrorPort a.val.val.val.2⟩ :
        LocalPort _ (kind A q B))=(ps,false) := by
  have hh := (wiring A q B).endOf_portAt (ps,false)
  change (wiring A q B).endOf ((wiring A q B).wire ps).val=_ at hh
  rw [external_transversePlusWire] at hh
  exact hh
lemma external_transverseMinusMirrorAttach_generic :
    (wiring A q B).endOf
      (⟨.inr (.inr b.val.val.val.1),(B.kind b.val.val.val.1).mirrorPort b.val.val.val.2⟩ :
        LocalPort _ (kind A q B))=(ms,true) :=
  (wiring A q B).endOf_portAt (ms,true)
lemma external_transverseMinusOrigAttach_generic :
    (wiring A q B).endOf
      (⟨.inr (.inl b.val.val.val.1),b.val.val.val.2⟩ : LocalPort _ (kind A q B))=(ms,false) := by
  have hh := (wiring A q B).endOf_portAt (ms,false)
  change (wiring A q B).endOf ((wiring A q B).wire ms).val=_ at hh
  rw [external_transverseMinusWire] at hh
  exact hh
lemma external_transversePlusSide_generic
    (rank : F → ℕ)
    (old : (s : Side S arity) → (Matrix (Fin (rank (A.facet s))) (Fin (rank (A.facet s))) R)ˣ)
    (short : Bool → (i : Option (Fin (arity q))) →
      (Matrix (Fin (rank (A.facet ⟨q,i⟩))) (Fin (rank (A.facet ⟨q,i⟩))) R)ˣ)
    (i : Option (Fin ((wiring A q B).seamArity ps))) :
    graftSideValues A B.doublePatch (doubleDecoration B.decoration) q
      (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
      (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
      (fun i => by rw [B.double_signature_minus]; cases i <;> rfl)
      rank old short ⟨ps,i⟩=1 := by
  exact graftSideValues_internal A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl)
    rank old short (.inr (.inl a)) i

lemma external_transverseMinusSide_generic
    (rank : F → ℕ)
    (old : (s : Side S arity) → (Matrix (Fin (rank (A.facet s))) (Fin (rank (A.facet s))) R)ˣ)
    (short : Bool → (i : Option (Fin (arity q))) →
      (Matrix (Fin (rank (A.facet ⟨q,i⟩))) (Fin (rank (A.facet ⟨q,i⟩))) R)ˣ)
    (i : Option (Fin ((wiring A q B).seamArity ms))) :
    graftSideValues A B.doublePatch (doubleDecoration B.decoration) q
      (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
      (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
      (fun i => by rw [B.double_signature_minus]; cases i <;> rfl)
      rank old short ⟨ms,i⟩=1 := by
  exact graftSideValues_internal A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl)
    rank old short (.inr (.inr b)) i

end
end OAI.IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
