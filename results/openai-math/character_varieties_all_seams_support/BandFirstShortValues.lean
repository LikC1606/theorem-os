import GraftShortUnit
set_option maxHeartbeats 0
namespace OAI.IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
noncomputable section
open scoped Classical Matrix
open VertexTable SurfacePresentation.Diagram
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
    (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
    (rank : F → ℕ)
    (old : (s : Side S arity) → FacetUnit (R:=R) rank (A.facet s))
    (short : Bool → (i : Option (Fin (arity q))) → FacetUnit (R:=R) rank (A.facet ⟨q,i⟩))
lemma external_bandValues_first_one (hone : ∀ i,short false i=1)
    (i : Option (Fin ((wiring A q B).seamArity (originalPort A q B 0 true)))) :
    bandValues A q B rank old short ⟨originalPort A q B 0 true,i⟩=1 := by
  exact external_graftSideValues_short_one A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun j => by rw [B.double_signature_plus]; cases j <;> rfl)
    (fun j => by rw [B.double_signature_minus]; cases j <;> rfl)
    rank old short false hone i
end
end OAI.IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
#print axioms OAI.IntegralCharacterVarieties.OccurrenceIncidence.BandGraft.external_bandValues_first_one
