import OAI.AlgebraicGeometry.CharacterVarieties.Cutting.GraftValues
set_option maxHeartbeats 0
namespace OAI.IntegralCharacterVarieties.OccurrenceIncidence
noncomputable section
open scoped Classical Matrix
open VertexTable SurfacePresentation.Diagram
variable {F S V W I R : Type} {arity : S → ℕ} [CommRing R]
    (A : PortAssembly F S V arity) {kind : W → Kind}
    (P : PortPatch kind I Bool Bool) (d : (w : W) → Decoration (kind w) F)
    (q : S) (hi : P.SignatureMatch d)
    (hp : ∀ b,portSignature d (P.plus (.inr b)).val=A.seamSignature q)
    (hm : ∀ b,portSignature d (P.minus (.inr b)).val=A.seamSignature q)
local notation "E" => graftSideEquiv A P d q hi hp hm
local notation "a" => graftLabelArity A P d q hi hp hm
variable (rank : F → ℕ)
    (old : (s : Side S arity) → FacetUnit (R:=R) rank (A.facet s))
    (short : Bool → (i : Option (Fin (arity q))) → FacetUnit (R:=R) rank (A.facet ⟨q,i⟩))

lemma external_graftSideValues_short_one (b : Bool)
    (hone : ∀ i,short b i=1) (i : Option (Fin (a (.inr (.inr b))))) :
    graftSideValues A P d q hi hp hm rank old short (E ⟨.inr (.inr b),i⟩)=1 := by
  rw [graftSideValues_coord]
  unfold graftLabelValues
  simp only [hone]
  generalize_proofs ht
  have castOne {nn mm : ℕ} (hn : nn=mm)
      (ht : (Matrix (Fin nn) (Fin nn) R)ˣ=(Matrix (Fin mm) (Fin mm) R)ˣ) :
      cast ht (1 : (Matrix (Fin nn) (Fin nn) R)ˣ)=1 := by
    subst mm
    rfl
  apply castOne
  have hc := graft_short_color A P d q hi hp hm b (i.map (finCongr ht))
  have hi' : (i.map (finCongr ht)).map
      (finCongr (graftLabelArity_short A P d q hi hp hm b).symm)=i := by
    cases i with
    | none => rfl
    | some i => rfl
  have hc' : (graftAssembly A P d q hi hp hm).facet
      (E ⟨.inr (.inr b),i⟩)=A.facet ⟨q,i.map (finCongr ht)⟩ := by
    change (graftAssembly A P d q hi hp hm).facet ⟨graftPlus A P (.inr (.inr b)),i⟩=_
    erw [hi'] at hc
    exact hc
  exact congrArg rank hc'.symm

end
end OAI.IntegralCharacterVarieties.OccurrenceIncidence
#print axioms OAI.IntegralCharacterVarieties.OccurrenceIncidence.external_graftSideValues_short_one
