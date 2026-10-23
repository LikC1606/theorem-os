import NamedTransportOne
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression HomTransport
variable {F S V K R : Type} {arity : S → ℕ} [Field K] [CommRing R]
    (D : Diagram F S V arity) (q : S) (φ : R →+* K)
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)

lemma external_unitSideSeam
    (hone : ∀ i : Option (Fin (arity q)), g (.side ⟨q,i⟩)=1)
    (hflag : SameFramedFlag (fun i : (j : Fin (arity q)) × Fin (D.childDim q j) => i.1.val)
      (D.namedSeamFrame q (g (.frame q false)))
      (D.namedSeamFrame q (g (.frame q true)))) :
    SameFramedFlag (D.seamGrade q)
      (matrixUnitEquiv ((D.seamLeft q).eval φ g))
      (matrixUnitEquiv ((D.seamRight q).eval φ g)) := by
  apply (D.named_seam_iff q φ g).mpr
  rw [D.external_namedParentLinear_one q g (hone none),
    D.external_namedChildInverse_one q g (fun i => hone (some i))]
  exact hflag

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
