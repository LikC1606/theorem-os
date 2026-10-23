import OAI.AlgebraicGeometry.CharacterVarieties.Seams.ProducedEquations

set_option maxHeartbeats 0

namespace OAI

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K] [Algebra R K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (hproper : D.Proper) (hmax : ∀ f, D.rank f ≤ D.rank (D.ports.facet ⟨q,none⟩))
    (hg : 0 < D.genus (D.bandCutParent q))
    (P : D.Punctures R) (x : D.Solution P K)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))

theorem external_graftPlus_cases
    {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
    (Q : (BandGraft.wiring A q B).Seam → Prop)
    (old : ∀ s, s ≠ q → Q (graftPlus A B.doublePatch (.inl s)))
    (selected : Q (graftPlus A B.doublePatch (.inl q)))
    (original : ∀ j, Q (graftPlus A B.doublePatch (.inr (.inl (.inl (.inl j))))))
    (mirror : ∀ j, Q (graftPlus A B.doublePatch (.inr (.inl (.inl (.inr j))))))
    (transversePlus : ∀ a, Q (graftPlus A B.doublePatch (.inr (.inl (.inr (.inl a))))))
    (transverseMinus : ∀ b, Q (graftPlus A B.doublePatch (.inr (.inl (.inr (.inr b))))))
    (first : Q (graftPlus A B.doublePatch (.inr (.inr false))))
    (wrap : Q (graftPlus A B.doublePatch (.inr (.inr true)))) : ∀ s, Q s := by
  intro s
  obtain ⟨z,rfl⟩ := (graftPlus A B.doublePatch).surjective s
  rcases z with s|((j|j)|(a|b))|b
  · by_cases hs : s=q
    · subst s
      exact selected
    · exact old s hs
  · exact original j
  · exact mirror j
  · exact transversePlus a
  · exact transverseMinus b
  · cases b
    · exact first
    · exact wrap

end IntegralCharacterVarieties.SurfacePresentation.Diagram
end
end OAI
