import ParentWrapEndpoints
import ParentWrapSideTransport
import ParentBlockIdentity
set_option maxHeartbeats 0
set_option quotPrecheck false
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "ss" => BandGraft.mirrorOutput A q B (Fin.last (B).length)
lemma parent_wrapSideColumns_eq :
    D.parent_wrapSideColumns q w.shape rfl w.rowRanks w.colRanks =
      D.parent_wrapFirstNamedColumns q w := by
  apply Equiv.ext
  intro i
  have he : (D.parent_wrapSideColumns q w.shape rfl w.rowRanks w.colRanks i).1 =
      (D.parent_wrapFirstNamedColumns q w i).1 := by
    apply Fin.ext
    exact (D.parent_wrapFirstNamedColumns_grade q w i).symm
  apply Sigma.ext he
  apply (Fin.heq_ext_iff (congrArg ((C).childDim ss) he)).2
  exact (D.parent_wrapFirstNamedColumns_snd q w i).symm
lemma parent_wrapSideParent_eq :
    D.parent_wrapSideParent q w.shape rfl w.rowRanks w.colRanks =
      D.parent_wrapCommonParent q w := by
  apply Equiv.ext
  intro i
  rfl
lemma parent_wrapChildIdentity
    (old : D.SideValues (R:=K))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ) :
    ((MatrixIso.block (fun j : Fin ((BandGraft.wiring A q B).seamArity ss) =>
      MatrixIso.unit (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks old J Y
        ⟨ss,some j⟩)⁻¹)).reindex
      (D.parent_wrapFirstNamedColumns q w) (D.parent_wrapFirstNamedColumns q w)).linearEquiv=
      LinearEquiv.refl K _ := by
  rw [← D.parent_wrapSideColumns_eq q w]
  rw [D.parent_wrapChildInverseTransport q w.shape rfl w.rowRanks w.colRanks old J Y]
  exact MatrixIso.parent_blockUnitOne_linear (K:=K) (ι:=Fin (arity q))
    (d:=fun i => Fin (D.childDim q i))

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_wrapChildIdentity
