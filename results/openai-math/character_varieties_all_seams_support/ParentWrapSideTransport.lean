import OAI.AlgebraicGeometry.CharacterVarieties.Seams.ProducedEquations
set_option maxHeartbeats 0
set_option quotPrecheck false
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {r : ℕ} (d : TwoFlagBand.RankShape (arity q) (arity q) r)
    (hp : D.rank (D.ports.facet ⟨q,none⟩)=r)
    (hc : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.row i))
    (hc' : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.col i))
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q d)
local notation "B" => D.ports.refinedBandForSeam q d
local notation "C" => D.refinedCutDiagram q d hp hc hc'
local notation "ss" => BandGraft.mirrorOutput A q B (Fin.last (B).length)

lemma parent_wrapSideArity : (BandGraft.wiring A q B).seamArity ss = arity q :=
  graftLabelArity_short A (B).doublePatch (doubleDecoration (B).decoration) q
    ((B).patch.double_signatureMatch (B).decoration (B).patch_signatureMatch (B).shortFirst (B).shortLast)
    (fun i => by rw [(B).double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [(B).double_signature_minus]; cases i <;> rfl) true

lemma parent_wrapSideRank (i : Option (Fin (arity q))) :
    (C).rank ((C).ports.facet ⟨ss,i.map (finCongr (D.parent_wrapSideArity q d).symm)⟩) =
      D.rank (D.ports.facet ⟨q,i⟩) := by
  exact congrArg (D.ports.refinedRank q d D.rank)
    (graft_short_color A (B).doublePatch (doubleDecoration (B).decoration) q
      ((B).patch.double_signatureMatch (B).decoration (B).patch_signatureMatch (B).shortFirst (B).shortLast)
      (fun i => by rw [(B).double_signature_plus]; cases i <;> rfl)
      (fun i => by rw [(B).double_signature_minus]; cases i <;> rfl) true i)

lemma parent_wrapSideValue
    (old : D.SideValues (R:=K))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
    (i : Option (Fin (arity q))) :
    rebaseUnit (D.parent_wrapSideRank q d hp hc hc' i)
      (D.refinedCutSideValues q d hp hc hc' old J Y
        ⟨ss,i.map (finCongr (D.parent_wrapSideArity q d).symm)⟩) =
      D.cutShortSideValues q Y true i := by
  exact graftSideValues_short A (B).doublePatch (doubleDecoration (B).decoration) q
    ((B).patch.double_signatureMatch (B).decoration (B).patch_signatureMatch (B).shortFirst (B).shortLast)
    (fun i => by rw [(B).double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [(B).double_signature_minus]; cases i <;> rfl)
    (D.ports.refinedRank q d D.rank) (D.cutOldSideValues q old J)
    (D.cutShortSideValues q Y) true i

def parent_wrapSideColumns : ((i : Fin (arity q)) × Fin (D.childDim q i)) ≃
    ((j : Fin ((BandGraft.wiring A q B).seamArity ss)) × Fin ((C).childDim ss j)) :=
  Equiv.sigmaCongr (finCongr (D.parent_wrapSideArity q d).symm)
    (fun i => finCongr (D.parent_wrapSideRank q d hp hc hc' (some i)).symm)
def parent_wrapSideParent := (finCongr (D.parent_wrapSideRank q d hp hc hc' none)).symm

lemma parent_wrapParentTransport
    (old : D.SideValues (R:=K))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ) :
    (MatrixIso.unit (D.refinedCutSideValues q d hp hc hc' old J Y ⟨ss,none⟩)).reindex
      (D.parent_wrapSideParent q d hp hc hc')
      (D.parent_wrapSideParent q d hp hc hc') = MatrixIso.unit Y := by
  have h := D.parent_wrapSideValue q d hp hc hc' old J Y none
  change rebaseUnit _ _ = Y at h
  have hi := rebaseUnit_iso (D.parent_wrapSideRank q d hp hc hc' none)
    (D.refinedCutSideValues q d hp hc hc' old J Y ⟨ss,none⟩)
  erw [h] at hi
  exact hi.symm

lemma parent_wrapChildInverseTransport
    (old : D.SideValues (R:=K))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ) :
    (MatrixIso.block (fun j : Fin ((BandGraft.wiring A q B).seamArity ss) =>
      MatrixIso.unit (D.refinedCutSideValues q d hp hc hc' old J Y ⟨ss,some j⟩)⁻¹)).reindex
      (D.parent_wrapSideColumns q d hp hc hc')
      (D.parent_wrapSideColumns q d hp hc hc') =
      MatrixIso.block (fun i : Fin (arity q) =>
        MatrixIso.unit (1 : (Matrix (Fin (D.childDim q i)) (Fin (D.childDim q i)) K)ˣ)) := by
  erw [MatrixIso.block_reindex_sigma]
  congr 1
  funext i
  have h := D.parent_wrapSideValue q d hp hc hc' old J Y (some i)
  change rebaseUnit _ _ = 1 at h
  have hi := rebaseUnit_iso (D.parent_wrapSideRank q d hp hc hc' (some i))
    ((D.refinedCutSideValues q d hp hc hc' old J Y
      ⟨ss,some ((finCongr (D.parent_wrapSideArity q d).symm) i)⟩)⁻¹)
  erw [map_inv, h, inv_one] at hi
  exact hi.symm

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_wrapParentTransport
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_wrapChildInverseTransport
