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
variable (s : S)
local notation "ss" => BandGraft.oldPort A q B s true

lemma external_oldSideArity : (BandGraft.wiring A q B).seamArity ss = arity s :=
  (A).portAt_arity s true

lemma external_oldSideRank (i : Option (Fin (arity s))) :
    (C).rank ((C).ports.facet ⟨ss,i.map (finCongr (D.external_oldSideArity q d s).symm)⟩) =
      D.rank (D.ports.facet ⟨s,i⟩) := by
  exact congrArg (D.ports.refinedRank q d D.rank)
    (graft_old_color A (B).doublePatch (doubleDecoration (B).decoration) q
      ((B).patch.double_signatureMatch (B).decoration (B).patch_signatureMatch (B).shortFirst (B).shortLast)
      (fun i => by rw [(B).double_signature_plus]; cases i <;> rfl)
      (fun i => by rw [(B).double_signature_minus]; cases i <;> rfl) s i)

lemma external_oldSideValue
    (old : D.SideValues (R:=K))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
    (i : Option (Fin (arity s))) :
    rebaseUnit (D.external_oldSideRank q d hp hc hc' s i)
      (D.refinedCutSideValues q d hp hc hc' old J Y
        ⟨ss,i.map (finCongr (D.external_oldSideArity q d s).symm)⟩) =
      D.cutOldSideValues q old J ⟨s,i⟩ := by
  exact graftSideValues_old A (B).doublePatch (doubleDecoration (B).decoration) q
    ((B).patch.double_signatureMatch (B).decoration (B).patch_signatureMatch (B).shortFirst (B).shortLast)
    (fun i => by rw [(B).double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [(B).double_signature_minus]; cases i <;> rfl)
    (D.ports.refinedRank q d D.rank) (D.cutOldSideValues q old J)
    (D.cutShortSideValues q Y) s i

lemma external_oldSideValue_unselected
    (old : D.SideValues (R:=K))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
    (hs : s≠q) (i : Option (Fin (arity s))) :
    rebaseUnit (D.external_oldSideRank q d hp hc hc' s i)
      (D.refinedCutSideValues q d hp hc hc' old J Y
        ⟨ss,i.map (finCongr (D.external_oldSideArity q d s).symm)⟩) = old ⟨s,i⟩ := by
  rw [D.external_oldSideValue q d hp hc hc' s old J Y i]
  cases i with
  | none => simp only [cutOldSideValues, dif_neg hs]
  | some i => rfl

def external_oldSideColumns : ((i : Fin (arity s)) × Fin (D.childDim s i)) ≃
    ((j : Fin ((BandGraft.wiring A q B).seamArity ss)) × Fin ((C).childDim ss j)) :=
  Equiv.sigmaCongr (finCongr (D.external_oldSideArity q d s).symm)
    (fun i => finCongr (D.external_oldSideRank q d hp hc hc' s (some i)).symm)

def external_oldSideParent := (finCongr (D.external_oldSideRank q d hp hc hc' s none)).symm

lemma external_oldParentTransport
    (old : D.SideValues (R:=K))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
    (hs : s≠q) :
    (MatrixIso.unit (D.refinedCutSideValues q d hp hc hc' old J Y ⟨ss,none⟩)).reindex
      (D.external_oldSideParent q d hp hc hc' s)
      (D.external_oldSideParent q d hp hc hc' s) = MatrixIso.unit (old ⟨s,none⟩) := by
  have h := D.external_oldSideValue_unselected q d hp hc hc' s old J Y hs none
  have hi := rebaseUnit_iso (D.external_oldSideRank q d hp hc hc' s none)
    (D.refinedCutSideValues q d hp hc hc' old J Y ⟨ss,none⟩)
  erw [h] at hi
  exact hi.symm

lemma external_oldChildInverseTransport
    (old : D.SideValues (R:=K))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ) :
    (MatrixIso.block (fun j : Fin ((BandGraft.wiring A q B).seamArity ss) =>
      MatrixIso.unit (D.refinedCutSideValues q d hp hc hc' old J Y ⟨ss,some j⟩)⁻¹)).reindex
      (D.external_oldSideColumns q d hp hc hc' s)
      (D.external_oldSideColumns q d hp hc hc' s) =
      MatrixIso.block (fun i : Fin (arity s) => MatrixIso.unit (old ⟨s,some i⟩)⁻¹) := by
  erw [MatrixIso.block_reindex_sigma]
  congr 1
  funext i
  have h := D.external_oldSideValue q d hp hc hc' s old J Y (some i)
  have hi := rebaseUnit_iso (D.external_oldSideRank q d hp hc hc' s (some i))
    ((D.refinedCutSideValues q d hp hc hc' old J Y
      ⟨ss,some ((finCongr (D.external_oldSideArity q d s).symm) i)⟩)⁻¹)
  erw [map_inv, h] at hi
  exact hi.symm

lemma parent_selectedSideTransport
    (old : D.SideValues (R:=K))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ) :
    (MatrixIso.unit (D.refinedCutSideValues q d hp hc hc' old J Y
      ⟨BandGraft.oldPort A q B q true,none⟩)).reindex
      (D.external_oldSideParent q d hp hc hc' q)
      (D.external_oldSideParent q d hp hc hc' q) = MatrixIso.unit J := by
  have h := D.external_oldSideValue q d hp hc hc' q old J Y none
  rw [D.cutOldSideValues_selected q old J] at h
  have hi := rebaseUnit_iso (D.external_oldSideRank q d hp hc hc' q none)
    (D.refinedCutSideValues q d hp hc hc' old J Y
      ⟨BandGraft.oldPort A q B q true,none⟩)
  erw [h] at hi
  exact hi.symm

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
