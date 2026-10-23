import OAI.AlgebraicGeometry.CharacterVarieties.Seams.ProducedEquations
set_option maxHeartbeats 0
set_option quotPrecheck false
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {r : ℕ} (d : TwoFlagBand.RankShape (arity q) (arity q) r)
    (hp : D.rank (D.ports.facet ⟨q,none⟩)=r)
    (hc : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.row i))
    (hc' : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.col i))
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q d)
local notation "B" => D.ports.refinedBandForSeam q d
local notation "C" => D.refinedCutDiagram q d hp hc hc'
variable (old : D.SideValues (R:=R))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) R)ˣ)

lemma external_originalInternalSide_one (j : Fin d.atomicBand.length)
    (i : Option (Fin ((BandGraft.wiring A q B).seamArity (BandGraft.originalPort A q B j.succ true)))) :
    D.refinedCutSideValues q d hp hc hc' old J Y ⟨BandGraft.originalPort A q B j.succ true,i⟩=1 := by
  exact graftSideValues_internal A (B).doublePatch (doubleDecoration (B).decoration) q
    ((B).patch.double_signatureMatch (B).decoration (B).patch_signatureMatch (B).shortFirst (B).shortLast)
    (fun i => by rw [(B).double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [(B).double_signature_minus]; cases i <;> rfl)
    (D.ports.refinedRank q d D.rank) (D.cutOldSideValues q old J) (D.cutShortSideValues q Y)
    (.inl (.inl j)) i

lemma external_mirrorInternalSide_one (j : Fin d.atomicBand.length)
    (i : Option (Fin ((BandGraft.wiring A q B).seamArity (BandGraft.mirrorOutput A q B j.castSucc)))) :
    D.refinedCutSideValues q d hp hc hc' old J Y ⟨BandGraft.mirrorOutput A q B j.castSucc,i⟩=1 := by
  exact graftSideValues_internal A (B).doublePatch (doubleDecoration (B).decoration) q
    ((B).patch.double_signatureMatch (B).decoration (B).patch_signatureMatch (B).shortFirst (B).shortLast)
    (fun i => by rw [(B).double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [(B).double_signature_minus]; cases i <;> rfl)
    (D.ports.refinedRank q d D.rank) (D.cutOldSideValues q old J) (D.cutShortSideValues q Y)
    (.inl (.inr j)) i
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
