import ParentMarkedValueDataV2
import MarkedCutNamedBridge
set_option autoImplicit false
set_option maxHeartbeats 0
set_option quotPrecheck false
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable TwoFlagBand MatrixExpression HomTransport
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {r : ℕ} (d : RankShape (arity q) (arity q) r)
    (hp : D.rank (D.ports.facet ⟨q,none⟩)=r)
    (hc : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.row i))
    (hc' : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.col i))
    (hpMark : D.Proper) (hmaxMark : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (φ : R →+* K)
    (seed : (z : D.Generator) → (Matrix (Fin (D.generatorRank z)) (Fin (D.generatorRank z)) K)ˣ)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
    (t a : (Matrix (Fin (D.rank (D.bandCutParent q)))
      (Fin (D.rank (D.bandCutParent q))) K)ˣ)
    (frames : (D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).PortFrames (R:=K))
local notation "lifted" => D.bandCutLiftGenerators q φ seed b0 t a
local notation "J" => D.bandCutChosenJ q φ lifted b0 i0 a
local notation "T" => D.bandCutChosenT q φ lifted b0 i0 t
local notation "RJ" => rebaseUnit (D.seamRank q).symm J
local notation "RT" => rebaseUnit (D.seamRank q).symm T
lemma parent_markedLiftSide_rebased
    (side : Side (BandGraft.wiring (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q d)) q
      (D.ports.refinedBandForSeam q d)).Seam
      (BandGraft.wiring (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q d)) q
      (D.ports.refinedBandForSeam q d)).seamArity) :
    D.refinedMarkedLiftValues q d hp hc hc' hpMark hmaxMark φ seed b0 i0 t a frames (.side side)=
      D.refinedCutSideValues q d hp hc hc' (fun z => lifted (.side z)) RJ
        (RT⁻¹*RJ⁻¹*(show (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
          (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ from lifted (.side ⟨q,none⟩))*RT) side := by
  have h := D.parent_markedLiftSideValue q d hp hc hc' hpMark hmaxMark φ seed b0 i0 t a frames side
  have hm := D.bandCutMirror_rebase q lifted J T
  exact h.trans (congrArg (fun Y => D.refinedCutSideValues q d hp hc hc'
    (fun z => lifted (.side z)) RJ Y side) hm)

lemma parent_markedLiftCutPortFrame
    (p : LocalPort _ (D.refinedCutDiagram q d hp hc hc').ports.kind) :
    (D.refinedCutDiagram q d hp hc hc').portFrame
      (D.external_markedAsCutValues q d hp hc hc' hpMark hmaxMark
        (D.refinedMarkedLiftValues q d hp hc hc' hpMark hmaxMark φ seed b0 i0 t a frames)) p =
      frames p := by
  calc
    _ = (D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).portFrame
      (D.refinedMarkedLiftValues q d hp hc hc' hpMark hmaxMark φ seed b0 i0 t a frames) p :=
        D.external_markedAsCutValues_portFrame q d hp hc hc' hpMark hmaxMark _ p
    _ = frames p :=
        D.parent_markedLiftPortFrame q d hp hc hc' hpMark hmaxMark φ seed b0 i0 t a frames p
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_markedLiftSide_rebased
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_markedLiftCutPortFrame
