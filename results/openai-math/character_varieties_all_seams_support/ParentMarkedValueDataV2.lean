import OAI.AlgebraicGeometry.CharacterVarieties.Seams.ProducedEquations
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

lemma parent_markedBandSideValue
    (hpMark : D.Proper) (hmaxMark : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (frames : (D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).PortFrames (R:=K))
    (seed : (z : D.Generator) → (Matrix (Fin (D.generatorRank z)) (Fin (D.generatorRank z)) K)ˣ)
    (J T : D.BandCutUnit (A:=K) q)
    (hh : (f : F) → Fin ((D.bandCutDiagram q).genus f) → Bool →
      (Matrix (Fin (D.rank f)) (Fin (D.rank f)) K)ˣ)
    (a : Side (BandGraft.wiring (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q d)) q (D.ports.refinedBandForSeam q d)).Seam
      (BandGraft.wiring (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q d)) q (D.ports.refinedBandForSeam q d)).seamArity) :
    D.refinedMarkedBandValues q d hp hc hc' hpMark hmaxMark frames seed J T hh (.side a)=
      D.refinedCutSideValues q d hp hc hc' (fun a => seed (.side a))
        (rebaseUnit (D.seamRank q).symm J)
        (rebaseUnit (D.seamRank q).symm (T⁻¹*J⁻¹*D.bandCutP q seed*T)) a := by
  rfl

lemma parent_markedBandPortFrame
    (hpMark : D.Proper) (hmaxMark : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (frames : (D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).PortFrames (R:=K))
    (seed : (z : D.Generator) → (Matrix (Fin (D.generatorRank z)) (Fin (D.generatorRank z)) K)ˣ)
    (J T : D.BandCutUnit (A:=K) q)
    (hh : (f : F) → Fin ((D.bandCutDiagram q).genus f) → Bool →
      (Matrix (Fin (D.rank f)) (Fin (D.rank f)) K)ˣ)
    (p : LocalPort _ (D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).ports.kind) :
    (D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).portFrame
      (D.refinedMarkedBandValues q d hp hc hc' hpMark hmaxMark frames seed J T hh) p=frames p := by
  exact (D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).portFrame_valuesFromPorts _ _ _ p

lemma parent_markedLiftSideValue
    (hpMark : D.Proper) (hmaxMark : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (φ : R →+* K)
    (seed : (z : D.Generator) → (Matrix (Fin (D.generatorRank z)) (Fin (D.generatorRank z)) K)ˣ)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
    (t a : (Matrix (Fin (D.rank (D.bandCutParent q))) (Fin (D.rank (D.bandCutParent q))) K)ˣ)
    (frames : (D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).PortFrames (R:=K))
    (side : Side (BandGraft.wiring (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q d)) q (D.ports.refinedBandForSeam q d)).Seam
      (BandGraft.wiring (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q d)) q (D.ports.refinedBandForSeam q d)).seamArity) :
    D.refinedMarkedLiftValues q d hp hc hc' hpMark hmaxMark φ seed b0 i0 t a frames (.side side)=
      let seed' := D.bandCutLiftGenerators q φ seed b0 t a
      D.refinedCutSideValues q d hp hc hc' (fun z => seed' (.side z))
        (rebaseUnit (D.seamRank q).symm (D.bandCutChosenJ q φ seed' b0 i0 a))
        (rebaseUnit (D.seamRank q).symm
          ((D.bandCutChosenT q φ seed' b0 i0 t)⁻¹*(D.bandCutChosenJ q φ seed' b0 i0 a)⁻¹*
            D.bandCutP q seed'*(D.bandCutChosenT q φ seed' b0 i0 t))) side := by
  rfl

lemma parent_markedLiftPortFrame
    (hpMark : D.Proper) (hmaxMark : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (φ : R →+* K)
    (seed : (z : D.Generator) → (Matrix (Fin (D.generatorRank z)) (Fin (D.generatorRank z)) K)ˣ)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
    (t a : (Matrix (Fin (D.rank (D.bandCutParent q))) (Fin (D.rank (D.bandCutParent q))) K)ˣ)
    (frames : (D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).PortFrames (R:=K))
    (p : LocalPort _ (D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).ports.kind) :
    (D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).portFrame
      (D.refinedMarkedLiftValues q d hp hc hc' hpMark hmaxMark φ seed b0 i0 t a frames) p=frames p := by
  exact D.parent_markedBandPortFrame q d hp hc hc' hpMark hmaxMark frames
    (D.bandCutLiftGenerators q φ seed b0 t a)
    (D.bandCutChosenJ q φ (D.bandCutLiftGenerators q φ seed b0 t a) b0 i0 a)
    (D.bandCutChosenT q φ (D.bandCutLiftGenerators q φ seed b0 t a) b0 i0 t)
    (D.bandCutRetainedHandles q (D.bandCutLiftGenerators q φ seed b0 t a) t) p
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
#check OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_markedLiftSideValue
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_markedLiftSideValue
#check OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_markedLiftPortFrame
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_markedLiftPortFrame
