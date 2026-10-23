import RefinedFirstShortAtPortV2
import NamedTransportOne
set_option maxHeartbeats 0
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {r : ℕ} (d : TwoFlagBand.RankShape (arity q) (arity q) r)
    (hp : D.rank (D.ports.facet ⟨q,none⟩)=r)
    (hc : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.row i))
    (hc' : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.col i))
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
local notation "C" => D.refinedMarkedDiagram q d hp hc hc' hproper hmax
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q d)
local notation "B" => D.ports.refinedBandForSeam q d
local notation "s0" => BandGraft.originalPort A q B 0 true

lemma external_markedBandFirstSide_one
    (frames : (C).PortFrames (R:=K))
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (J T : (Matrix (Fin (D.seamDim q)) (Fin (D.seamDim q)) K)ˣ)
    (h : (f : F) → Fin ((D.bandCutDiagram q).genus f) → Bool →
      (Matrix (Fin (D.rank f)) (Fin (D.rank f)) K)ˣ)
    (i : Option (Fin ((BandGraft.wiring A q B).seamArity s0))) :
    D.refinedMarkedBandValues q d hp hc hc' hproper hmax frames g J T h
      (.side ⟨s0,i⟩) = 1 := by
  exact D.external_refinedFirstShortSideValuesAtPortV2 q d hp hc hc'
    (fun a => g (.side a)) (rebaseUnit (D.seamRank q).symm J)
    (rebaseUnit (D.seamRank q).symm (T⁻¹*J⁻¹*D.bandCutP q g*T)) i

lemma external_markedLiftFirstSide_one
    (φ : R →+* K)
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
    (t a : (Matrix (Fin (D.rank (D.bandCutParent q)))
      (Fin (D.rank (D.bandCutParent q))) K)ˣ)
    (frames : (C).PortFrames (R:=K))
    (i : Option (Fin ((BandGraft.wiring A q B).seamArity s0))) :
    D.refinedMarkedLiftValues q d hp hc hc' hproper hmax φ g b0 i0 t a frames
      (.side ⟨s0,i⟩) = 1 := by
  exact D.external_markedBandFirstSide_one q d hp hc hc' hproper hmax frames
    (D.bandCutLiftGenerators q φ g b0 t a)
    (D.bandCutChosenJ q φ (D.bandCutLiftGenerators q φ g b0 t a) b0 i0 a)
    (D.bandCutChosenT q φ (D.bandCutLiftGenerators q φ g b0 t a) b0 i0 t)
    (D.bandCutRetainedHandles q (D.bandCutLiftGenerators q φ g b0 t a) t) i

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
