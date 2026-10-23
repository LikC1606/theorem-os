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
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
local notation "CC" => D.refinedCutDiagram q d hp hc hc'
local notation "MM" => D.refinedMarkedDiagram q d hp hc hc' hproper hmax
variable (g : (e : (MM).Generator) →
    (Matrix (Fin ((MM).generatorRank e)) (Fin ((MM).generatorRank e)) K)ˣ)

def external_markedAsCutValues
    (hpMark : D.Proper) (hmaxMark : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (z : (e : (D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).Generator) →
      (Matrix (Fin ((D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).generatorRank e))
        (Fin ((D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).generatorRank e)) K)ˣ) : (e : (CC).Generator) →
    (Matrix (Fin ((CC).generatorRank e)) (Fin ((CC).generatorRank e)) K)ˣ
  | .side a => z (.side a)
  | .frame s b => z (.frame s b)
  | .handle f k b => z (.handle f k b)

lemma external_markedAsCutValues_portFrame
    (hpMark : D.Proper) (hmaxMark : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (z : (e : (D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).Generator) →
      (Matrix (Fin ((D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).generatorRank e))
        (Fin ((D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).generatorRank e)) K)ˣ)
    (p : LocalPort _ (CC).ports.kind) :
    (CC).portFrame (R:=K) (D.external_markedAsCutValues q d hp hc hc' hpMark hmaxMark z) p=
      (D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).portFrame (R:=K) z p := by
  rfl

lemma external_markedSeam_of_cut
    (hpMark : D.Proper) (hmaxMark : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (z : (e : (D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).Generator) →
      (Matrix (Fin ((D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).generatorRank e))
        (Fin ((D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).generatorRank e)) K)ˣ) (φ : R →+* K)
    (s : (BandGraft.wiring
      (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q d)) q
      (D.ports.refinedBandForSeam q d)).Seam)
    (hs : SameFramedFlag ((CC).seamGrade s)
      (matrixUnitEquiv (((CC).seamLeft s).eval φ
        (D.external_markedAsCutValues q d hp hc hc' hpMark hmaxMark z)))
      (matrixUnitEquiv (((CC).seamRight s).eval φ
        (D.external_markedAsCutValues q d hp hc hc' hpMark hmaxMark z)))) :
    SameFramedFlag ((D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).seamGrade s)
      (matrixUnitEquiv (((D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).seamLeft s).eval φ z))
      (matrixUnitEquiv (((D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).seamRight s).eval φ z)) := by
  apply (D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).named_seam_iff s φ z |>.mpr
  have hh := ((CC).named_seam_iff s φ
    (D.external_markedAsCutValues q d hp hc hc' hpMark hmaxMark z)).mp hs
  exact hh
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
#check OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_markedAsCutValues
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_markedAsCutValues
#check OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_markedAsCutValues_portFrame
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_markedAsCutValues_portFrame
#check OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_markedSeam_of_cut
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_markedSeam_of_cut
