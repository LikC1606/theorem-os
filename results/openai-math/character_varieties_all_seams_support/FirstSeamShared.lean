import FirstCommonEqualityV3
import FirstPortFrameShared
import FirstNegativeFrameShared
import EndpointNormalization
import NamedEndpointFlagFromFrames
import UnitSideSeam
set_option autoImplicit false
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
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "s0" => BandGraft.originalPort A q B 0 true
local notation "p0" => (Subtype.val (BandGraft.originalPort A q B 0 true))
local notation "pold" => (Subtype.val (D.ports.portAt false q))
local notation "pn" => (Subtype.val (BandGraft.oldPort A q B q false))

lemma external_firstPositiveEndpoint_eq
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    (((C).external_endpointNamedMatrix (D.namedCutPortFrames q w (D.portFrame g) T)
      p0 s0 true (D.external_firstAttach q w)).reindex
      (D.external_firstCommonColumns q w) (D.external_firstCommonParent q w)).linearEquiv =
        w.firstFrame := by
  have hp : D.external_firstCommonParent q w =
      (finCongr (D.external_firstPortParentRank q w)).symm.trans
        (finCongr (congrArg (fun z => (C).rank ((C).ports.facet ⟨z,none⟩))
          (congrArg Prod.fst (D.external_firstAttach q w)))) := by
    apply Equiv.ext
    intro i
    rfl
  have hh := (C).external_endpointNamedMatrix_normalized
    (D.namedCutPortFrames q w (D.portFrame g) T) p0 s0 true
    (D.external_firstAttach q w) (D.external_firstPortColumns q w).symm
    (finCongr (D.external_firstPortParentRank q w)).symm
  have hc := D.external_firstCommonColumns_positive q w
  have h1 := congrArg MatrixIso.linearEquiv hh
  erw [← hc,← hp] at h1
  exact h1.trans (D.external_firstPortFrame_eq q w (D.portFrame g) T)

lemma external_firstNegativePortParentRank :
    ((C).vertexRanks (pn).1).rank (pn).2 none = D.rank (D.ports.facet ⟨q,none⟩) := by
  have hh := congrArg (fun d => d.rank (pold).2 none)
    (D.refinedCut_old_vertexRanks q w.shape rfl w.rowRanks w.colRanks (pold).1)
  exact hh.trans (congrArg (fun e : S × Bool => D.rank (D.ports.facet ⟨e.1,none⟩))
    (D.ports.attach_portAt q false))

lemma external_firstNegativeEndpoint_eq
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    (((C).external_endpointNamedMatrix (D.namedCutPortFrames q w (D.portFrame g) T)
      pn s0 false (D.external_firstNegativeAttach_core q w)).reindex
      (D.external_firstCommonColumns q w) (D.external_firstCommonParent q w)).linearEquiv =
        D.namedSeamFrame q (g (.frame q false)) := by
  have hp : D.external_firstCommonParent q w =
      (finCongr (D.external_firstNegativePortParentRank q w)).symm.trans
        (finCongr (congrArg (fun z => (C).rank ((C).ports.facet ⟨z,none⟩))
          (congrArg Prod.fst (D.external_firstNegativeAttach_core q w)))) := by
    apply Equiv.ext
    intro i
    rfl
  have hh := (C).external_endpointNamedMatrix_normalized
    (D.namedCutPortFrames q w (D.portFrame g) T) pn s0 false
    (D.external_firstNegativeAttach_core q w) (D.external_firstNegativePortColumns q w).symm
    (finCongr (D.external_firstNegativePortParentRank q w)).symm
  have h1 := congrArg MatrixIso.linearEquiv hh
  erw [← hp] at h1
  exact h1.trans (D.external_firstNegativePortFrame_eq q w g T)

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "s0" => BandGraft.originalPort A q B 0 true
local notation "p0" => (Subtype.val (BandGraft.originalPort A q B 0 true))
local notation "pn" => (Subtype.val (BandGraft.oldPort A q B q false))

lemma external_firstActualFlagFromPortFrames_shared
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
    (z : (e : (C).Generator) → (Matrix (Fin ((C).generatorRank e)) (Fin ((C).generatorRank e)) K)ˣ)
    (hframes : ∀ p,(C).portFrame z p=D.namedCutPortFrames q w (D.portFrame g) T p)
    (hf : f = D.namedSeamFrame q (g (.frame q false))) :
    SameFramedFlag (fun i : (j : Fin ((BandGraft.wiring A q B).seamArity s0)) × Fin ((C).childDim s0 j) => i.1.val)
      ((C).namedSeamFrame s0 (z (.frame s0 false)))
      ((C).namedSeamFrame s0 (z (.frame s0 true))) := by
  apply (C).external_endpointFlag_of_portFrame z (D.namedCutPortFrames q w (D.portFrame g) T)
    hframes s0 p0 pn (D.external_firstAttach q w) (D.external_firstNegativeAttach_core q w)
    (D.external_firstCommonColumns q w) (D.external_firstCommonParent q w)
  have hg : (fun i : (j : Fin (arity q)) × Fin (D.childDim q j) =>
      (D.external_firstCommonColumns q w i).1.val)=(fun i => i.1.val) := by
    funext i
    exact D.external_firstCommonColumns_grade q w i
  erw [hg,D.external_firstNegativeEndpoint_eq q w g T,D.external_firstPositiveEndpoint_eq q w g T]
  rw [← hf]
  have hh := w.firstFrame_holds
  refine ⟨fun k => (hh.1 k).symm,?_⟩
  intro k v hv
  exact (hh.2 k v (by rw [hh.1 (k+1)];exact hv)).symm
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram

#check OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_firstActualFlagFromPortFrames_shared
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_firstActualFlagFromPortFrames_shared
