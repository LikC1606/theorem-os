import TransportedFrameNamed
import NamedEndpointFlagFromFrames
import UnitSideSeam
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.MarkedFrames
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
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q (w).shape)
local notation "B" => D.ports.refinedBandForSeam q (w).shape
local notation "C" => D.refinedCutDiagram q (w).shape rfl (w).rowRanks (w).colRanks
variable (j : Fin (w).shape.atomicBand.length)
local notation "ss" => BandGraft.originalPort A q B j.succ true
local notation "pp" => Subtype.val (BandGraft.originalPort A q B j.succ true)
local notation "nn" => Subtype.val (BandGraft.originalPort A q B j.castSucc false)
local notation "ko" => ((w).shape.atomicBand.kind j.castSucc).output
local notation "ki" => ((w).shape.atomicBand.kind j.succ).input
local notation "lo" => (w).shape.vertexAtoms j.castSucc
local notation "li" => (w).shape.vertexAtoms j.succ

lemma external_originalInternalPositiveAttach : (C).ports.attach pp=(ss,true) :=
  (BandGraft.wiring A q B).endOf_portAt (ss,true)
lemma external_originalInternalNegativeAttach : (C).ports.attach nn=(ss,false) := by
  have hh := (BandGraft.wiring A q B).endOf_portAt (ss,false)
  change (BandGraft.wiring A q B).endOf ((BandGraft.wiring A q B).wire ss).val=_ at hh
  erw [BandGraft.wire_original] at hh
  exact hh

def external_originalInternalRawColumns : (lo).localRanks.Columns ko ≃ (li).localRanks.Columns ki :=
  (lo).seamColumns li ko ki ((w).interiorChild j)
    (fun a => congrArg (w).shape.facetAtoms ((w).interior_child j a))
def external_originalInternalRawParent : (lo).localRanks.Parent ko ≃ (li).localRanks.Parent ki :=
  finCongr ((lo).rank_of_atoms li (congrArg (w).shape.facetAtoms ((w).interior_parent j)))

def external_originalInternalNegativeColumns : (lo).localRanks.Columns ko ≃
    ((C).vertexRanks (nn).1).Columns (nn).2 :=
  Equiv.sigmaCongr (Equiv.refl _) (fun c => finCongr
    (congrArg (fun d => d.rank ko (some c)) (D.namedCut_orig_localRanks q w j.castSucc)))
def external_originalInternalPositiveColumns : (lo).localRanks.Columns ko ≃
    ((C).vertexRanks (pp).1).Columns (pp).2 :=
  (D.external_originalInternalRawColumns q w j).trans
    (Equiv.sigmaCongr (Equiv.refl _) (fun c => finCongr
      (congrArg (fun d => d.rank ki (some c)) (D.namedCut_orig_localRanks q w j.succ))))
def external_originalInternalNegativeParent : (lo).localRanks.Parent ko ≃
    ((C).vertexRanks (nn).1).Parent (nn).2 :=
  finCongr (congrArg (fun d => d.rank ko none) (D.namedCut_orig_localRanks q w j.castSucc))
def external_originalInternalPositiveParent : (lo).localRanks.Parent ko ≃
    ((C).vertexRanks (pp).1).Parent (pp).2 :=
  (D.external_originalInternalRawParent q w j).trans
    (finCongr (congrArg (fun d => d.rank ki none) (D.namedCut_orig_localRanks q w j.succ)))

lemma external_originalInternalNegativeFrame (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    (D.namedCutPortFrames q w old T nn).reindex
      (D.external_originalInternalNegativeColumns q w j)
      (D.external_originalInternalNegativeParent q w j) = (w).vertexFrames j.castSucc ko := by
  exact LocalRanks.external_transportFrames_reindex
    (D.namedCut_orig_localRanks q w j.castSucc) ((w).vertexFrames j.castSucc) ko

lemma external_originalInternalPositiveFrame (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    (D.namedCutPortFrames q w old T pp).reindex
      (D.external_originalInternalPositiveColumns q w j)
      (D.external_originalInternalPositiveParent q w j) = (w).vertexFrames j.castSucc ko := by
  have hh := LocalRanks.external_transportFrames_reindex_extra
    (D.namedCut_orig_localRanks q w j.succ) ((w).vertexFrames j.succ) ki
    (D.external_originalInternalRawColumns q w j) (D.external_originalInternalRawParent q w j)
  exact hh.trans ((w).interior_frame_seam j)

def external_originalInternalNegativeNamedColumns :=
  ((D.external_originalInternalNegativeColumns q w j).trans ((C).external_portColumns nn)).trans
    ((C).external_seamColumnsTransport
      (congrArg Prod.fst (D.external_originalInternalNegativeAttach q w j)))
def external_originalInternalPositiveNamedColumns :=
  ((D.external_originalInternalPositiveColumns q w j).trans ((C).external_portColumns pp)).trans
    ((C).external_seamColumnsTransport
      (congrArg Prod.fst (D.external_originalInternalPositiveAttach q w j)))
def external_originalInternalCommonParent :=
  (D.external_originalInternalNegativeParent q w j).trans
    (finCongr (congrArg (fun z => (C).rank ((C).ports.facet ⟨z,none⟩))
      (congrArg Prod.fst (D.external_originalInternalNegativeAttach q w j))))

lemma external_originalInternalNamedColumns_eq :
    D.external_originalInternalNegativeNamedColumns q w j =
      D.external_originalInternalPositiveNamedColumns q w j := by
  apply Equiv.ext
  intro i
  have hfst : (D.external_originalInternalNegativeNamedColumns q w j i).1 =
      (D.external_originalInternalPositiveNamedColumns q w j i).1 := by
    apply Fin.ext
    change (((w).shape.atomicBand.kind j.castSucc).childEnumeration ko i.1).val =
      (((w).shape.atomicBand.kind j.succ).childEnumeration ki ((w).interiorChild j i.1)).val
    simp only [IdentifiedBand.interiorChild,Equiv.trans_apply,Equiv.apply_symm_apply]
    rfl
  apply Sigma.ext hfst
  apply (Fin.heq_ext_iff (congrArg ((C).childDim ss) hfst)).2
  rfl

lemma external_originalInternalCommonParent_positive :
    D.external_originalInternalCommonParent q w j =
      (D.external_originalInternalPositiveParent q w j).trans
        (finCongr (congrArg (fun z => (C).rank ((C).ports.facet ⟨z,none⟩))
          (congrArg Prod.fst (D.external_originalInternalPositiveAttach q w j)))) := by
  apply Equiv.ext
  intro i
  rfl

lemma external_originalInternalNegativeEndpoint (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    ((C).external_endpointNamedMatrix (D.namedCutPortFrames q w old T)
      nn ss false (D.external_originalInternalNegativeAttach q w j)).reindex
      (D.external_originalInternalNegativeNamedColumns q w j)
      (D.external_originalInternalCommonParent q w j) = (w).vertexFrames j.castSucc ko := by
  have hh := (C).external_endpointNamedMatrix_normalized
    (D.namedCutPortFrames q w old T) nn ss false (D.external_originalInternalNegativeAttach q w j)
    (D.external_originalInternalNegativeColumns q w j)
    (D.external_originalInternalNegativeParent q w j)
  exact hh.trans (D.external_originalInternalNegativeFrame q w j old T)

lemma external_originalInternalPositiveEndpoint (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    ((C).external_endpointNamedMatrix (D.namedCutPortFrames q w old T)
      pp ss true (D.external_originalInternalPositiveAttach q w j)).reindex
      (D.external_originalInternalNegativeNamedColumns q w j)
      (D.external_originalInternalCommonParent q w j) = (w).vertexFrames j.castSucc ko := by
  erw [D.external_originalInternalNamedColumns_eq q w j,
    D.external_originalInternalCommonParent_positive q w j]
  have hh := (C).external_endpointNamedMatrix_normalized
    (D.namedCutPortFrames q w old T) pp ss true (D.external_originalInternalPositiveAttach q w j)
    (D.external_originalInternalPositiveColumns q w j)
    (D.external_originalInternalPositiveParent q w j)
  exact hh.trans (D.external_originalInternalPositiveFrame q w j old T)

lemma external_originalInternalSeam
    {R : Type} [CommRing R] (φ : R →+* K)
    (g : (e : (C).Generator) →
      (Matrix (Fin ((C).generatorRank e)) (Fin ((C).generatorRank e)) K)ˣ)
    (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
    (hframes : ∀ p,(C).portFrame g p=D.namedCutPortFrames q w old T p)
    (hone : ∀ i : Option (Fin ((BandGraft.wiring A q B).seamArity ss)),g (.side ⟨ss,i⟩)=1) :
    SameFramedFlag ((C).seamGrade ss)
      (matrixUnitEquiv (((C).seamLeft ss).eval φ g))
      (matrixUnitEquiv (((C).seamRight ss).eval φ g)) := by
  apply (C).external_unitSideSeam ss φ g hone
  apply (C).external_endpointFlag_of_portFrame g (D.namedCutPortFrames q w old T) hframes
    ss pp nn (D.external_originalInternalPositiveAttach q w j)
    (D.external_originalInternalNegativeAttach q w j)
    (D.external_originalInternalNegativeNamedColumns q w j)
    (D.external_originalInternalCommonParent q w j)
  erw [D.external_originalInternalNegativeEndpoint q w j old T,
    D.external_originalInternalPositiveEndpoint q w j old T]
  exact ⟨fun _ => rfl,fun _ _ _ => rfl⟩
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
