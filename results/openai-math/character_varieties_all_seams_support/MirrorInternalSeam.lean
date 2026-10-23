import TransportedFrameNamed
import NamedEndpointFlagFromFrames
import UnitSideSeam
import MirrorInteriorFrame
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
local notation "ss" => BandGraft.mirrorOutput A q B j.castSucc
local notation "pp" => Subtype.val (BandGraft.mirrorOutput A q B j.castSucc)
local notation "nn" => Subtype.val (BandGraft.mirrorInput A q B j.succ)
local notation "ko" => ((w).shape.atomicBand.kind j.castSucc).mirrorPort ((w).shape.atomicBand.kind j.castSucc).output
local notation "ki" => ((w).shape.atomicBand.kind j.succ).mirrorPort ((w).shape.atomicBand.kind j.succ).input
local notation "lo" => ((w).shape.vertexAtoms j.castSucc).mirror
local notation "li" => ((w).shape.vertexAtoms j.succ).mirror

lemma external_mirrorInternalPositiveAttach : (C).ports.attach pp=(ss,true) :=
  (BandGraft.wiring A q B).endOf_portAt (ss,true)
lemma external_mirrorInternalNegativeAttach : (C).ports.attach nn=(ss,false) := by
  have hh := (BandGraft.wiring A q B).endOf_portAt (ss,false)
  change (BandGraft.wiring A q B).endOf ((BandGraft.wiring A q B).wire ss).val=_ at hh
  erw [BandGraft.wire_mirror] at hh
  exact hh

def external_mirrorInternalRawColumns : (lo).localRanks.Columns ko ≃ (li).localRanks.Columns ki :=
  (lo).seamColumns li ko ki ((w).external_mirrorInteriorChild j)
    (fun a => congrArg (w).shape.facetAtoms ((w).external_mirrorInteriorChildColor j a))
def external_mirrorInternalRawParent : (lo).localRanks.Parent ko ≃ (li).localRanks.Parent ki :=
  finCongr ((lo).rank_of_atoms li (congrArg (w).shape.facetAtoms ((w).external_mirrorInteriorParent j)))

def external_mirrorInternalPositiveColumns : (lo).localRanks.Columns ko ≃
    ((C).vertexRanks (pp).1).Columns (pp).2 :=
  Equiv.sigmaCongr (Equiv.refl _) (fun c => finCongr
    (congrArg (fun d => d.rank ko (some c)) (D.namedCut_mirror_localRanks q w j.castSucc)))
def external_mirrorInternalNegativeColumns : (lo).localRanks.Columns ko ≃
    ((C).vertexRanks (nn).1).Columns (nn).2 :=
  (D.external_mirrorInternalRawColumns q w j).trans
    (Equiv.sigmaCongr (Equiv.refl _) (fun c => finCongr
      (congrArg (fun d => d.rank ki (some c)) (D.namedCut_mirror_localRanks q w j.succ))))
def external_mirrorInternalPositiveParent : (lo).localRanks.Parent ko ≃
    ((C).vertexRanks (pp).1).Parent (pp).2 :=
  finCongr (congrArg (fun d => d.rank ko none) (D.namedCut_mirror_localRanks q w j.castSucc))
def external_mirrorInternalNegativeParent : (lo).localRanks.Parent ko ≃
    ((C).vertexRanks (nn).1).Parent (nn).2 :=
  (D.external_mirrorInternalRawParent q w j).trans
    (finCongr (congrArg (fun d => d.rank ki none) (D.namedCut_mirror_localRanks q w j.succ)))

lemma external_mirrorInternalPositiveFrame (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    (D.namedCutPortFrames q w old T pp).reindex
      (D.external_mirrorInternalPositiveColumns q w j)
      (D.external_mirrorInternalPositiveParent q w j) = (w).mirrorVertexFrames T j.castSucc ko := by
  exact LocalRanks.external_transportFrames_reindex
    (D.namedCut_mirror_localRanks q w j.castSucc) ((w).mirrorVertexFrames T j.castSucc) ko

lemma external_mirrorInternalNegativeFrame (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    (D.namedCutPortFrames q w old T nn).reindex
      (D.external_mirrorInternalNegativeColumns q w j)
      (D.external_mirrorInternalNegativeParent q w j) = (w).mirrorVertexFrames T j.castSucc ko := by
  have hh := LocalRanks.external_transportFrames_reindex_extra
    (D.namedCut_mirror_localRanks q w j.succ) ((w).mirrorVertexFrames T j.succ) ki
    (D.external_mirrorInternalRawColumns q w j) (D.external_mirrorInternalRawParent q w j)
  exact hh.trans ((w).external_mirrorInteriorFrame T j)
def external_mirrorInternalNegativeNamedColumns :=
  ((D.external_mirrorInternalNegativeColumns q w j).trans ((C).external_portColumns nn)).trans
    ((C).external_seamColumnsTransport
      (congrArg Prod.fst (D.external_mirrorInternalNegativeAttach q w j)))
def external_mirrorInternalPositiveNamedColumns :=
  ((D.external_mirrorInternalPositiveColumns q w j).trans ((C).external_portColumns pp)).trans
    ((C).external_seamColumnsTransport
      (congrArg Prod.fst (D.external_mirrorInternalPositiveAttach q w j)))
def external_mirrorInternalCommonParent :=
  (D.external_mirrorInternalNegativeParent q w j).trans
    (finCongr (congrArg (fun z => (C).rank ((C).ports.facet ⟨z,none⟩))
      (congrArg Prod.fst (D.external_mirrorInternalNegativeAttach q w j))))

lemma external_mirrorInternalNamedColumns_eq :
    D.external_mirrorInternalNegativeNamedColumns q w j =
      D.external_mirrorInternalPositiveNamedColumns q w j := by
  apply Equiv.ext
  intro i
  have hfst : (D.external_mirrorInternalNegativeNamedColumns q w j i).1 =
      (D.external_mirrorInternalPositiveNamedColumns q w j i).1 := by
    apply Fin.ext
    let b := (((w).shape.atomicBand.kind j.castSucc).mirrorChild
      ((w).shape.atomicBand.kind j.castSucc).output).symm i.1
    have hb : i.1=(((w).shape.atomicBand.kind j.castSucc).mirrorChild
      ((w).shape.atomicBand.kind j.castSucc).output) b :=
      (((w).shape.atomicBand.kind j.castSucc).mirrorChild _).apply_symm_apply i.1 |>.symm
    have hi : (w).external_mirrorInteriorChild j
        ((((w).shape.atomicBand.kind j.castSucc).mirrorChild _) b)=
        (((w).shape.atomicBand.kind j.succ).mirrorChild _) ((w).interiorChild j b) := by
      simp only [IdentifiedBand.external_mirrorInteriorChild,Equiv.trans_apply,Equiv.symm_apply_apply]
    change ((((w).shape.atomicBand.kind j.succ).mirror.childEnumeration ki)
      ((w).external_mirrorInteriorChild j i.1)).val =
      ((((w).shape.atomicBand.kind j.castSucc).mirror.childEnumeration ko) i.1).val
    rw [hb]
    change ((((w).shape.atomicBand.kind j.succ).mirror.childEnumeration ki)
      ((w).external_mirrorInteriorChild j ((((w).shape.atomicBand.kind j.castSucc).mirrorChild _) b))).val =
      ((((w).shape.atomicBand.kind j.castSucc).mirror.childEnumeration ko)
        ((((w).shape.atomicBand.kind j.castSucc).mirrorChild _) b)).val
    rw [hi,Kind.mirror_childEnumeration,Kind.mirror_childEnumeration]
    change ((((w).shape.atomicBand.kind j.succ).childEnumeration _) ((w).interiorChild j b)).val =
      ((((w).shape.atomicBand.kind j.castSucc).childEnumeration _) b).val
    simp only [IdentifiedBand.interiorChild,Equiv.trans_apply,Equiv.apply_symm_apply]
    rfl
  apply Sigma.ext hfst
  apply (Fin.heq_ext_iff (congrArg ((C).childDim ss) hfst)).2
  rfl

lemma external_mirrorInternalCommonParent_positive :
    D.external_mirrorInternalCommonParent q w j =
      (D.external_mirrorInternalPositiveParent q w j).trans
        (finCongr (congrArg (fun z => (C).rank ((C).ports.facet ⟨z,none⟩))
          (congrArg Prod.fst (D.external_mirrorInternalPositiveAttach q w j)))) := by
  apply Equiv.ext
  intro i
  rfl

lemma external_mirrorInternalNegativeEndpoint (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    ((C).external_endpointNamedMatrix (D.namedCutPortFrames q w old T)
      nn ss false (D.external_mirrorInternalNegativeAttach q w j)).reindex
      (D.external_mirrorInternalNegativeNamedColumns q w j)
      (D.external_mirrorInternalCommonParent q w j) = (w).mirrorVertexFrames T j.castSucc ko := by
  have hh := (C).external_endpointNamedMatrix_normalized
    (D.namedCutPortFrames q w old T) nn ss false (D.external_mirrorInternalNegativeAttach q w j)
    (D.external_mirrorInternalNegativeColumns q w j)
    (D.external_mirrorInternalNegativeParent q w j)
  exact hh.trans (D.external_mirrorInternalNegativeFrame q w j old T)

lemma external_mirrorInternalPositiveEndpoint (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    ((C).external_endpointNamedMatrix (D.namedCutPortFrames q w old T)
      pp ss true (D.external_mirrorInternalPositiveAttach q w j)).reindex
      (D.external_mirrorInternalNegativeNamedColumns q w j)
      (D.external_mirrorInternalCommonParent q w j) = (w).mirrorVertexFrames T j.castSucc ko := by
  erw [D.external_mirrorInternalNamedColumns_eq q w j,
    D.external_mirrorInternalCommonParent_positive q w j]
  have hh := (C).external_endpointNamedMatrix_normalized
    (D.namedCutPortFrames q w old T) pp ss true (D.external_mirrorInternalPositiveAttach q w j)
    (D.external_mirrorInternalPositiveColumns q w j)
    (D.external_mirrorInternalPositiveParent q w j)
  exact hh.trans (D.external_mirrorInternalPositiveFrame q w j old T)

lemma external_mirrorInternalSeam
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
    ss pp nn (D.external_mirrorInternalPositiveAttach q w j)
    (D.external_mirrorInternalNegativeAttach q w j)
    (D.external_mirrorInternalNegativeNamedColumns q w j)
    (D.external_mirrorInternalCommonParent q w j)
  erw [D.external_mirrorInternalNegativeEndpoint q w j old T,
    D.external_mirrorInternalPositiveEndpoint q w j old T]
  exact ⟨fun _ => rfl,fun _ _ _ => rfl⟩
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
