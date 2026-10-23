import TransportedFrameNamed
import NamedEndpointFlagFromFrames
import UnitSideSeam
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.MarkedFrames
set_option maxHeartbeats 0
set_option quotPrecheck false
set_option autoImplicit false
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
variable (u : Fin ((w).shape.atomicBand.length+1))
    (p : ((w).shape.atomicBand.kind u).table.Port)
local notation "kk" => (w).shape.atomicBand.kind u
local notation "mp" => (kk).mirrorPort p
local notation "lo" => (w).shape.vertexAtoms u
local notation "lm" => ((w).shape.vertexAtoms u).mirror
local notation "po" => (⟨.inr (.inl u),p⟩ : LocalPort _ (C).ports.kind)
local notation "pm" => (⟨.inr (.inr u),mp⟩ : LocalPort _ (C).ports.kind)

def external_transverseRawColumns : (lo).localRanks.Columns p ≃ (lm).localRanks.Columns mp :=
  (lo).seamColumns lm p mp ((kk).mirrorChild p)
    (fun a => ((lo).mirror_atoms ⟨p,some a⟩).symm)
def external_transverseRawParent : (lo).localRanks.Parent p ≃ (lm).localRanks.Parent mp :=
  finCongr ((lo).rank_of_atoms lm ((lo).mirror_atoms ⟨p,none⟩).symm)
def external_transverseOrigColumns : (lo).localRanks.Columns p ≃ ((C).vertexRanks (po).1).Columns (po).2 :=
  Equiv.sigmaCongr (Equiv.refl _) (fun c => finCongr
    (congrArg (fun d => d.rank p (some c)) (D.namedCut_orig_localRanks q w u)))
def external_transverseMirrorColumns : (lo).localRanks.Columns p ≃ ((C).vertexRanks (pm).1).Columns (pm).2 :=
  (D.external_transverseRawColumns q w u p).trans
    (Equiv.sigmaCongr (Equiv.refl _) (fun c => finCongr
      (congrArg (fun d => d.rank mp (some c)) (D.namedCut_mirror_localRanks q w u))))
def external_transverseOrigParent : (lo).localRanks.Parent p ≃ ((C).vertexRanks (po).1).Parent (po).2 :=
  finCongr (congrArg (fun d => d.rank p none) (D.namedCut_orig_localRanks q w u))
def external_transverseMirrorParent : (lo).localRanks.Parent p ≃ ((C).vertexRanks (pm).1).Parent (pm).2 :=
  (D.external_transverseRawParent q w u p).trans
    (finCongr (congrArg (fun d => d.rank mp none) (D.namedCut_mirror_localRanks q w u)))

lemma external_transverseOrigFrame (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩))) (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    (D.namedCutPortFrames q w old T po).reindex
      (D.external_transverseOrigColumns q w u p) (D.external_transverseOrigParent q w u p)=
      (w).vertexFrames u p := by
  exact LocalRanks.external_transportFrames_reindex
    (D.namedCut_orig_localRanks q w u) ((w).vertexFrames u) p

lemma external_transverseMirrorFrame (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩))) (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
    (hin : p≠(kk).input) (hout : p≠(kk).output) :
    (D.namedCutPortFrames q w old T pm).reindex
      (D.external_transverseMirrorColumns q w u p) (D.external_transverseMirrorParent q w u p)=
      (w).vertexFrames u p := by
  have hh := LocalRanks.external_transportFrames_reindex_extra
    (D.namedCut_mirror_localRanks q w u) ((w).mirrorVertexFrames T u) mp
    (D.external_transverseRawColumns q w u p) (D.external_transverseRawParent q w u p)
  exact hh.trans ((w).transverse_frame_seam T u p hin hout)

variable (ss : (BandGraft.wiring A q B).Seam) (b : Bool)
    (ho : (C).ports.attach po=(ss,b)) (hm : (C).ports.attach pm=(ss,!b))
def external_transverseOrigNamedColumns (ss : (BandGraft.wiring A q B).Seam) (b : Bool)
    (ho : (C).ports.attach po=(ss,b)) :=
  ((D.external_transverseOrigColumns q w u p).trans ((C).external_portColumns po)).trans
    ((C).external_seamColumnsTransport (congrArg Prod.fst ho))
def external_transverseMirrorNamedColumns (ss : (BandGraft.wiring A q B).Seam) (b : Bool)
    (hm : (C).ports.attach pm=(ss,!b)) :=
  ((D.external_transverseMirrorColumns q w u p).trans ((C).external_portColumns pm)).trans
    ((C).external_seamColumnsTransport (congrArg Prod.fst hm))
def external_transverseCommonParent (ss : (BandGraft.wiring A q B).Seam) (b : Bool)
    (ho : (C).ports.attach po=(ss,b)) :=
  (D.external_transverseOrigParent q w u p).trans
    (finCongr (congrArg (fun z => (C).rank ((C).ports.facet ⟨z,none⟩)) (congrArg Prod.fst ho)))

lemma external_transverseNamedColumns_eq
    (ss : (BandGraft.wiring A q B).Seam) (b : Bool)
    (ho : (C).ports.attach po=(ss,b)) (hm : (C).ports.attach pm=(ss,!b)) :
    D.external_transverseOrigNamedColumns q w u p ss b ho=
      D.external_transverseMirrorNamedColumns q w u p ss b hm := by
  apply Equiv.ext
  intro i
  have hfst : (D.external_transverseOrigNamedColumns q w u p ss b ho i).1=
      (D.external_transverseMirrorNamedColumns q w u p ss b hm i).1 := by
    apply Fin.ext
    change (((kk).childEnumeration p) i.1).val=
      (((kk).mirror.childEnumeration mp) (((kk).mirrorChild p) i.1)).val
    rw [Kind.mirror_childEnumeration]
    rfl
  apply Sigma.ext hfst
  apply (Fin.heq_ext_iff (congrArg ((C).childDim ss) hfst)).2
  rfl

lemma external_transverseCommonParent_mirror
    (ss : (BandGraft.wiring A q B).Seam) (b : Bool)
    (ho : (C).ports.attach po=(ss,b)) (hm : (C).ports.attach pm=(ss,!b)) :
    D.external_transverseCommonParent q w u p ss b ho=
      (D.external_transverseMirrorParent q w u p).trans
        (finCongr (congrArg (fun z => (C).rank ((C).ports.facet ⟨z,none⟩)) (congrArg Prod.fst hm))) := by
  apply Equiv.ext
  intro i
  rfl
lemma external_transverseOrigEndpoint
    (ss : (BandGraft.wiring A q B).Seam) (b : Bool)
    (ho : (C).ports.attach po=(ss,b)) (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩))) (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    ((C).external_endpointNamedMatrix (D.namedCutPortFrames q w old T) po ss b ho).reindex
      (D.external_transverseOrigNamedColumns q w u p ss b ho)
      (D.external_transverseCommonParent q w u p ss b ho)=(w).vertexFrames u p := by
  exact ((C).external_endpointNamedMatrix_normalized (D.namedCutPortFrames q w old T)
    po ss b ho (D.external_transverseOrigColumns q w u p)
    (D.external_transverseOrigParent q w u p)).trans
      (D.external_transverseOrigFrame q w u p old T)

lemma external_transverseMirrorEndpoint
    (ss : (BandGraft.wiring A q B).Seam) (b : Bool)
    (ho : (C).ports.attach po=(ss,b)) (hm : (C).ports.attach pm=(ss,!b)) (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩))) (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
    (hin : p≠(kk).input) (hout : p≠(kk).output) :
    ((C).external_endpointNamedMatrix (D.namedCutPortFrames q w old T) pm ss (!b) hm).reindex
      (D.external_transverseOrigNamedColumns q w u p ss b ho)
      (D.external_transverseCommonParent q w u p ss b ho)=(w).vertexFrames u p := by
  erw [D.external_transverseNamedColumns_eq q w u p ss b ho hm,
    D.external_transverseCommonParent_mirror q w u p ss b ho hm]
  exact ((C).external_endpointNamedMatrix_normalized (D.namedCutPortFrames q w old T)
    pm ss (!b) hm (D.external_transverseMirrorColumns q w u p)
    (D.external_transverseMirrorParent q w u p)).trans
      (D.external_transverseMirrorFrame q w u p old T hin hout)

lemma external_transverseSeam
    (ss : (BandGraft.wiring A q B).Seam) (b : Bool)
    (ho : (C).ports.attach po=(ss,b)) (hm : (C).ports.attach pm=(ss,!b))
    {R : Type} [CommRing R] (φ : R →+* K)
    (g : (e : (C).Generator) →
      (Matrix (Fin ((C).generatorRank e)) (Fin ((C).generatorRank e)) K)ˣ)
    (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩))) (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
    (hin : p≠(kk).input) (hout : p≠(kk).output)
    (hframes : ∀ a,(C).portFrame g a=D.namedCutPortFrames q w old T a)
    (hone : ∀ i : Option (Fin ((BandGraft.wiring A q B).seamArity ss)),g (.side ⟨ss,i⟩)=1) :
    SameFramedFlag ((C).seamGrade ss)
      (matrixUnitEquiv (((C).seamLeft ss).eval φ g))
      (matrixUnitEquiv (((C).seamRight ss).eval φ g)) := by
  apply (C).external_unitSideSeam ss φ g hone
  cases b
  · apply (C).external_endpointFlag_of_portFrame g (D.namedCutPortFrames q w old T) hframes
      ss pm po hm ho (D.external_transverseOrigNamedColumns q w u p ss false ho)
      (D.external_transverseCommonParent q w u p ss false ho)
    erw [D.external_transverseOrigEndpoint q w u p ss false ho old T,
      D.external_transverseMirrorEndpoint q w u p ss false ho hm old T hin hout]
    exact ⟨fun _ => rfl,fun _ _ _ => rfl⟩
  · apply (C).external_endpointFlag_of_portFrame g (D.namedCutPortFrames q w old T) hframes
      ss po pm ho hm (D.external_transverseOrigNamedColumns q w u p ss true ho)
      (D.external_transverseCommonParent q w u p ss true ho)
    erw [D.external_transverseOrigEndpoint q w u p ss true ho old T,
      D.external_transverseMirrorEndpoint q w u p ss true ho hm old T hin hout]
    exact ⟨fun _ => rfl,fun _ _ _ => rfl⟩
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram

#check OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_transverseSeam
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.external_transverseSeam
