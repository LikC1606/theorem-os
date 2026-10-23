import SigmaFinCoordinates
import FrameIndexBridge
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.MarkedFrames
set_option maxHeartbeats 0

namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
    (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))


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
    (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))

local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "s0" => BandGraft.originalPort A q B 0 true

lemma external_firstArity :
    (BandGraft.wiring A q B).seamArity s0 = arity q := w.firstArity

lemma external_firstParent :
    (C).rank ((C).ports.facet ⟨s0,none⟩) = D.rank (D.ports.facet ⟨q,none⟩) := by
  exact congrArg (D.ports.refinedRank q w.shape D.rank) (B).input_parent

lemma external_firstChild (c : (w.shape.atomicBand.kind 0).table.Child
    (w.shape.atomicBand.kind 0).input) :
    ((C).ports.childEquiv (s0).val c).val = (w.firstChild c).val := by
  rfl

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity)

def external_localNamedFrame (frames : D.PortFrames (R:=K)) (p : LocalPort V D.ports.kind) :=
  (frames p).reindex (D.external_portColumns p).symm (Equiv.refl _)

lemma external_localNamedFrame_eq
    (frames : D.PortFrames (R:=K)) (side : D.SideValues (R:=K))
    (handle : D.HandleValues (R:=K)) (p : LocalPort V D.ports.kind) :
    (D.external_localNamedFrame frames p).linearEquiv =
      D.namedSeamFrame (D.ports.attach p).1
        ((D.valuesFromPorts frames side handle)
          (.frame (D.ports.attach p).1 (D.ports.attach p).2)) :=
  (D.external_namedFrame_valuesFromPorts frames side handle p).symm

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
    (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))

local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "s0" => BandGraft.originalPort A q B 0 true
local notation "p0" => (Subtype.val (BandGraft.originalPort A q B 0 true))

lemma external_firstAttach : (C).ports.attach p0 = (s0,true) := by
  exact (BandGraft.wiring A q B).endOf_portAt (s0,true)

lemma external_firstPortParent :
    ((C).vertexRanks (p0).1).Parent (p0).2 = Fin (D.rank (D.ports.facet ⟨q,none⟩)) := by
  change Fin ((C).rank ((C).ports.facet ⟨((C).ports.attach p0).1,none⟩)) = _
  rw [D.external_firstAttach q w]
  exact congrArg Fin (D.external_firstParent q w)

lemma external_firstColumnGrade (c : (w.shape.atomicBand.kind 0).table.Child
    (w.shape.atomicBand.kind 0).input) :
    ((C).ports.childEquiv p0 c).val = (w.firstChild c).val := rfl

lemma external_firstColumnRank (c : (w.shape.atomicBand.kind 0).table.Child
    (w.shape.atomicBand.kind 0).input) :
    ((C).vertexRanks (p0).1).rank (p0).2 (some c) = D.childDim q (w.firstChild c) := by
  exact ((D.refinedCut_orig_ranks q w.shape rfl w.rowRanks w.colRanks 0 _ _).symm).trans
    (w.firstChild_rank c)

lemma external_firstPortParentRank :
    ((C).vertexRanks (p0).1).rank (p0).2 none = D.rank (D.ports.facet ⟨q,none⟩) := by
  exact ((D.refinedCut_orig_ranks q w.shape rfl w.rowRanks w.colRanks 0 _ _).symm).trans
    w.firstParent_rank

def external_firstPortColumns : ((C).vertexRanks (p0).1).Columns (p0).2 ≃
    ((i : Fin (arity q)) × Fin (D.childDim q i)) :=
  Equiv.sigmaCongr w.firstChild (fun c => finCongr (D.external_firstColumnRank q w c))


def external_firstNamedColumns :=
  (D.external_firstPortColumns q w).symm.trans ((C).external_portColumns p0)

lemma external_firstNamedColumns_grade (i : (j : Fin (arity q)) × Fin (D.childDim q j)) :
    (D.external_firstNamedColumns q w i).1.val = i.1.val := by
  change (w.firstChild (w.firstChild.symm i.1)).val = i.1.val
  rw [Equiv.apply_symm_apply]

lemma external_firstNamedColumns_snd
    (i : (j : Fin (arity q)) × Fin (D.childDim q j)) :
    (D.external_firstNamedColumns q w i).2.val = i.2.val := by
  unfold external_firstNamedColumns
  change ((C).external_portColumns p0 ((D.external_firstPortColumns q w).symm i)).2.val = _
  rw [(C).external_portColumns_snd]
  exact external_sigmaFinCongr_symm_snd w.firstChild
    (fun c => ((C).vertexRanks (p0).1).rank (p0).2 (some c))
    (D.childDim q) (D.external_firstColumnRank q w) i

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
local notation "pold" => (Subtype.val (D.ports.portAt false q))
local notation "pn" => (Subtype.val (BandGraft.oldPort A q B q false))

lemma external_firstNegativeAttach_core : (C).ports.attach pn = (s0,false) := by
  have hh := (BandGraft.wiring A q B).endOf_portAt (s0,false)
  change (BandGraft.wiring A q B).endOf
    ((BandGraft.wiring A q B).wire s0).val = _ at hh
  erw [BandGraft.wire_first] at hh
  exact hh

lemma external_firstNegativeChildRank
    (c : (D.ports.kind (pold).1).table.Child (pold).2) :
    ((C).vertexRanks (pn).1).rank (pn).2 (some c) =
      D.childDim q ((finCongr (congrArg (fun e => arity e.1)
        (D.ports.attach_portAt q false))) (D.ports.childEquiv pold c)) := by
  have hh := congrArg (fun d => d.rank (pold).2 (some c))
    (D.refinedCut_old_vertexRanks q w.shape rfl w.rowRanks w.colRanks (pold).1)
  change ((C).vertexRanks (.inl (pold).1)).rank (pold).2 (some c) = _
  rw [hh]
  change D.rank (D.ports.facet ⟨(D.ports.attach pold).1,some (D.ports.childEquiv pold c)⟩) = _
  have aux {s t : S} (he : s=t) (i : Fin (arity s)) :
      D.rank (D.ports.facet ⟨s,some i⟩) =
      D.rank (D.ports.facet ⟨t,some (finCongr (congrArg arity he) i)⟩) := by
    subst t
    rfl
  exact aux (congrArg Prod.fst (D.ports.attach_portAt q false)) _


def external_firstNegativeChild := (D.ports.childEquiv pold).trans
  (finCongr (congrArg (fun e => arity e.1) (D.ports.attach_portAt q false)))

def external_firstNegativePortColumns :
    ((C).vertexRanks (pn).1).Columns (pn).2 ≃ ((i : Fin (arity q)) × Fin (D.childDim q i)) :=
  Equiv.sigmaCongr (D.external_firstNegativeChild q) (fun c =>
    finCongr (D.external_firstNegativeChildRank q w c))

def external_firstNegativeNamedColumns :=
  (D.external_firstNegativePortColumns q w).symm.trans ((C).external_portColumns pn)

lemma external_firstNegativeNamedColumns_grade
    (i : (j : Fin (arity q)) × Fin (D.childDim q j)) :
    (D.external_firstNegativeNamedColumns q w i).1.val = i.1.val := by
  change ((D.external_firstNegativeChild q)
    ((D.external_firstNegativeChild q).symm i.1)).val = i.1.val
  rw [Equiv.apply_symm_apply]



lemma external_firstNegativeNamedColumns_snd
    (i : (j : Fin (arity q)) × Fin (D.childDim q j)) :
    (D.external_firstNegativeNamedColumns q w i).2.val = i.2.val := by
  unfold external_firstNegativeNamedColumns
  change ((C).external_portColumns pn ((D.external_firstNegativePortColumns q w).symm i)).2.val = _
  rw [(C).external_portColumns_snd]
  exact external_sigmaFinCongr_symm_snd (D.external_firstNegativeChild q)
    (fun c => ((C).vertexRanks (pn).1).rank (pn).2 (some c))
    (D.childDim q) (D.external_firstNegativeChildRank q w) i

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
local notation "pold" => (Subtype.val (D.ports.portAt false q))
local notation "pn" => (Subtype.val (BandGraft.oldPort A q B q false))

lemma external_firstSeamParentRank :
    (C).rank ((C).ports.facet ⟨s0,none⟩) = D.rank (D.ports.facet ⟨q,none⟩) := by
  exact congrArg (D.ports.refinedRank q w.shape D.rank) (B).input_parent

def external_firstCommonParent := (finCongr (D.external_firstSeamParentRank q w)).symm

def external_firstCommonColumns :=
  (D.external_firstNegativeNamedColumns q w).trans
    ((C).external_seamColumnsTransport
      (congrArg Prod.fst (D.external_firstNegativeAttach_core q w)))

lemma external_firstCommonColumns_grade
    (i : (j : Fin (arity q)) × Fin (D.childDim q j)) :
    (D.external_firstCommonColumns q w i).1.val = i.1.val := by
  exact D.external_firstNegativeNamedColumns_grade q w i


lemma external_firstCommonColumns_positive :
    D.external_firstCommonColumns q w =
      (D.external_firstNamedColumns q w).trans
        ((C).external_seamColumnsTransport
          (congrArg Prod.fst (D.external_firstAttach q w))) := by
  apply Equiv.ext
  intro i
  have hp := D.external_firstNamedColumns_grade q w i
  have hn := D.external_firstCommonColumns_grade q w i
  have he : (D.external_firstCommonColumns q w i).1 =
      (((D.external_firstNamedColumns q w).trans
        ((C).external_seamColumnsTransport
          (congrArg Prod.fst (D.external_firstAttach q w)))) i).1 := by
    apply Fin.ext
    exact hn.trans hp.symm
  apply Sigma.ext he
  apply (Fin.heq_ext_iff (congrArg ((C).childDim s0) he)).2
  have hp2 := D.external_firstNamedColumns_snd q w i
  have hn2 := D.external_firstNegativeNamedColumns_snd q w i
  have hpt := (C).external_seamColumnsTransport_snd
    (congrArg Prod.fst (D.external_firstAttach q w)) (D.external_firstNamedColumns q w i)
  have hnt := (C).external_seamColumnsTransport_snd
    (congrArg Prod.fst (D.external_firstNegativeAttach_core q w))
      (D.external_firstNegativeNamedColumns q w i)
  exact (hnt.trans hn2).trans (hpt.trans hp2).symm

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
