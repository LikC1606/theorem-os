import TransportedFrameNamed
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
    (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))

local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "s0" => BandGraft.originalPort A q B (Fin.last (B).length) false
local notation "p0" => (Subtype.val (BandGraft.originalPort A q B (Fin.last (B).length) false))

lemma parent_selectedLastColumnGrade (c : (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).table.Child
    (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output) :
    ((C).ports.childEquiv p0 c).val = (w.lastChild c).val := rfl

lemma parent_selectedLastColumnRank (c : (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).table.Child
    (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output) :
    ((C).vertexRanks (p0).1).rank (p0).2 (some c) = D.childDim q (w.lastChild c) := by
  exact ((D.refinedCut_orig_ranks q w.shape rfl w.rowRanks w.colRanks (Fin.last (B).length) _ _).symm).trans
    (w.lastChild_rank c)

lemma parent_selectedLastPortParentRank :
    ((C).vertexRanks (p0).1).rank (p0).2 none = D.rank (D.ports.facet ⟨q,none⟩) := by
  exact ((D.refinedCut_orig_ranks q w.shape rfl w.rowRanks w.colRanks (Fin.last (B).length) _ _).symm).trans
    w.lastParent_rank

def parent_selectedLastPortColumns : ((C).vertexRanks (p0).1).Columns (p0).2 ≃
    ((i : Fin (arity q)) × Fin (D.childDim q i)) :=
  Equiv.sigmaCongr w.lastChild (fun c => finCongr (D.parent_selectedLastColumnRank q w c))

lemma parent_selectedLastPortFrame_eq :
    ((D.namedCutPortFrames q w old T p0).reindex
      (D.parent_selectedLastPortColumns q w).symm
      (finCongr (D.parent_selectedLastPortParentRank q w)).symm).linearEquiv = w.lastFrame := by
  have ec : w.lastColumns.symm.trans
      (Equiv.sigmaCongr (Equiv.refl ((w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).table.Child (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output))
        (fun c => finCongr (congrArg (fun d => d.rank (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output (some c))
          (D.namedCut_orig_localRanks q w (Fin.last (B).length))))) =
      (D.parent_selectedLastPortColumns q w).symm := by
    apply Equiv.ext
    intro i
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Fin.ext
      rfl
  have ep : (finCongr w.lastParent_rank).symm.trans
      (finCongr (congrArg (fun d => d.rank (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output none)
        (D.namedCut_orig_localRanks q w (Fin.last (B).length)))) =
      (finCongr (D.parent_selectedLastPortParentRank q w)).symm := by
    ext i
    rfl
  have hh := LocalRanks.external_transportFrames_reindex_extra
    (D.namedCut_orig_localRanks q w (Fin.last w.shape.atomicBand.length))
    (w.vertexFrames (Fin.last w.shape.atomicBand.length))
    (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output
    w.lastColumns.symm (finCongr w.lastParent_rank).symm
  have hh2 := congrArg MatrixIso.linearEquiv hh
  erw [ec, ep] at hh2
  exact hh2

def parent_selectedLastNamedColumns :=
    (D.parent_selectedLastPortColumns q w).symm.trans ((C).external_portColumns p0)

lemma parent_selectedLastNamedColumns_grade (i : (j : Fin (arity q)) × Fin (D.childDim q j)) :
    (D.parent_selectedLastNamedColumns q w i).1.val = i.1.val := by
  change (w.lastChild (w.lastChild.symm i.1)).val = i.1.val
  rw [Equiv.apply_symm_apply]


end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_selectedLastPortFrame_eq
