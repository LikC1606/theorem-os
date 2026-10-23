import ParentWrapRawFrames
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
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "ss" => BandGraft.mirrorOutput A q B (Fin.last (B).length)
local notation "pp" => Subtype.val (BandGraft.mirrorOutput A q B (Fin.last (B).length))
local notation "nn" => Subtype.val (BandGraft.mirrorInput A q B 0)
lemma parent_wrapPositiveAttach : (C).ports.attach pp=(ss,true) :=
  (BandGraft.wiring A q B).endOf_portAt (ss,true)
lemma parent_wrapNegativeAttach : (C).ports.attach nn=(ss,false) := by
  have hh := (BandGraft.wiring A q B).endOf_portAt (ss,false)
  change (BandGraft.wiring A q B).endOf ((BandGraft.wiring A q B).wire ss).val=_ at hh
  erw [BandGraft.wire_mirror_wrap] at hh
  exact hh

def parent_wrapFirstPortColumns : ((i : Fin (arity q)) × Fin (D.childDim q i)) ≃
    ((C).vertexRanks (nn).1).Columns (nn).2 :=
  (w.parent_mirrorFirstColumns).trans
    (Equiv.sigmaCongr (Equiv.refl _) (fun c => finCongr
      (congrArg (fun d => d.rank ((w.shape.atomicBand.kind 0).mirrorPort
        (w.shape.atomicBand.kind 0).input) (some c)) (D.namedCut_mirror_localRanks q w 0))))
def parent_wrapFirstPortParent : Fin (D.rank (D.ports.facet ⟨q,none⟩)) ≃
    ((C).vertexRanks (nn).1).Parent (nn).2 :=
  (w.parent_mirrorFirstParent).trans
    (finCongr (congrArg (fun d => d.rank ((w.shape.atomicBand.kind 0).mirrorPort
      (w.shape.atomicBand.kind 0).input) none) (D.namedCut_mirror_localRanks q w 0)))
lemma parent_wrapFirstPortFrame (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    ((D.namedCutPortFrames q w old T nn).reindex
      (D.parent_wrapFirstPortColumns q w) (D.parent_wrapFirstPortParent q w)).linearEquiv =
      w.firstFrame.trans T.linearEquiv.symm := by
  have hh := LocalRanks.external_transportFrames_reindex_extra
    (D.namedCut_mirror_localRanks q w 0) (w.mirrorVertexFrames T 0)
    ((w.shape.atomicBand.kind 0).mirrorPort (w.shape.atomicBand.kind 0).input)
    (w.parent_mirrorFirstColumns) (w.parent_mirrorFirstParent)
  exact (congrArg MatrixIso.linearEquiv hh).trans (w.parent_mirrorFirstFrame T)

def parent_wrapLastPortColumns : ((i : Fin (arity q)) × Fin (D.childDim q i)) ≃
    ((C).vertexRanks (pp).1).Columns (pp).2 :=
  (w.parent_mirrorLastColumns).trans
    (Equiv.sigmaCongr (Equiv.refl _) (fun c => finCongr
      (congrArg (fun d => d.rank ((w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).mirrorPort
        (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output) (some c)) (D.namedCut_mirror_localRanks q w (Fin.last w.shape.atomicBand.length)))))
def parent_wrapLastPortParent : Fin (D.rank (D.ports.facet ⟨q,none⟩)) ≃
    ((C).vertexRanks (pp).1).Parent (pp).2 :=
  (w.parent_mirrorLastParent).trans
    (finCongr (congrArg (fun d => d.rank ((w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).mirrorPort
      (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output) none) (D.namedCut_mirror_localRanks q w (Fin.last w.shape.atomicBand.length))))
lemma parent_wrapLastPortFrame (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    ((D.namedCutPortFrames q w old T pp).reindex
      (D.parent_wrapLastPortColumns q w) (D.parent_wrapLastPortParent q w)).linearEquiv =
      w.lastFrame.trans T.linearEquiv.symm := by
  have hh := LocalRanks.external_transportFrames_reindex_extra
    (D.namedCut_mirror_localRanks q w (Fin.last w.shape.atomicBand.length)) (w.mirrorVertexFrames T (Fin.last w.shape.atomicBand.length))
    ((w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).mirrorPort (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output)
    (w.parent_mirrorLastColumns) (w.parent_mirrorLastParent)
  exact (congrArg MatrixIso.linearEquiv hh).trans (w.parent_mirrorLastFrame T)

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_wrapFirstPortFrame
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.parent_wrapLastPortFrame
