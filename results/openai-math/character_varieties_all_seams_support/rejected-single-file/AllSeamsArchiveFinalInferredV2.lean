import OAI.AlgebraicGeometry.CharacterVarieties.Seams.ProducedEquations


/- Local proof module: SeamCases -/
section

set_option maxHeartbeats 0

namespace OAI

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K] [Algebra R K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (hproper : D.Proper) (hmax : ∀ f, D.rank f ≤ D.rank (D.ports.facet ⟨q,none⟩))
    (hg : 0 < D.genus (D.bandCutParent q))
    (P : D.Punctures R) (x : D.Solution P K)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))

theorem external_graftPlus_cases
    {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
    (Q : (BandGraft.wiring A q B).Seam → Prop)
    (old : ∀ s, s ≠ q → Q (graftPlus A B.doublePatch (.inl s)))
    (selected : Q (graftPlus A B.doublePatch (.inl q)))
    (original : ∀ j, Q (graftPlus A B.doublePatch (.inr (.inl (.inl (.inl j))))))
    (mirror : ∀ j, Q (graftPlus A B.doublePatch (.inr (.inl (.inl (.inr j))))))
    (transversePlus : ∀ a, Q (graftPlus A B.doublePatch (.inr (.inl (.inr (.inl a))))))
    (transverseMinus : ∀ b, Q (graftPlus A B.doublePatch (.inr (.inl (.inr (.inr b))))))
    (first : Q (graftPlus A B.doublePatch (.inr (.inr false))))
    (wrap : Q (graftPlus A B.doublePatch (.inr (.inr true)))) : ∀ s, Q s := by
  intro s
  obtain ⟨z,rfl⟩ := (graftPlus A B.doublePatch).surjective s
  rcases z with s|((j|j)|(a|b))|b
  · by_cases hs : s=q
    · subst s
      exact selected
    · exact old s hs
  · exact original j
  · exact mirror j
  · exact transversePlus a
  · exact transverseMinus b
  · cases b
    · exact first
    · exact wrap

end IntegralCharacterVarieties.SurfacePresentation.Diagram
end
end OAI
end


/- Local proof module: AllSeamsFromBranchesInferredV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option quotPrecheck false
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K] [Algebra R K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (hg : 0<D.genus (D.bandCutParent q))
    (P : D.Punctures R) (x : D.Solution P K)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
local notation "w" => D.producedCutBand q hg P x b0 i0
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q (w).shape)
local notation "B" => D.ports.refinedBandForSeam q (w).shape
local notation "C" => D.producedMarkedDiagram q hproper hmax hg P x b0 i0
local notation "v" => D.producedMarkedValues q hproper hmax hg P x b0 i0
local notation "ss" => BandGraft.originalPort A q B 0 true
local notation "CC" => D.refinedCutDiagram q (w).shape rfl (w).rowRanks (w).colRanks
local notation "cv" => D.external_markedAsCutValues q (w).shape rfl (w).rowRanks (w).colRanks hproper hmax v
local notation "Q" => (fun s => SameFramedFlag ((C).seamGrade s)
  (matrixUnitEquiv (((C).seamLeft s).eval (algebraMap R K) v))
  (matrixUnitEquiv (((C).seamRight s).eval (algebraMap R K) v)))
local notation "g" => D.producedCutSeed q hg P x b0

def external_allSeamsFromBranches :=
  external_graftPlus_cases A q B Q
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: FrameIndexBridge -/
section

namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity)

def external_portColumns (p : LocalPort V D.ports.kind) :
    (D.vertexRanks p.1).Columns p.2 ≃
      ((i : Fin (arity (D.ports.attach p).1)) × Fin (D.childDim (D.ports.attach p).1 i)) :=
  Equiv.sigmaCongr (D.ports.childEquiv p) (fun _ => Equiv.refl _)

lemma external_namedFrame_port
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (p : LocalPort V D.ports.kind) :
    D.namedSeamFrame (D.ports.attach p).1
        (g (.frame (D.ports.attach p).1 (D.ports.attach p).2)) =
      ((D.portFrame g p).reindex (D.external_portColumns p).symm (Equiv.refl _)).linearEquiv := by
  unfold namedSeamFrame portFrame
  erw [MatrixIso.reindex_reindex_eq]
  have he : (D.external_portColumns p).symm.trans (D.portColumnIndex p) =
      (blockIndex (D.childDim (D.ports.attach p).1)).symm := by
    change (D.external_portColumns p).symm.trans
      ((D.external_portColumns p).trans (blockIndex (D.childDim (D.ports.attach p).1)).symm) = _
    ext i
    exact congrArg (fun z => ((blockIndex (D.childDim (D.ports.attach p).1)).symm z).val)
      ((D.external_portColumns p).apply_symm_apply i)
  erw [he]
  rfl

lemma external_namedFrame_valuesFromPorts
    (frames : D.PortFrames (R:=K)) (side : D.SideValues (R:=K))
    (handle : D.HandleValues (R:=K)) (p : LocalPort V D.ports.kind) :
    D.namedSeamFrame (D.ports.attach p).1
      ((D.valuesFromPorts frames side handle)
        (.frame (D.ports.attach p).1 (D.ports.attach p).2)) =
      ((frames p).reindex (D.external_portColumns p).symm (Equiv.refl _)).linearEquiv := by
  rw [external_namedFrame_port, portFrame_valuesFromPorts]

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace OAI.IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
noncomputable section
open scoped Classical
variable {R : Type} [CommRing R] {k : Kind} {d e : LocalRanks k}

lemma external_transportFrames_eq_reindex (h : d=e)
    (f : (p : k.table.Port) → MatrixIso R (d.Columns p) (d.Parent p))
    (p : k.table.Port) :
    transportFrames h f p = (f p).reindex
      (Equiv.sigmaCongr (Equiv.refl _) (fun c =>
        finCongr (congrArg (fun z : LocalRanks k => z.rank p (some c)) h.symm)))
      (finCongr (congrArg (fun z : LocalRanks k => z.rank p none) h.symm)) := by
  subst e
  have ec : (Equiv.sigmaCongr (Equiv.refl (k.table.Child p)) (fun c =>
      finCongr (congrArg (fun z : LocalRanks k => z.rank p (some c)) (rfl : d=d)))) =
      Equiv.refl (d.Columns p) := by
    apply Equiv.ext
    rintro ⟨c,i⟩
    rfl
  change f p = (f p).reindex _ (Equiv.refl _)
  erw [ec]
  exact (MatrixIso.reindex_refl_eq _).symm

lemma external_transportFrames_reindex (h : d=e)
    (f : (p : k.table.Port) → MatrixIso R (d.Columns p) (d.Parent p))
    (p : k.table.Port) :
    ((transportFrames h f p).reindex
      (Equiv.sigmaCongr (Equiv.refl _) (fun c =>
        finCongr (congrArg (fun z : LocalRanks k => z.rank p (some c)) h)))
      (finCongr (congrArg (fun z : LocalRanks k => z.rank p none) h))) = f p := by
  subst e
  have ec : (Equiv.sigmaCongr (Equiv.refl (k.table.Child p)) (fun c =>
      finCongr (congrArg (fun z : LocalRanks k => z.rank p (some c)) (rfl : d=d)))) =
      Equiv.refl (d.Columns p) := by
    apply Equiv.ext
    rintro ⟨c,i⟩
    rfl
  change (f p).reindex _ (Equiv.refl _) = f p
  erw [ec]
  exact MatrixIso.reindex_refl_eq _

end
end OAI.IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
end


/- Local proof module: NamedFramePortAt -/
section

namespace OAI.IntegralCharacterVarieties.MatrixIso
noncomputable section
open scoped Classical Matrix
variable {R α β : Type*} [CommRing R] [Fintype α] [Fintype β]
lemma external_ofLinearEquiv_linearEquiv (x : MatrixIso R α β) :
    MatrixIso.ofLinearEquiv x.linearEquiv=x := by
  apply MatrixIso.ext
  · exact LinearMap.toMatrix'.apply_symm_apply _
  · have he : x.linearEquiv.symm.toLinearMap = Matrix.toLin' x.inv := by rfl
    change LinearMap.toMatrix' x.linearEquiv.symm.toLinearMap = x.inv
    rw [he]
    exact LinearMap.toMatrix'.apply_symm_apply _
end
end OAI.IntegralCharacterVarieties.MatrixIso

namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity)

def external_seamColumnsTransport {s t : S} (he : s=t) :
    ((i : Fin (arity s)) × Fin (D.childDim s i)) ≃
      ((i : Fin (arity t)) × Fin (D.childDim t i)) :=
  Equiv.sigmaCongr (finCongr (congrArg arity he)) (fun i =>
    finCongr (by subst t; rfl))

lemma external_seamColumnsTransport_grade {s t : S} (he : s=t)
    (i : (j : Fin (arity s)) × Fin (D.childDim s j)) :
    (D.external_seamColumnsTransport he i).1.val=i.1.val := rfl

lemma external_namedFrame_transport {s t : S} (he : s=t)
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (b : Bool) :
    ((MatrixIso.ofLinearEquiv (D.namedSeamFrame s (g (.frame s b)))).reindex
      (D.external_seamColumnsTransport he).symm
      (finCongr (congrArg (fun z => D.rank (D.ports.facet ⟨z,none⟩)) he)).symm).linearEquiv =
      D.namedSeamFrame t (g (.frame t b)) := by
  subst t
  have ec : (D.external_seamColumnsTransport (rfl : s=s)).symm = Equiv.refl _ := by
    apply Equiv.ext
    rintro ⟨i,j⟩
    rfl
  have ep : (finCongr (congrArg (fun z => D.rank (D.ports.facet ⟨z,none⟩)) (rfl : s=s))).symm = Equiv.refl _ := by
    apply Equiv.ext
    intro i
    rfl
  erw [ec,ep,MatrixIso.reindex_refl_eq,MatrixIso.linearEquiv_ofLinearEquiv]


lemma external_namedFrame_port_at
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (p : LocalPort V D.ports.kind) (s : S) (b : Bool) (hp : D.ports.attach p=(s,b)) :
    (((D.portFrame g p).reindex (D.external_portColumns p).symm (Equiv.refl _)).reindex
      (D.external_seamColumnsTransport (congrArg Prod.fst hp)).symm
      (finCongr (congrArg (fun z => D.rank (D.ports.facet ⟨z,none⟩)) (congrArg Prod.fst hp))).symm).linearEquiv =
      D.namedSeamFrame s (g (.frame s b)) := by
  have hb : b=(D.ports.attach p).2 := (congrArg Prod.snd hp).symm
  subst b
  have hs : s=(D.ports.attach p).1 := (congrArg Prod.fst hp).symm
  subst s
  have h := D.external_namedFrame_port g p
  have hh := D.external_namedFrame_transport (rfl : (D.ports.attach p).1=(D.ports.attach p).1) g (D.ports.attach p).2
  have he : MatrixIso.ofLinearEquiv
      (D.namedSeamFrame (D.ports.attach p).1 (g (.frame (D.ports.attach p).1 (D.ports.attach p).2))) =
      (D.portFrame g p).reindex (D.external_portColumns p).symm (Equiv.refl _) := by
    rw [h]
    exact MatrixIso.external_ofLinearEquiv_linearEquiv _
  rw [he] at hh
  exact hh

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: NamedEndpointFlag -/
section

namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity)

def external_endpointNamedMatrix (frames : D.PortFrames (R:=K))
    (p : LocalPort V D.ports.kind) (s : S) (b : Bool) (hp : D.ports.attach p=(s,b)) :=
  ((frames p).reindex (D.external_portColumns p).symm (Equiv.refl _)).reindex
    (D.external_seamColumnsTransport (congrArg Prod.fst hp)).symm
    (finCongr (congrArg (fun z => D.rank (D.ports.facet ⟨z,none⟩)) (congrArg Prod.fst hp))).symm

lemma external_endpointNamedMatrix_eq
    (frames : D.PortFrames (R:=K)) (side : D.SideValues (R:=K))
    (handle : D.HandleValues (R:=K))
    (p : LocalPort V D.ports.kind) (s : S) (b : Bool) (hp : D.ports.attach p=(s,b)) :
    (D.external_endpointNamedMatrix frames p s b hp).linearEquiv =
      D.namedSeamFrame s ((D.valuesFromPorts frames side handle) (.frame s b)) := by
  have h := D.external_namedFrame_port_at (D.valuesFromPorts frames side handle) p s b hp
  rw [D.portFrame_valuesFromPorts] at h
  exact h

lemma external_endpointFlag
    (frames : D.PortFrames (R:=K)) (side : D.SideValues (R:=K))
    (handle : D.HandleValues (R:=K)) (s : S)
    (p n : LocalPort V D.ports.kind) (hp : D.ports.attach p=(s,true))
    (hn : D.ports.attach n=(s,false))
    {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ ((i : Fin (arity s)) × Fin (D.childDim s i)))
    (f : β ≃ Fin (D.rank (D.ports.facet ⟨s,none⟩)))
    (h : SameFramedFlag (fun i => (e i).1.val)
      ((D.external_endpointNamedMatrix frames n s false hn).reindex e f).linearEquiv
      ((D.external_endpointNamedMatrix frames p s true hp).reindex e f).linearEquiv) :
    SameFramedFlag (fun i : (j : Fin (arity s)) × Fin (D.childDim s j) => i.1.val)
      (D.namedSeamFrame s ((D.valuesFromPorts frames side handle) (.frame s false)))
      (D.namedSeamFrame s ((D.valuesFromPorts frames side handle) (.frame s true))) := by
  have hh := (MatrixIso.sameFramedFlag_reindex_iff (fun i => i.1.val)
    (D.external_endpointNamedMatrix frames n s false hn)
    (D.external_endpointNamedMatrix frames p s true hp) e f).mp h
  erw [D.external_endpointNamedMatrix_eq frames side handle n s false hn,
    D.external_endpointNamedMatrix_eq frames side handle p s true hp] at hh
  exact hh

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: NamedEndpointCancel -/
section

namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity)

lemma external_endpointNamedMatrix_reindex_cancel
    (frames : D.PortFrames (R:=K))
    (p : LocalPort V D.ports.kind) (s : S) (b : Bool)
    (hp : D.ports.attach p=(s,b))
    {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ ((i : Fin (arity (D.ports.attach p).1)) ×
      Fin (D.childDim (D.ports.attach p).1 i)))
    (f : β ≃ Fin (D.rank (D.ports.facet ⟨(D.ports.attach p).1,none⟩))) :
    (D.external_endpointNamedMatrix frames p s b hp).reindex
      (e.trans (D.external_seamColumnsTransport (congrArg Prod.fst hp)))
      (f.trans (finCongr (congrArg (fun z => D.rank (D.ports.facet ⟨z,none⟩))
        (congrArg Prod.fst hp)))) =
      ((frames p).reindex (D.external_portColumns p).symm (Equiv.refl _)).reindex e f := by
  unfold external_endpointNamedMatrix
  erw [MatrixIso.reindex_reindex_eq]

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: SigmaFinCoordinates -/
section

namespace OAI.IntegralCharacterVarieties
noncomputable section
open scoped Classical

lemma external_sigmaFinCongr_snd {α β : Type*} (e : α ≃ β)
    (d : α → ℕ) (f : β → ℕ) (h : ∀ a, d a = f (e a))
    (i : (a : α) × Fin (d a)) :
    (((Equiv.sigmaCongr e (fun a => finCongr (h a)) : ((a : α) × Fin (d a)) ≃ ((b : β) × Fin (f b)))) i).2.val = i.2.val := rfl

lemma external_sigmaFinCongr_symm_snd {α β : Type*} (e : α ≃ β)
    (d : α → ℕ) (f : β → ℕ) (h : ∀ a, d a = f (e a))
    (i : (b : β) × Fin (f b)) :
    (((Equiv.sigmaCongr e (fun a => finCongr (h a)) : ((a : α) × Fin (d a)) ≃ ((b : β) × Fin (f b)))).symm i).2.val = i.2.val := by
  obtain ⟨j, rfl⟩ := ((Equiv.sigmaCongr e (fun a => finCongr (h a)) : ((a : α) × Fin (d a)) ≃ ((b : β) × Fin (f b)))).surjective i
  rw [Equiv.symm_apply_apply]
  rfl

end
end OAI.IntegralCharacterVarieties

namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity)

lemma external_seamColumnsTransport_snd {s t : S} (he : s=t)
    (i : (j : Fin (arity s)) × Fin (D.childDim s j)) :
    (D.external_seamColumnsTransport he i).2.val = i.2.val := rfl

lemma external_portColumns_snd (p : LocalPort V D.ports.kind)
    (i : (D.vertexRanks p.1).Columns p.2) :
    (D.external_portColumns p i).2.val = i.2.val := rfl

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: MatrixReindexCancel -/
section
namespace OAI.IntegralCharacterVarieties.MatrixIso
noncomputable section
open scoped Classical Matrix
variable {R α β γ δ ε : Type*} [CommRing R]
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ε]

lemma external_reindex_column_cancel (x : MatrixIso R α β)
    (a : α ≃ γ) (b : α ≃ δ) (f : ε ≃ β) :
    (x.reindex a.symm (Equiv.refl β)).reindex (b.symm.trans a) f =
      x.reindex b.symm f := by
  rw [reindex_reindex_eq]
  have he : (b.symm.trans a).trans a.symm=b.symm := by
    apply Equiv.ext
    intro i
    exact a.symm_apply_apply _
  rw [he]
  rfl

end
end OAI.IntegralCharacterVarieties.MatrixIso
end


/- Local proof module: EndpointNormalization -/
section
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity)

lemma external_endpointNamedMatrix_normalized
    (frames : D.PortFrames (R:=K)) (p : LocalPort V D.ports.kind)
    (s : S) (b : Bool) (hp : D.ports.attach p=(s,b))
    {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ (D.vertexRanks p.1).Columns p.2)
    (f : β ≃ (D.vertexRanks p.1).Parent p.2) :
    (D.external_endpointNamedMatrix frames p s b hp).reindex
      ((e.trans (D.external_portColumns p)).trans
        (D.external_seamColumnsTransport (congrArg Prod.fst hp)))
      (f.trans (finCongr (congrArg (fun z => D.rank (D.ports.facet ⟨z,none⟩))
        (congrArg Prod.fst hp)))) = (frames p).reindex e f := by
  erw [D.external_endpointNamedMatrix_reindex_cancel]
  erw [MatrixIso.reindex_reindex_eq]
  have he : (e.trans (D.external_portColumns p)).trans
      (D.external_portColumns p).symm=e := by
    apply Equiv.ext
    intro i
    exact (D.external_portColumns p).symm_apply_apply _
  erw [he]
  rfl

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: TransportedFrameNamed -/
section
namespace OAI.IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
noncomputable section
open scoped Classical Matrix
variable {R : Type} [CommRing R] {k : Kind} {d e : LocalRanks k}

lemma external_transportFrames_reindex_extra (h : d=e)
    (f : (p : k.table.Port) → MatrixIso R (d.Columns p) (d.Parent p))
    (p : k.table.Port) {α β : Type*} [Fintype α] [Fintype β]
    (a : α ≃ d.Columns p) (b : β ≃ d.Parent p) :
    (transportFrames h f p).reindex
      (a.trans (Equiv.sigmaCongr (Equiv.refl _) (fun c =>
        finCongr (congrArg (fun z : LocalRanks k => z.rank p (some c)) h))))
      (b.trans (finCongr (congrArg (fun z : LocalRanks k => z.rank p none) h))) =
      (f p).reindex a b := by
  have hh := external_transportFrames_reindex h f p
  have hh' := congrArg (fun u => u.reindex a b) hh
  rw [MatrixIso.reindex_reindex_eq] at hh'
  exact hh'

end
end OAI.IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
end


/- Local proof module: ParentSelectedOldPort -/
section
set_option quotPrecheck false
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
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "s0" => BandGraft.originalPort A q B 0 true
variable (s : S) (b : Bool)
local notation "pold" => (Subtype.val (D.ports.portAt b s))
local notation "pn" => (Subtype.val (BandGraft.oldPort A q B s b))

lemma external_oldEndpointChildRank
    (c : (D.ports.kind (pold).1).table.Child (pold).2) :
    ((C).vertexRanks (pn).1).rank (pn).2 (some c) =
      D.childDim s ((finCongr (congrArg (fun e => arity e.1)
        (D.ports.attach_portAt s b))) (D.ports.childEquiv pold c)) := by
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
  exact aux (congrArg Prod.fst (D.ports.attach_portAt s b)) _


def external_oldEndpointChild := (D.ports.childEquiv pold).trans
  (finCongr (congrArg (fun e => arity e.1) (D.ports.attach_portAt s b)))

def external_oldEndpointPortColumns :
    ((C).vertexRanks (pn).1).Columns (pn).2 ≃ ((i : Fin (arity s)) × Fin (D.childDim s i)) :=
  Equiv.sigmaCongr (D.external_oldEndpointChild s b) (fun c =>
    finCongr (D.external_oldEndpointChildRank q w s b c))

def external_oldEndpointNamedColumns :=
  (D.external_oldEndpointPortColumns q w s b).symm.trans ((C).external_portColumns pn)

lemma external_oldEndpointNamedColumns_grade
    (i : (j : Fin (arity s)) × Fin (D.childDim s j)) :
    (D.external_oldEndpointNamedColumns q w s b i).1.val = i.1.val := by
  change ((D.external_oldEndpointChild s b)
    ((D.external_oldEndpointChild s b).symm i.1)).val = i.1.val
  rw [Equiv.apply_symm_apply]


lemma external_oldEndpointPortFrame_eq
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    ((D.namedCutPortFrames q w (D.portFrame g) T pn).reindex
      (D.external_oldEndpointPortColumns q w s b).symm
      (finCongr (show ((C).vertexRanks (pn).1).rank (pn).2 none = D.rank (D.ports.facet ⟨s,none⟩) from by
        have hh := congrArg (fun d => d.rank (pold).2 none)
          (D.refinedCut_old_vertexRanks q w.shape rfl w.rowRanks w.colRanks (pold).1)
        exact hh.trans (congrArg (fun e : S × Bool => D.rank (D.ports.facet ⟨e.1,none⟩))
          (D.ports.attach_portAt s b)))).symm).linearEquiv =
      D.namedSeamFrame s (g (.frame s b)) := by
  have hh := LocalRanks.external_transportFrames_reindex
    (D.refinedCut_old_vertexRanks q w.shape rfl w.rowRanks w.colRanks (pold).1).symm
    (fun z => D.portFrame g ⟨(pold).1,z⟩) (pold).2
  have ho := D.external_namedFrame_port_at g pold s b (D.ports.attach_portAt s b)
  have hh2 := congrArg (fun u => ((u.reindex (D.external_portColumns pold).symm (Equiv.refl _)).reindex
    (D.external_seamColumnsTransport (congrArg Prod.fst (D.ports.attach_portAt s b))).symm
    (finCongr (congrArg (fun z => D.rank (D.ports.facet ⟨z,none⟩))
      (congrArg Prod.fst (D.ports.attach_portAt s b)))).symm).linearEquiv) hh
  have ec : (((D.external_seamColumnsTransport (congrArg Prod.fst (D.ports.attach_portAt s b))).symm.trans
      (D.external_portColumns pold).symm).trans
      (Equiv.sigmaCongr (Equiv.refl ((D.ports.kind (pold).1).table.Child (pold).2)) (fun c =>
        finCongr (congrArg (fun d => d.rank (pold).2 (some c))
          (D.refinedCut_old_vertexRanks q w.shape rfl w.rowRanks w.colRanks (pold).1).symm)))) =
      (D.external_oldEndpointPortColumns q w s b).symm := by
    have aux {α β : Type} (e f : α ≃ β) (h : e.symm=f.symm) : e=f := by
      have hh := congrArg Equiv.symm h
      exact hh
    apply aux
    apply Equiv.ext
    intro i
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Fin.ext
      rfl
  erw [MatrixIso.reindex_reindex_eq,MatrixIso.reindex_reindex_eq] at hh2
  have hfinal := hh2.trans ho
  convert hfinal using 1
  · congr 2
    exact ec.symm

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: OldEndpointAssemblyShared -/
section
set_option autoImplicit false
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
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "B" => D.ports.refinedBandForSeam q w.shape
variable (s : S) (b : Bool)
local notation "pold" => (Subtype.val (D.ports.portAt b s))
local notation "pn" => (Subtype.val (BandGraft.oldPort A q B s b))
lemma external_oldEndpointPortParentRank :
    ((C).vertexRanks (pn).1).rank (pn).2 none = D.rank (D.ports.facet ⟨s,none⟩) := by
  have hh := congrArg (fun d => d.rank (pold).2 none)
    (D.refinedCut_old_vertexRanks q w.shape rfl w.rowRanks w.colRanks (pold).1)
  exact hh.trans (congrArg (fun e : S × Bool => D.rank (D.ports.facet ⟨e.1,none⟩))
    (D.ports.attach_portAt s b))


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
variable (s : S) (hs : s≠q)
local notation "ss" => BandGraft.oldPort A q B s true
local notation "pp" => (Subtype.val (BandGraft.oldPort A q B s true))
local notation "nn" => (Subtype.val (BandGraft.oldPort A q B s false))

lemma external_oldPositiveAttach : (C).ports.attach pp=(ss,true) := by
  exact (BandGraft.wiring A q B).endOf_portAt (ss,true)

lemma external_oldNegativeAttach (hs : s≠q) : (C).ports.attach nn=(ss,false) := by
  have hh := (BandGraft.wiring A q B).endOf_portAt (ss,false)
  change (BandGraft.wiring A q B).endOf ((BandGraft.wiring A q B).wire ss).val = _ at hh
  erw [BandGraft.wire_old A q B s hs] at hh
  exact hh

lemma external_oldEndpointNamedColumns_snd (b : Bool)
    (i : (j : Fin (arity s)) × Fin (D.childDim s j)) :
    (D.external_oldEndpointNamedColumns q w s b i).2.val = i.2.val := by
  unfold external_oldEndpointNamedColumns
  change ((C).external_portColumns
    (Subtype.val (BandGraft.oldPort A q B s b))
    ((D.external_oldEndpointPortColumns q w s b).symm i)).2.val = _
  rw [(C).external_portColumns_snd]
  exact external_sigmaFinCongr_symm_snd (D.external_oldEndpointChild s b)
    (fun c => ((C).vertexRanks (.inl (Subtype.val (D.ports.portAt b s)).1)).rank
      (Subtype.val (D.ports.portAt b s)).2 (some c))
    (D.childDim s) (D.external_oldEndpointChildRank q w s b) i

def external_oldCommonColumns := (D.external_oldEndpointNamedColumns q w s false).trans
  ((C).external_seamColumnsTransport (congrArg Prod.fst (D.external_oldNegativeAttach q w s hs)))

def external_oldCommonParent :=
  (finCongr (D.external_oldEndpointPortParentRank q w s false)).symm.trans
    (finCongr (congrArg (fun z => (C).rank ((C).ports.facet ⟨z,none⟩))
      (congrArg Prod.fst (D.external_oldNegativeAttach q w s hs))))

lemma external_oldCommonColumns_grade
    (i : (j : Fin (arity s)) × Fin (D.childDim s j)) :
    (D.external_oldCommonColumns q w s hs i).1.val = i.1.val := by
  exact D.external_oldEndpointNamedColumns_grade q w s false i

lemma external_oldCommonColumns_positive :
    D.external_oldCommonColumns q w s hs =
      (D.external_oldEndpointNamedColumns q w s true).trans
        ((C).external_seamColumnsTransport
          (congrArg Prod.fst (D.external_oldPositiveAttach q w s))) := by
  apply Equiv.ext
  intro i
  have hp := D.external_oldEndpointNamedColumns_grade q w s true i
  have hn := D.external_oldCommonColumns_grade q w s hs i
  have he : (D.external_oldCommonColumns q w s hs i).1 =
      (((D.external_oldEndpointNamedColumns q w s true).trans
        ((C).external_seamColumnsTransport
          (congrArg Prod.fst (D.external_oldPositiveAttach q w s)))) i).1 := by
    apply Fin.ext
    exact hn.trans hp.symm
  apply Sigma.ext he
  apply (Fin.heq_ext_iff (congrArg ((C).childDim ss) he)).2
  have hp2 := D.external_oldEndpointNamedColumns_snd q w s true i
  have hn2 := D.external_oldEndpointNamedColumns_snd q w s false i
  have hpt := (C).external_seamColumnsTransport_snd
    (congrArg Prod.fst (D.external_oldPositiveAttach q w s))
    (D.external_oldEndpointNamedColumns q w s true i)
  have hnt := (C).external_seamColumnsTransport_snd
    (congrArg Prod.fst (D.external_oldNegativeAttach q w s hs))
      (D.external_oldEndpointNamedColumns q w s false i)
  exact (hnt.trans hn2).trans (hpt.trans hp2).symm

lemma external_oldNegativeEndpoint_eq
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    (((C).external_endpointNamedMatrix (D.namedCutPortFrames q w (D.portFrame g) T)
      nn ss false (D.external_oldNegativeAttach q w s hs)).reindex
      (D.external_oldCommonColumns q w s hs) (D.external_oldCommonParent q w s hs)).linearEquiv =
        D.namedSeamFrame s (g (.frame s false)) := by
  have hh := (C).external_endpointNamedMatrix_normalized
    (D.namedCutPortFrames q w (D.portFrame g) T) nn ss false
    (D.external_oldNegativeAttach q w s hs) (D.external_oldEndpointPortColumns q w s false).symm
    (finCongr (D.external_oldEndpointPortParentRank q w s false)).symm
  exact (congrArg MatrixIso.linearEquiv hh).trans (D.external_oldEndpointPortFrame_eq q w s false g T)

lemma external_oldPositiveEndpoint_eq
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    (((C).external_endpointNamedMatrix (D.namedCutPortFrames q w (D.portFrame g) T)
      pp ss true (D.external_oldPositiveAttach q w s)).reindex
      (D.external_oldCommonColumns q w s hs) (D.external_oldCommonParent q w s hs)).linearEquiv =
        D.namedSeamFrame s (g (.frame s true)) := by
  have hp : D.external_oldCommonParent q w s hs =
      (finCongr (D.external_oldEndpointPortParentRank q w s true)).symm.trans
        (finCongr (congrArg (fun z => (C).rank ((C).ports.facet ⟨z,none⟩))
          (congrArg Prod.fst (D.external_oldPositiveAttach q w s)))) := by
    apply Equiv.ext
    intro i
    rfl
  have hh := (C).external_endpointNamedMatrix_normalized
    (D.namedCutPortFrames q w (D.portFrame g) T) pp ss true
    (D.external_oldPositiveAttach q w s) (D.external_oldEndpointPortColumns q w s true).symm
    (finCongr (D.external_oldEndpointPortParentRank q w s true)).symm
  have hc := D.external_oldCommonColumns_positive q w s hs
  have h1 := congrArg MatrixIso.linearEquiv hh
  erw [← hc,← hp] at h1
  exact h1.trans (D.external_oldEndpointPortFrame_eq q w s true g T)

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram

end


/- Local proof module: ParentSelectedSideTransport -/
section
set_option maxHeartbeats 0
set_option quotPrecheck false
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {r : ℕ} (d : TwoFlagBand.RankShape (arity q) (arity q) r)
    (hp : D.rank (D.ports.facet ⟨q,none⟩)=r)
    (hc : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.row i))
    (hc' : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.col i))
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q d)
local notation "B" => D.ports.refinedBandForSeam q d
local notation "C" => D.refinedCutDiagram q d hp hc hc'
variable (s : S)
local notation "ss" => BandGraft.oldPort A q B s true

lemma external_oldSideArity : (BandGraft.wiring A q B).seamArity ss = arity s :=
  (A).portAt_arity s true

lemma external_oldSideRank (i : Option (Fin (arity s))) :
    (C).rank ((C).ports.facet ⟨ss,i.map (finCongr (D.external_oldSideArity q d s).symm)⟩) =
      D.rank (D.ports.facet ⟨s,i⟩) := by
  exact congrArg (D.ports.refinedRank q d D.rank)
    (graft_old_color A (B).doublePatch (doubleDecoration (B).decoration) q
      ((B).patch.double_signatureMatch (B).decoration (B).patch_signatureMatch (B).shortFirst (B).shortLast)
      (fun i => by rw [(B).double_signature_plus]; cases i <;> rfl)
      (fun i => by rw [(B).double_signature_minus]; cases i <;> rfl) s i)

lemma external_oldSideValue
    (old : D.SideValues (R:=K))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
    (i : Option (Fin (arity s))) :
    rebaseUnit (D.external_oldSideRank q d hp hc hc' s i)
      (D.refinedCutSideValues q d hp hc hc' old J Y
        ⟨ss,i.map (finCongr (D.external_oldSideArity q d s).symm)⟩) =
      D.cutOldSideValues q old J ⟨s,i⟩ := by
  exact graftSideValues_old A (B).doublePatch (doubleDecoration (B).decoration) q
    ((B).patch.double_signatureMatch (B).decoration (B).patch_signatureMatch (B).shortFirst (B).shortLast)
    (fun i => by rw [(B).double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [(B).double_signature_minus]; cases i <;> rfl)
    (D.ports.refinedRank q d D.rank) (D.cutOldSideValues q old J)
    (D.cutShortSideValues q Y) s i

lemma external_oldSideValue_unselected
    (old : D.SideValues (R:=K))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
    (hs : s≠q) (i : Option (Fin (arity s))) :
    rebaseUnit (D.external_oldSideRank q d hp hc hc' s i)
      (D.refinedCutSideValues q d hp hc hc' old J Y
        ⟨ss,i.map (finCongr (D.external_oldSideArity q d s).symm)⟩) = old ⟨s,i⟩ := by
  rw [D.external_oldSideValue q d hp hc hc' s old J Y i]
  cases i with
  | none => simp only [cutOldSideValues, dif_neg hs]
  | some i => rfl

def external_oldSideColumns : ((i : Fin (arity s)) × Fin (D.childDim s i)) ≃
    ((j : Fin ((BandGraft.wiring A q B).seamArity ss)) × Fin ((C).childDim ss j)) :=
  Equiv.sigmaCongr (finCongr (D.external_oldSideArity q d s).symm)
    (fun i => finCongr (D.external_oldSideRank q d hp hc hc' s (some i)).symm)

def external_oldSideParent := (finCongr (D.external_oldSideRank q d hp hc hc' s none)).symm

lemma external_oldParentTransport
    (old : D.SideValues (R:=K))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
    (hs : s≠q) :
    (MatrixIso.unit (D.refinedCutSideValues q d hp hc hc' old J Y ⟨ss,none⟩)).reindex
      (D.external_oldSideParent q d hp hc hc' s)
      (D.external_oldSideParent q d hp hc hc' s) = MatrixIso.unit (old ⟨s,none⟩) := by
  have h := D.external_oldSideValue_unselected q d hp hc hc' s old J Y hs none
  have hi := rebaseUnit_iso (D.external_oldSideRank q d hp hc hc' s none)
    (D.refinedCutSideValues q d hp hc hc' old J Y ⟨ss,none⟩)
  erw [h] at hi
  exact hi.symm

lemma external_oldChildInverseTransport
    (old : D.SideValues (R:=K))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ) :
    (MatrixIso.block (fun j : Fin ((BandGraft.wiring A q B).seamArity ss) =>
      MatrixIso.unit (D.refinedCutSideValues q d hp hc hc' old J Y ⟨ss,some j⟩)⁻¹)).reindex
      (D.external_oldSideColumns q d hp hc hc' s)
      (D.external_oldSideColumns q d hp hc hc' s) =
      MatrixIso.block (fun i : Fin (arity s) => MatrixIso.unit (old ⟨s,some i⟩)⁻¹) := by
  erw [MatrixIso.block_reindex_sigma]
  congr 1
  funext i
  have h := D.external_oldSideValue q d hp hc hc' s old J Y (some i)
  have hi := rebaseUnit_iso (D.external_oldSideRank q d hp hc hc' s (some i))
    ((D.refinedCutSideValues q d hp hc hc' old J Y
      ⟨ss,some ((finCongr (D.external_oldSideArity q d s).symm) i)⟩)⁻¹)
  erw [map_inv, h] at hi
  exact hi.symm

lemma parent_selectedSideTransport
    (old : D.SideValues (R:=K))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ) :
    (MatrixIso.unit (D.refinedCutSideValues q d hp hc hc' old J Y
      ⟨BandGraft.oldPort A q B q true,none⟩)).reindex
      (D.external_oldSideParent q d hp hc hc' q)
      (D.external_oldSideParent q d hp hc hc' q) = MatrixIso.unit J := by
  have h := D.external_oldSideValue q d hp hc hc' q old J Y none
  rw [D.cutOldSideValues_selected q old J] at h
  have hi := rebaseUnit_iso (D.external_oldSideRank q d hp hc hc' q none)
    (D.refinedCutSideValues q d hp hc hc' old J Y
      ⟨BandGraft.oldPort A q B q true,none⟩)
  erw [h] at hi
  exact hi.symm

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: SeamCoordinateBridge -/
section
set_option maxHeartbeats 0
namespace OAI.IntegralCharacterVarieties.MatrixIso
noncomputable section
open scoped Classical Matrix
variable {K α β γ : Type*} [Field K] [Fintype α] [Fintype β] [Fintype γ]
lemma external_linearEquiv_trans (x : MatrixIso K α β) (y : MatrixIso K β γ) :
    (x.trans y).linearEquiv=x.linearEquiv.trans y.linearEquiv := by
  apply LinearEquiv.ext
  intro v
  exact linearEquiv_trans_apply x y v
end
end OAI.IntegralCharacterVarieties.MatrixIso
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K]
    (D : Diagram F S V arity) (s : S)
    (φ : R →+* K)
    (v : (g : D.Generator) → (Matrix (Fin (D.generatorRank g)) (Fin (D.generatorRank g)) K)ˣ)
lemma external_seam_of_commonCoordinates
    {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ ((i : Fin (arity s)) × Fin (D.childDim s i)))
    (f : β ≃ Fin (D.rank (D.ports.facet ⟨s,none⟩)))
    (h : SameFramedFlag (fun i => (e i).1.val)
      ((((MatrixIso.unit (v (.frame s false))).reindex
        (blockIndex (D.childDim s)).symm (finCongr (D.seamRank s))).reindex e f).linearEquiv.trans
        (((MatrixIso.unit (v (.side ⟨s,none⟩))).reindex f f).linearEquiv))
      ((((MatrixIso.block (fun i : Fin (arity s) =>
        MatrixIso.unit (v (.side ⟨s,some i⟩))⁻¹)).reindex e e).linearEquiv).trans
        ((((MatrixIso.unit (v (.frame s true))).reindex
          (blockIndex (D.childDim s)).symm (finCongr (D.seamRank s))).reindex e f).linearEquiv))) :
    SameFramedFlag (D.seamGrade s)
      (matrixUnitEquiv ((D.seamLeft s).eval φ v))
      (matrixUnitEquiv ((D.seamRight s).eval φ v)) := by
  apply (D.named_seam_iff s φ v).mpr
  have hh := (MatrixIso.sameFramedFlag_reindex_iff (fun i => i.1.val)
    (((MatrixIso.unit (v (.frame s false))).reindex
      (blockIndex (D.childDim s)).symm (finCongr (D.seamRank s))).trans
      (MatrixIso.unit (v (.side ⟨s,none⟩))))
    ((MatrixIso.block (fun i : Fin (arity s) =>
      MatrixIso.unit (v (.side ⟨s,some i⟩))⁻¹)).trans
      ((MatrixIso.unit (v (.frame s true))).reindex
        (blockIndex (D.childDim s)).symm (finCongr (D.seamRank s)))) e f).mp
  have hz := hh (by
    erw [MatrixIso.reindex_trans _ _ e f f, MatrixIso.reindex_trans _ _ e e f,
      MatrixIso.external_linearEquiv_trans, MatrixIso.external_linearEquiv_trans]
    exact h)
  erw [MatrixIso.external_linearEquiv_trans, MatrixIso.external_linearEquiv_trans] at hz
  exact hz
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: NamedEndpointFlagFromFrames -/
section
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity)

lemma external_endpointFlag_of_portFrame
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (frames : D.PortFrames (R:=K)) (he : ∀ p,D.portFrame g p=frames p)
    (s : S) (p n : LocalPort V D.ports.kind)
    (hp : D.ports.attach p=(s,true)) (hn : D.ports.attach n=(s,false))
    {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ ((i : Fin (arity s)) × Fin (D.childDim s i)))
    (f : β ≃ Fin (D.rank (D.ports.facet ⟨s,none⟩)))
    (h : SameFramedFlag (fun i => (e i).1.val)
      ((D.external_endpointNamedMatrix frames n s false hn).reindex e f).linearEquiv
      ((D.external_endpointNamedMatrix frames p s true hp).reindex e f).linearEquiv) :
    SameFramedFlag (fun i : (j : Fin (arity s)) × Fin (D.childDim s j) => i.1.val)
      (D.namedSeamFrame s (g (.frame s false)))
      (D.namedSeamFrame s (g (.frame s true))) := by
  have hh := (MatrixIso.sameFramedFlag_reindex_iff (fun i => i.1.val)
    (D.external_endpointNamedMatrix frames n s false hn)
    (D.external_endpointNamedMatrix frames p s true hp) e f).mp h
  have hn' := D.external_namedFrame_port_at g n s false hn
  have hp' := D.external_namedFrame_port_at g p s true hp
  rw [he n] at hn'
  rw [he p] at hp'
  erw [hn',hp'] at hh
  exact hh

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: EndpointActualMatrix -/
section
set_option maxHeartbeats 0
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity)
lemma external_endpointActualMatrix
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (frames : D.PortFrames (R:=K)) (he : ∀ p,D.portFrame g p=frames p)
    (p : LocalPort V D.ports.kind) (s : S) (b : Bool) (hp : D.ports.attach p=(s,b)) :
    D.external_endpointNamedMatrix frames p s b hp =
      (MatrixIso.unit (g (.frame s b))).reindex
        (blockIndex (D.childDim s)).symm (finCongr (D.seamRank s)) := by
  have hh := D.external_namedFrame_port_at g p s b hp
  rw [he p] at hh
  have hm := congrArg MatrixIso.ofLinearEquiv hh
  erw [MatrixIso.external_ofLinearEquiv_linearEquiv,MatrixIso.external_ofLinearEquiv_linearEquiv] at hm
  exact hm
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: OldSeamFromValuesV2 -/
section
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
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
variable (s : S) (hs : s≠q)
local notation "ss" => BandGraft.oldPort A q B s true
local notation "pp" => Subtype.val (BandGraft.oldPort A q B s true)
local notation "nn" => Subtype.val (BandGraft.oldPort A q B s false)
lemma external_oldSeamFromValues (hs : s≠q)
    {R : Type} [CommRing R] (φ : R →+* K)
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
    (z : (e : (C).Generator) → (Matrix (Fin ((C).generatorRank e)) (Fin ((C).generatorRank e)) K)ˣ)
    (hframes : ∀ p,(C).portFrame z p=D.namedCutPortFrames q w (D.portFrame g) T p)
    (hparent : (MatrixIso.unit (z (.side ⟨ss,none⟩))).reindex
      (D.external_oldSideParent q w.shape rfl w.rowRanks w.colRanks s)
      (D.external_oldSideParent q w.shape rfl w.rowRanks w.colRanks s)=
      MatrixIso.unit (g (.side ⟨s,none⟩)))
    (hchild : (MatrixIso.block (fun ii : Fin ((BandGraft.wiring A q B).seamArity ss) =>
      MatrixIso.unit (z (.side ⟨ss,some ii⟩))⁻¹)).reindex
      (D.external_oldSideColumns q w.shape rfl w.rowRanks w.colRanks s)
      (D.external_oldSideColumns q w.shape rfl w.rowRanks w.colRanks s)=
      MatrixIso.block (fun ii : Fin (arity s) => MatrixIso.unit (g (.side ⟨s,some ii⟩))⁻¹))
    (hold : SameFramedFlag (fun i : (j : Fin (arity s)) × Fin (D.childDim s j) => i.1.val)
      ((D.namedSeamFrame s (g (.frame s false))).trans (D.namedParentLinear s g))
      ((D.namedChildInverse s g).trans (D.namedSeamFrame s (g (.frame s true))))) :
    SameFramedFlag ((C).seamGrade ss)
      (matrixUnitEquiv (((C).seamLeft ss).eval φ z))
      (matrixUnitEquiv (((C).seamRight ss).eval φ z)) := by
  let e := D.external_oldSideColumns q w.shape rfl w.rowRanks w.colRanks s
  let f := D.external_oldSideParent q w.shape rfl w.rowRanks w.colRanks s
  have he : e=D.external_oldCommonColumns q w s hs := by
    apply Equiv.ext
    intro i
    have hgrade := D.external_oldCommonColumns_grade q w s hs i
    have hfst : (e i).1=(D.external_oldCommonColumns q w s hs i).1 := by
      apply Fin.ext
      exact hgrade.symm
    apply Sigma.ext hfst
    apply (Fin.heq_ext_iff (congrArg ((C).childDim ss) hfst)).2
    have h1 := (C).external_seamColumnsTransport_snd
      (congrArg Prod.fst (D.external_oldNegativeAttach q w s hs))
      (D.external_oldEndpointNamedColumns q w s false i)
    have h2 := D.external_oldEndpointNamedColumns_snd q w s false i
    exact (h1.trans h2).symm
  have hf : f=D.external_oldCommonParent q w s hs := by
    apply Equiv.ext
    intro i
    rfl
  have hneg' := D.external_oldNegativeEndpoint_eq q w s hs g T
  have hpos' := D.external_oldPositiveEndpoint_eq q w s hs g T
  have nframe : (((MatrixIso.unit (z (.frame ss false))).reindex
      (blockIndex ((C).childDim ss)).symm (finCongr ((C).seamRank ss))).reindex e f).linearEquiv =
      D.namedSeamFrame s (g (.frame s false)) := by
    rw [← (C).external_endpointActualMatrix z _ hframes nn ss false
      (D.external_oldNegativeAttach q w s hs),he,hf]
    exact hneg'
  have pframe : (((MatrixIso.unit (z (.frame ss true))).reindex
      (blockIndex ((C).childDim ss)).symm (finCongr ((C).seamRank ss))).reindex e f).linearEquiv =
      D.namedSeamFrame s (g (.frame s true)) := by
    rw [← (C).external_endpointActualMatrix z _ hframes pp ss true
      (D.external_oldPositiveAttach q w s),he,hf]
    exact hpos'
  apply (C).external_seam_of_commonCoordinates ss φ z e f
  erw [nframe,pframe,hparent,hchild]
  have hgrade : (fun i => (e i).1.val)=(fun i => i.1.val) := by
    funext i
    rfl
  rw [hgrade]
  exact hold

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram

end


/- Local proof module: ParentMarkedValueDataV2 -/
section
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
end


/- Local proof module: MarkedCutNamedBridge -/
section
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
end


/- Local proof module: ParentMarkedCutLiftData -/
section
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
    (hpMark : D.Proper) (hmaxMark : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (φ : R →+* K)
    (seed : (z : D.Generator) → (Matrix (Fin (D.generatorRank z)) (Fin (D.generatorRank z)) K)ˣ)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
    (t a : (Matrix (Fin (D.rank (D.bandCutParent q)))
      (Fin (D.rank (D.bandCutParent q))) K)ˣ)
    (frames : (D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).PortFrames (R:=K))
local notation "lifted" => D.bandCutLiftGenerators q φ seed b0 t a
local notation "J" => D.bandCutChosenJ q φ lifted b0 i0 a
local notation "T" => D.bandCutChosenT q φ lifted b0 i0 t
local notation "RJ" => rebaseUnit (D.seamRank q).symm J
local notation "RT" => rebaseUnit (D.seamRank q).symm T
lemma parent_markedLiftSide_rebased
    (side : Side (BandGraft.wiring (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q d)) q
      (D.ports.refinedBandForSeam q d)).Seam
      (BandGraft.wiring (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q d)) q
      (D.ports.refinedBandForSeam q d)).seamArity) :
    D.refinedMarkedLiftValues q d hp hc hc' hpMark hmaxMark φ seed b0 i0 t a frames (.side side)=
      D.refinedCutSideValues q d hp hc hc' (fun z => lifted (.side z)) RJ
        (RT⁻¹*RJ⁻¹*(show (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
          (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ from lifted (.side ⟨q,none⟩))*RT) side := by
  have h := D.parent_markedLiftSideValue q d hp hc hc' hpMark hmaxMark φ seed b0 i0 t a frames side
  have hm := D.bandCutMirror_rebase q lifted J T
  exact h.trans (congrArg (fun Y => D.refinedCutSideValues q d hp hc hc'
    (fun z => lifted (.side z)) RJ Y side) hm)

lemma parent_markedLiftCutPortFrame
    (p : LocalPort _ (D.refinedCutDiagram q d hp hc hc').ports.kind) :
    (D.refinedCutDiagram q d hp hc hc').portFrame
      (D.external_markedAsCutValues q d hp hc hc' hpMark hmaxMark
        (D.refinedMarkedLiftValues q d hp hc hc' hpMark hmaxMark φ seed b0 i0 t a frames)) p =
      frames p := by
  calc
    _ = (D.refinedMarkedDiagram q d hp hc hc' hpMark hmaxMark).portFrame
      (D.refinedMarkedLiftValues q d hp hc hc' hpMark hmaxMark φ seed b0 i0 t a frames) p :=
        D.external_markedAsCutValues_portFrame q d hp hc hc' hpMark hmaxMark _ p
    _ = frames p :=
        D.parent_markedLiftPortFrame q d hp hc hc' hpMark hmaxMark φ seed b0 i0 t a frames p
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: ParentProducedValueDataInferredV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option quotPrecheck false
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable TwoFlagBand MatrixExpression HomTransport
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K] [Algebra R K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (hg : 0<D.genus (D.bandCutParent q))
    (P : D.Punctures R) (x : D.Solution P K)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
local notation "w" => D.producedCutBand q hg P x b0 i0

-- Infer the proposition from the checked generic interface, preserving its sharing.
def parent_producedMarkedSideValue :=
  D.parent_markedLiftSide_rebased q (w).shape rfl (w).rowRanks (w).colRanks
    hproper hmax (algebraMap R K) x.val.val b0 i0
    (D.bandCutHandleT q hg P x) (D.bandCutHandleA q hg P x)
    (D.producedMarkedFrames q hproper hmax hg P x b0 i0)

def parent_producedMarkedPortFrame :=
  D.parent_markedLiftPortFrame q (w).shape rfl (w).rowRanks (w).colRanks
    hproper hmax (algebraMap R K) x.val.val b0 i0
    (D.bandCutHandleT q hg P x) (D.bandCutHandleA q hg P x)
    (D.producedMarkedFrames q hproper hmax hg P x b0 i0)

def parent_producedCutPortFrame :=
  D.parent_markedLiftCutPortFrame q (w).shape rfl (w).rowRanks (w).colRanks
    hproper hmax (algebraMap R K) x.val.val b0 i0
    (D.bandCutHandleT q hg P x) (D.bandCutHandleA q hg P x)
    (D.producedMarkedFrames q hproper hmax hg P x b0 i0)
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: ProducedOldSeamDataInferredV3 -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option quotPrecheck false
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K] [Algebra R K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (hg : 0<D.genus (D.bandCutParent q))
    (P : D.Punctures R) (x : D.Solution P K)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
local notation "w" => D.producedCutBand q hg P x b0 i0
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q (w).shape)
local notation "B" => D.ports.refinedBandForSeam q (w).shape
local notation "C" => D.producedMarkedDiagram q hproper hmax hg P x b0 i0
local notation "v" => D.producedMarkedValues q hproper hmax hg P x b0 i0
local notation "CC" => D.refinedCutDiagram q (w).shape rfl (w).rowRanks (w).colRanks
local notation "cv" => D.external_markedAsCutValues q (w).shape rfl (w).rowRanks (w).colRanks hproper hmax v
local notation "g" => D.producedCutSeed q hg P x b0

variable (s : S)
local notation "ss" => BandGraft.oldPort A q B s true
local notation "Y" => ((D.producedCutT q hg P x b0 i0)⁻¹ * (D.producedCutJ q hg P x b0 i0)⁻¹ *
  (show (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
    (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ from g (.side ⟨q,none⟩)) *
    D.producedCutT q hg P x b0 i0)

local notation "J" => D.producedCutJ q hg P x b0 i0
local notation "T" => D.producedCutT q hg P x b0 i0

def external_producedOldParent_dataInferred (hs : s≠q) :=
  (congrArg (fun U => (MatrixIso.unit U).reindex
    (D.external_oldSideParent q (w).shape rfl (w).rowRanks (w).colRanks s)
    (D.external_oldSideParent q (w).shape rfl (w).rowRanks (w).colRanks s))
    (D.parent_producedMarkedSideValue q hproper hmax hg P x b0 i0 ⟨ss,none⟩)).trans
    (D.external_oldParentTransport q (w).shape rfl (w).rowRanks (w).colRanks s
      (fun a => g (.side a)) J Y hs)

def external_producedOldChild_dataInferred :=
  (congrArg (fun ds : (j : Fin ((BandGraft.wiring A q B).seamArity ss)) →
      MatrixIso K (Fin ((CC).childDim ss j)) (Fin ((CC).childDim ss j)) =>
      (MatrixIso.block ds).reindex
        (D.external_oldSideColumns q (w).shape rfl (w).rowRanks (w).colRanks s)
        (D.external_oldSideColumns q (w).shape rfl (w).rowRanks (w).colRanks s))
    (funext (fun ii => congrArg (fun U => MatrixIso.unit U⁻¹)
      (D.parent_producedMarkedSideValue q hproper hmax hg P x b0 i0 ⟨ss,some ii⟩)))).trans
    (D.external_oldChildInverseTransport q (w).shape rfl (w).rowRanks (w).colRanks s
      (fun a => g (.side a)) J Y)

def external_producedOldSeam_dataV2 (hs : s≠q) :=
  D.external_markedSeam_of_cut q (w).shape rfl (w).rowRanks (w).colRanks
    hproper hmax v (algebraMap R K) ss
    (D.external_oldSeamFromValues q w s hs (algebraMap R K) g (MatrixIso.unit T) cv
      (D.parent_producedCutPortFrame q hproper hmax hg P x b0 i0)
      (D.external_producedOldParent_dataInferred q hproper hmax hg P x b0 i0 s hs)
      (D.external_producedOldChild_dataInferred q hproper hmax hg P x b0 i0 s)
      (D.producedCutSeed_namedSeam q hg P x b0 s))
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: NamedTransportOne -/
section
set_option maxHeartbeats 0
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S)
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)

lemma external_namedParentLinear_one (hone : g (.side ⟨q,none⟩)=1) :
    D.namedParentLinear q g=LinearEquiv.refl K _ := by
  unfold namedParentLinear
  rw [hone]
  apply LinearEquiv.ext
  intro v
  exact Matrix.one_mulVec v

lemma external_namedChildInverse_one (hone : ∀ i,g (.side ⟨q,some i⟩)=1) :
    D.namedChildInverse q g=LinearEquiv.refl K _ := by
  have hv : (MatrixIso.block (fun i : Fin (arity q) =>
      MatrixIso.unit (g (.side ⟨q,some i⟩))⁻¹)).val=1 := by
    simp only [MatrixIso.block, MatrixIso.unit, hone, inv_one, Units.val_one]
    ext ⟨i,j⟩ ⟨k,l⟩
    by_cases h : i=k
    · subst k; simp [Matrix.blockDiagonal', Matrix.one_apply]
    · simp [Matrix.blockDiagonal', Matrix.one_apply, h]
  apply LinearEquiv.ext
  intro v
  exact (congrArg (fun M : Matrix _ _ K => M *ᵥ v) hv).trans (Matrix.one_mulVec v)

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: UnitSideSeam -/
section
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression HomTransport
variable {F S V K R : Type} {arity : S → ℕ} [Field K] [CommRing R]
    (D : Diagram F S V arity) (q : S) (φ : R →+* K)
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)

lemma external_unitSideSeam
    (hone : ∀ i : Option (Fin (arity q)), g (.side ⟨q,i⟩)=1)
    (hflag : SameFramedFlag (fun i : (j : Fin (arity q)) × Fin (D.childDim q j) => i.1.val)
      (D.namedSeamFrame q (g (.frame q false)))
      (D.namedSeamFrame q (g (.frame q true)))) :
    SameFramedFlag (D.seamGrade q)
      (matrixUnitEquiv ((D.seamLeft q).eval φ g))
      (matrixUnitEquiv ((D.seamRight q).eval φ g)) := by
  apply (D.named_seam_iff q φ g).mpr
  rw [D.external_namedParentLinear_one q g (hone none),
    D.external_namedChildInverse_one q g (fun i => hone (some i))]
  exact hflag

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: OriginalInternalSeam -/
section
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
end


/- Local proof module: InternalSideValues -/
section
set_option maxHeartbeats 0
set_option quotPrecheck false
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {r : ℕ} (d : TwoFlagBand.RankShape (arity q) (arity q) r)
    (hp : D.rank (D.ports.facet ⟨q,none⟩)=r)
    (hc : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.row i))
    (hc' : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.col i))
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q d)
local notation "B" => D.ports.refinedBandForSeam q d
local notation "C" => D.refinedCutDiagram q d hp hc hc'
variable (old : D.SideValues (R:=R))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) R)ˣ)

lemma external_originalInternalSide_one (j : Fin d.atomicBand.length)
    (i : Option (Fin ((BandGraft.wiring A q B).seamArity (BandGraft.originalPort A q B j.succ true)))) :
    D.refinedCutSideValues q d hp hc hc' old J Y ⟨BandGraft.originalPort A q B j.succ true,i⟩=1 := by
  exact graftSideValues_internal A (B).doublePatch (doubleDecoration (B).decoration) q
    ((B).patch.double_signatureMatch (B).decoration (B).patch_signatureMatch (B).shortFirst (B).shortLast)
    (fun i => by rw [(B).double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [(B).double_signature_minus]; cases i <;> rfl)
    (D.ports.refinedRank q d D.rank) (D.cutOldSideValues q old J) (D.cutShortSideValues q Y)
    (.inl (.inl j)) i

lemma external_mirrorInternalSide_one (j : Fin d.atomicBand.length)
    (i : Option (Fin ((BandGraft.wiring A q B).seamArity (BandGraft.mirrorOutput A q B j.castSucc)))) :
    D.refinedCutSideValues q d hp hc hc' old J Y ⟨BandGraft.mirrorOutput A q B j.castSucc,i⟩=1 := by
  exact graftSideValues_internal A (B).doublePatch (doubleDecoration (B).decoration) q
    ((B).patch.double_signatureMatch (B).decoration (B).patch_signatureMatch (B).shortFirst (B).shortLast)
    (fun i => by rw [(B).double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [(B).double_signature_minus]; cases i <;> rfl)
    (D.ports.refinedRank q d D.rank) (D.cutOldSideValues q old J) (D.cutShortSideValues q Y)
    (.inl (.inr j)) i
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: ProducedOriginalInternalSeamDataInferredV2 -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option quotPrecheck false
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K] [Algebra R K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (hg : 0<D.genus (D.bandCutParent q))
    (P : D.Punctures R) (x : D.Solution P K)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
local notation "w" => D.producedCutBand q hg P x b0 i0
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q (w).shape)
local notation "B" => D.ports.refinedBandForSeam q (w).shape
local notation "C" => D.producedMarkedDiagram q hproper hmax hg P x b0 i0
local notation "v" => D.producedMarkedValues q hproper hmax hg P x b0 i0
local notation "g" => D.producedCutSeed q hg P x b0

local notation "J" => D.producedCutJ q hg P x b0 i0
local notation "T" => D.producedCutT q hg P x b0 i0
local notation "Y" => (T⁻¹ * J⁻¹ *
  (show (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
    (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ from g (.side ⟨q,none⟩)) * T)
local notation "cv" => D.external_markedAsCutValues q (w).shape rfl (w).rowRanks (w).colRanks hproper hmax v

def external_producedOriginalInternalSide_one_data (jj : Fin (w).shape.atomicBand.length)
    (ii : Option (Fin ((BandGraft.wiring A q B).seamArity (BandGraft.originalPort A q B jj.succ true)))) :=
  (D.parent_producedMarkedSideValue q hproper hmax hg P x b0 i0 ⟨BandGraft.originalPort A q B jj.succ true,ii⟩).trans
    (D.external_originalInternalSide_one q (w).shape rfl (w).rowRanks (w).colRanks
      (fun a => g (.side a)) J Y jj ii)

def external_producedOriginalInternalSeam_data (jj : Fin (w).shape.atomicBand.length) :=
  D.external_markedSeam_of_cut q (w).shape rfl (w).rowRanks (w).colRanks
    hproper hmax v (algebraMap R K) (BandGraft.originalPort A q B jj.succ true)
    (D.external_originalInternalSeam q w jj (algebraMap R K) cv
      (D.portFrame g) (MatrixIso.unit T)
      (D.parent_producedCutPortFrame q hproper hmax hg P x b0 i0)
      (fun ii => D.external_producedOriginalInternalSide_one_data q hproper hmax hg P x b0 i0 jj ii))
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: MirrorInteriorFrame -/
section
set_option maxHeartbeats 0
namespace OAI.IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
noncomputable section
open scoped Classical
open TwoFlagBand OccurrenceIncidence VertexTable
variable {K : Type} [Field K] {n r : ℕ} {s : Fin n → ℕ}
    {f h : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K)}
    (w : IdentifiedBand s f h)

lemma external_mirror_color (v : Fin (w.shape.atomicBand.length+1))
    (p : (w.shape.atomicBand.kind v).table.Port)
    (a : Option ((w.shape.atomicBand.kind v).table.Child p)) :
    (w.shape.atomicBand.decoration v).mirror.color
      ⟨(w.shape.atomicBand.kind v).mirrorPort p,a.map ((w.shape.atomicBand.kind v).mirrorChild p)⟩=
      (w.shape.atomicBand.decoration v).color ⟨p,a⟩ := by
  change (w.shape.atomicBand.decoration v).color
    ((w.shape.atomicBand.kind v).mirrorEnd.symm ((w.shape.atomicBand.kind v).mirrorEnd ⟨p,a⟩))=_
  rw [Equiv.symm_apply_apply]

def external_mirrorInteriorChild (j : Fin w.shape.atomicBand.length) :
    (w.shape.atomicBand.kind j.castSucc).mirror.table.Child
      ((w.shape.atomicBand.kind j.castSucc).mirrorPort (w.shape.atomicBand.kind j.castSucc).output) ≃
    (w.shape.atomicBand.kind j.succ).mirror.table.Child
      ((w.shape.atomicBand.kind j.succ).mirrorPort (w.shape.atomicBand.kind j.succ).input) :=
  ((w.shape.atomicBand.kind j.castSucc).mirrorChild _).symm.trans
    ((w.interiorChild j).trans ((w.shape.atomicBand.kind j.succ).mirrorChild _))

lemma external_mirrorInteriorParent (j : Fin w.shape.atomicBand.length) :
    (w.shape.atomicBand.decoration j.castSucc).mirror.color
      ⟨(w.shape.atomicBand.kind j.castSucc).mirrorPort (w.shape.atomicBand.kind j.castSucc).output,none⟩=
    (w.shape.atomicBand.decoration j.succ).mirror.color
      ⟨(w.shape.atomicBand.kind j.succ).mirrorPort (w.shape.atomicBand.kind j.succ).input,none⟩ := by
  have h1 := w.external_mirror_color j.castSucc (w.shape.atomicBand.kind j.castSucc).output none
  have h2 := w.external_mirror_color j.succ (w.shape.atomicBand.kind j.succ).input none
  simp only [Option.map_none] at h1 h2
  exact h1.trans ((w.interior_parent j).trans h2.symm)

lemma external_mirrorInteriorChildColor (j : Fin w.shape.atomicBand.length) (a) :
    (w.shape.atomicBand.decoration j.castSucc).mirror.color
      ⟨(w.shape.atomicBand.kind j.castSucc).mirrorPort (w.shape.atomicBand.kind j.castSucc).output,some a⟩=
    (w.shape.atomicBand.decoration j.succ).mirror.color
      ⟨(w.shape.atomicBand.kind j.succ).mirrorPort (w.shape.atomicBand.kind j.succ).input,
        some (w.external_mirrorInteriorChild j a)⟩ := by
  obtain ⟨b,rfl⟩ := ((w.shape.atomicBand.kind j.castSucc).mirrorChild
    (w.shape.atomicBand.kind j.castSucc).output).surjective a
  have hi : w.external_mirrorInteriorChild j
      (((w.shape.atomicBand.kind j.castSucc).mirrorChild _) b)=
      ((w.shape.atomicBand.kind j.succ).mirrorChild _) (w.interiorChild j b) := by
    simp only [external_mirrorInteriorChild,Equiv.trans_apply,Equiv.symm_apply_apply]
  rw [hi]
  have h1 := w.external_mirror_color j.castSucc (w.shape.atomicBand.kind j.castSucc).output (some b)
  have h2 := w.external_mirror_color j.succ (w.shape.atomicBand.kind j.succ).input (some (w.interiorChild j b))
  simp only [Option.map_some] at h1 h2
  exact h1.trans ((w.interior_child j b).trans h2.symm)

lemma external_mirrorInteriorFrame (T : MatrixIso K (Fin r) (Fin r))
    (j : Fin w.shape.atomicBand.length) :
    (w.mirrorVertexFrames T j.succ
      ((w.shape.atomicBand.kind j.succ).mirrorPort (w.shape.atomicBand.kind j.succ).input)).reindex
      ((w.shape.vertexAtoms j.castSucc).mirror.seamColumns (w.shape.vertexAtoms j.succ).mirror
        _ _ (w.external_mirrorInteriorChild j)
        (fun a => congrArg w.shape.facetAtoms (w.external_mirrorInteriorChildColor j a)))
      (finCongr ((w.shape.vertexAtoms j.castSucc).mirror.rank_of_atoms (w.shape.vertexAtoms j.succ).mirror
        (congrArg w.shape.facetAtoms (w.external_mirrorInteriorParent j))))=
    w.mirrorVertexFrames T j.castSucc
      ((w.shape.atomicBand.kind j.castSucc).mirrorPort (w.shape.atomicBand.kind j.castSucc).output) := by
  apply (w.shape.vertexAtoms j.castSucc).mirror.reframe_seam (w.shape.vertexAtoms j.succ).mirror
    (w.mirrorVertexBases T j.castSucc) (w.mirrorVertexBases T j.succ) _ _
    (w.external_mirrorInteriorChild j)
    (congrArg w.shape.facetAtoms (w.external_mirrorInteriorParent j))
    (fun a => congrArg w.shape.facetAtoms (w.external_mirrorInteriorChildColor j a))
  · exact MatrixIso.finite_basis_transport _ (w.mirrorColorGauge T) _ _ _ _ _ _
      (w.external_mirrorInteriorParent j) _
  · intro a
    exact MatrixIso.finite_basis_transport _ (w.mirrorColorGauge T) _ _ _ _ _ _
      (w.external_mirrorInteriorChildColor j a) _
end
end OAI.IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
end


/- Local proof module: MirrorInternalSeam -/
section
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
end


/- Local proof module: ProducedMirrorInternalSeamDataInferredV2 -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option quotPrecheck false
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K] [Algebra R K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (hg : 0<D.genus (D.bandCutParent q))
    (P : D.Punctures R) (x : D.Solution P K)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
local notation "w" => D.producedCutBand q hg P x b0 i0
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q (w).shape)
local notation "B" => D.ports.refinedBandForSeam q (w).shape
local notation "C" => D.producedMarkedDiagram q hproper hmax hg P x b0 i0
local notation "v" => D.producedMarkedValues q hproper hmax hg P x b0 i0
local notation "g" => D.producedCutSeed q hg P x b0

local notation "J" => D.producedCutJ q hg P x b0 i0
local notation "T" => D.producedCutT q hg P x b0 i0
local notation "Y" => (T⁻¹ * J⁻¹ *
  (show (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
    (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ from g (.side ⟨q,none⟩)) * T)
local notation "cv" => D.external_markedAsCutValues q (w).shape rfl (w).rowRanks (w).colRanks hproper hmax v

def external_producedMirrorInternalSide_one_data (jj : Fin (w).shape.atomicBand.length)
    (ii : Option (Fin ((BandGraft.wiring A q B).seamArity (BandGraft.mirrorOutput A q B jj.castSucc)))) :=
  (D.parent_producedMarkedSideValue q hproper hmax hg P x b0 i0 ⟨BandGraft.mirrorOutput A q B jj.castSucc,ii⟩).trans
    (D.external_mirrorInternalSide_one q (w).shape rfl (w).rowRanks (w).colRanks
      (fun a => g (.side a)) J Y jj ii)

def external_producedMirrorInternalSeam_data (jj : Fin (w).shape.atomicBand.length) :=
  D.external_markedSeam_of_cut q (w).shape rfl (w).rowRanks (w).colRanks
    hproper hmax v (algebraMap R K) (BandGraft.mirrorOutput A q B jj.castSucc)
    (D.external_mirrorInternalSeam q w jj (algebraMap R K) cv
      (D.portFrame g) (MatrixIso.unit T)
      (D.parent_producedCutPortFrame q hproper hmax hg P x b0 i0)
      (fun ii => D.external_producedMirrorInternalSide_one_data q hproper hmax hg P x b0 i0 jj ii))
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: TransverseSeamV2 -/
section
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

end


/- Local proof module: TransverseWiringGeneric -/
section
set_option maxHeartbeats 0
set_option quotPrecheck false
set_option autoImplicit false
namespace OAI.IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
noncomputable section
open scoped Classical
open VertexTable
variable {F S V : Type} {arity : S → ℕ}
    (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
variable (a : {a : {p : PortAt B.kind true // p∉Set.range (VariableGallery.internalPlus B.kind)} // a≠B.shortFirst})
local notation "ps" => graftPlus A B.doublePatch (.inr (.inl (.inr (.inl a))))
lemma external_transversePlusPort :
    (ps).val=(⟨.inr (.inl a.val.val.val.1),a.val.val.val.2⟩ : LocalPort _ (kind A q B)) := rfl
lemma external_transversePlusWire :
    (wiring A q B).wire ps=
      graftMinus A B.doublePatch (.inr (.inl (.inr (.inl a)))) := by
  have hh := graft_wire_plus A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus];cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus];cases i <;> rfl)
    (.inr (.inl (.inr (.inl a))))
  rw [graftCycle_internal] at hh
  exact hh
lemma external_transversePlusNegativePort :
    (graftMinus A B.doublePatch (.inr (.inl (.inr (.inl a))))).val=
      (⟨.inr (.inr a.val.val.val.1),(B.kind a.val.val.val.1).mirrorPort a.val.val.val.2⟩ :
        LocalPort _ (kind A q B)) := rfl
variable (b : {b : {p : PortAt B.kind false // p∉Set.range (VariableGallery.internalMinus B.kind)} // b≠B.shortLast})
local notation "ms" => graftPlus A B.doublePatch (.inr (.inl (.inr (.inr b))))
lemma external_transverseMinusPort :
    (ms).val=(⟨.inr (.inr b.val.val.val.1),(B.kind b.val.val.val.1).mirrorPort b.val.val.val.2⟩ :
      LocalPort _ (kind A q B)) := rfl
lemma external_transverseMinusWire :
    (wiring A q B).wire ms=
      graftMinus A B.doublePatch (.inr (.inl (.inr (.inr b)))) := by
  have hh := graft_wire_plus A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus];cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus];cases i <;> rfl)
    (.inr (.inl (.inr (.inr b))))
  rw [graftCycle_internal] at hh
  exact hh
lemma external_transverseMinusNegativePort :
    (graftMinus A B.doublePatch (.inr (.inl (.inr (.inr b))))).val=
      (⟨.inr (.inl b.val.val.val.1),b.val.val.val.2⟩ : LocalPort _ (kind A q B)) := rfl
end
end OAI.IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
end


/- Local proof module: TransverseSideAttachGeneric -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option quotPrecheck false
namespace OAI.IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
noncomputable section
open scoped Classical Matrix
open VertexTable
variable {F S V R : Type} [CommRing R] {arity : S → ℕ}
    (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
variable (a : {a : {p : PortAt B.kind true // p∉Set.range (VariableGallery.internalPlus B.kind)} // a≠B.shortFirst})
local notation "ps" => graftPlus A B.doublePatch (.inr (.inl (.inr (.inl a))))
variable (b : {b : {p : PortAt B.kind false // p∉Set.range (VariableGallery.internalMinus B.kind)} // b≠B.shortLast})
local notation "ms" => graftPlus A B.doublePatch (.inr (.inl (.inr (.inr b))))

lemma external_transversePlusOrigAttach_generic :
    (wiring A q B).endOf
      (⟨.inr (.inl a.val.val.val.1),a.val.val.val.2⟩ : LocalPort _ (kind A q B))=(ps,true) :=
  (wiring A q B).endOf_portAt (ps,true)
lemma external_transversePlusMirrorAttach_generic :
    (wiring A q B).endOf
      (⟨.inr (.inr a.val.val.val.1),(B.kind a.val.val.val.1).mirrorPort a.val.val.val.2⟩ :
        LocalPort _ (kind A q B))=(ps,false) := by
  have hh := (wiring A q B).endOf_portAt (ps,false)
  change (wiring A q B).endOf ((wiring A q B).wire ps).val=_ at hh
  rw [external_transversePlusWire] at hh
  exact hh
lemma external_transverseMinusMirrorAttach_generic :
    (wiring A q B).endOf
      (⟨.inr (.inr b.val.val.val.1),(B.kind b.val.val.val.1).mirrorPort b.val.val.val.2⟩ :
        LocalPort _ (kind A q B))=(ms,true) :=
  (wiring A q B).endOf_portAt (ms,true)
lemma external_transverseMinusOrigAttach_generic :
    (wiring A q B).endOf
      (⟨.inr (.inl b.val.val.val.1),b.val.val.val.2⟩ : LocalPort _ (kind A q B))=(ms,false) := by
  have hh := (wiring A q B).endOf_portAt (ms,false)
  change (wiring A q B).endOf ((wiring A q B).wire ms).val=_ at hh
  rw [external_transverseMinusWire] at hh
  exact hh
lemma external_transversePlusSide_generic
    (rank : F → ℕ)
    (old : (s : Side S arity) → (Matrix (Fin (rank (A.facet s))) (Fin (rank (A.facet s))) R)ˣ)
    (short : Bool → (i : Option (Fin (arity q))) →
      (Matrix (Fin (rank (A.facet ⟨q,i⟩))) (Fin (rank (A.facet ⟨q,i⟩))) R)ˣ)
    (i : Option (Fin ((wiring A q B).seamArity ps))) :
    graftSideValues A B.doublePatch (doubleDecoration B.decoration) q
      (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
      (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
      (fun i => by rw [B.double_signature_minus]; cases i <;> rfl)
      rank old short ⟨ps,i⟩=1 := by
  exact graftSideValues_internal A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl)
    rank old short (.inr (.inl a)) i

lemma external_transverseMinusSide_generic
    (rank : F → ℕ)
    (old : (s : Side S arity) → (Matrix (Fin (rank (A.facet s))) (Fin (rank (A.facet s))) R)ˣ)
    (short : Bool → (i : Option (Fin (arity q))) →
      (Matrix (Fin (rank (A.facet ⟨q,i⟩))) (Fin (rank (A.facet ⟨q,i⟩))) R)ˣ)
    (i : Option (Fin ((wiring A q B).seamArity ms))) :
    graftSideValues A B.doublePatch (doubleDecoration B.decoration) q
      (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
      (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
      (fun i => by rw [B.double_signature_minus]; cases i <;> rfl)
      rank old short ⟨ms,i⟩=1 := by
  exact graftSideValues_internal A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl)
    rank old short (.inr (.inr b)) i

end
end OAI.IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
end


/- Local proof module: TransverseNonprincipal -/
section
set_option maxHeartbeats 0
namespace OAI.IntegralCharacterVarieties.OccurrenceIncidence.VariableGallery
noncomputable section
open scoped Classical
open VertexTable
variable {l : ℕ} (kind : Fin (l+1) → Kind)

def ExternalPositive := {p : PortAt kind true // p∉Set.range (internalPlus kind)}
def ExternalNegative := {p : PortAt kind false // p∉Set.range (internalMinus kind)}
lemma external_positive_ne_input (a : ExternalPositive kind)
    (ha : a ≠ ⟨input kind 0,first_exposed kind⟩) : a.val.val.2≠(kind a.val.val.1).input := by
  intro he
  let v := a.val.val.1
  have hp : a.val=input kind v := by
    apply Subtype.ext
    exact Sigma.ext rfl (heq_of_eq he)
  have hv : v=0 := by
    by_contra hn
    let j : Fin l := ⟨v.val-1,by have := v.isLt;have hv0 : v.val≠0 := fun h => hn (Fin.ext h);have : 0<v.val := Nat.pos_of_ne_zero hv0;omega⟩
    have hj : j.succ=v := by apply Fin.ext;have hv0 : v.val≠0 := fun h => hn (Fin.ext h);have : 0<v.val := Nat.pos_of_ne_zero hv0;dsimp [j];omega
    apply a.property
    exact ⟨j,by change input kind j.succ=a.val;rw [hj,hp]⟩
  apply ha
  apply Subtype.ext
  exact hp.trans (congrArg (input kind) hv)

lemma external_positive_ne_output (a : ExternalPositive kind) : a.val.val.2≠(kind a.val.val.1).output := by
  intro he
  have hh := a.val.property
  rw [he,Kind.output_endpoint] at hh
  cases hh

lemma external_negative_ne_output (a : ExternalNegative kind)
    (ha : a ≠ ⟨output kind (Fin.last l),last_exposed kind⟩) : a.val.val.2≠(kind a.val.val.1).output := by
  intro he
  let v := a.val.val.1
  have hp : a.val=output kind v := by
    apply Subtype.ext
    exact Sigma.ext rfl (heq_of_eq he)
  have hv : v=Fin.last l := by
    by_contra hn
    let j : Fin l := ⟨v.val,by have := v.isLt;have : v.val≠l := fun h => hn (Fin.ext h);omega⟩
    have hj : j.castSucc=v := Fin.ext rfl
    apply a.property
    exact ⟨j,by change output kind j.castSucc=a.val;rw [hj,hp]⟩
  apply ha
  apply Subtype.ext
  exact hp.trans (congrArg (output kind) hv)

lemma external_negative_ne_input (a : ExternalNegative kind) : a.val.val.2≠(kind a.val.val.1).input := by
  intro he
  have hh := a.val.property
  rw [he,Kind.input_endpoint] at hh
  cases hh
end
end OAI.IntegralCharacterVarieties.OccurrenceIncidence.VariableGallery
end


/- Local proof module: ProducedTransverseSeamsDataInferredV2 -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option quotPrecheck false
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K] [Algebra R K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (hg : 0<D.genus (D.bandCutParent q))
    (P : D.Punctures R) (x : D.Solution P K)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
local notation "w" => D.producedCutBand q hg P x b0 i0
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q (w).shape)
local notation "B" => D.ports.refinedBandForSeam q (w).shape
local notation "C" => D.producedMarkedDiagram q hproper hmax hg P x b0 i0
local notation "v" => D.producedMarkedValues q hproper hmax hg P x b0 i0
local notation "g" => D.producedCutSeed q hg P x b0


local notation "J" => D.producedCutJ q hg P x b0 i0
local notation "T" => D.producedCutT q hg P x b0 i0
local notation "Y" => (T⁻¹ * J⁻¹ *
  (show (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
    (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ from g (.side ⟨q,none⟩)) * T)
local notation "cv" => D.external_markedAsCutValues q (w).shape rfl (w).rowRanks (w).colRanks hproper hmax v

def external_producedTransversePlus_dataSide_one (aa : {a : {p : PortAt (B).kind true // p∉Set.range (VariableGallery.internalPlus (B).kind)} // a≠(B).shortFirst})
    (ii : Option (Fin ((BandGraft.wiring A q B).seamArity (graftPlus A (B).doublePatch (.inr (.inl (.inr (.inl aa)))))))) :=
  (D.parent_producedMarkedSideValue q hproper hmax hg P x b0 i0 ⟨graftPlus A (B).doublePatch (.inr (.inl (.inr (.inl aa)))),ii⟩).trans
    (BandGraft.external_transversePlusSide_generic A q B aa
      (D.ports.refinedRank q (w).shape D.rank)
      (D.cutOldSideValues q (fun a => g (.side a)) J)
      (D.cutShortSideValues q Y) ii)

def external_producedTransversePlus_dataSeam (aa : {a : {p : PortAt (B).kind true // p∉Set.range (VariableGallery.internalPlus (B).kind)} // a≠(B).shortFirst}) :=
  D.external_markedSeam_of_cut q (w).shape rfl (w).rowRanks (w).colRanks
    hproper hmax v (algebraMap R K) (graftPlus A (B).doublePatch (.inr (.inl (.inr (.inl aa)))))
    (D.external_transverseSeam q w (aa.val.val.val.1) (aa.val.val.val.2)
      (graftPlus A (B).doublePatch (.inr (.inl (.inr (.inl aa))))) true
      (BandGraft.external_transversePlusOrigAttach_generic A q B aa)
      (BandGraft.external_transversePlusMirrorAttach_generic A q B aa)
      (algebraMap R K) cv (D.portFrame g) (MatrixIso.unit T)
      (VariableGallery.external_positive_ne_input (B).kind aa.val aa.property) (VariableGallery.external_positive_ne_output (B).kind aa.val)
      (D.parent_producedCutPortFrame q hproper hmax hg P x b0 i0)
      (fun ii => D.external_producedTransversePlus_dataSide_one q hproper hmax hg P x b0 i0 aa ii))

def external_producedTransverseMinus_dataSide_one (bb : {a : {p : PortAt (B).kind false // p∉Set.range (VariableGallery.internalMinus (B).kind)} // a≠(B).shortLast})
    (ii : Option (Fin ((BandGraft.wiring A q B).seamArity (graftPlus A (B).doublePatch (.inr (.inl (.inr (.inr bb)))))))) :=
  (D.parent_producedMarkedSideValue q hproper hmax hg P x b0 i0 ⟨graftPlus A (B).doublePatch (.inr (.inl (.inr (.inr bb)))),ii⟩).trans
    (BandGraft.external_transverseMinusSide_generic A q B bb
      (D.ports.refinedRank q (w).shape D.rank)
      (D.cutOldSideValues q (fun a => g (.side a)) J)
      (D.cutShortSideValues q Y) ii)

def external_producedTransverseMinus_dataSeam (bb : {a : {p : PortAt (B).kind false // p∉Set.range (VariableGallery.internalMinus (B).kind)} // a≠(B).shortLast}) :=
  D.external_markedSeam_of_cut q (w).shape rfl (w).rowRanks (w).colRanks
    hproper hmax v (algebraMap R K) (graftPlus A (B).doublePatch (.inr (.inl (.inr (.inr bb)))))
    (D.external_transverseSeam q w (bb.val.val.val.1) (bb.val.val.val.2)
      (graftPlus A (B).doublePatch (.inr (.inl (.inr (.inr bb))))) false
      (BandGraft.external_transverseMinusOrigAttach_generic A q B bb)
      (BandGraft.external_transverseMinusMirrorAttach_generic A q B bb)
      (algebraMap R K) cv (D.portFrame g) (MatrixIso.unit T)
      (VariableGallery.external_negative_ne_input (B).kind bb.val) (VariableGallery.external_negative_ne_output (B).kind bb.val bb.property)
      (D.parent_producedCutPortFrame q hproper hmax hg P x b0 i0)
      (fun ii => D.external_producedTransverseMinus_dataSide_one q hproper hmax hg P x b0 i0 bb ii))
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: FirstCommonEqualityV3 -/
section
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
end


/- Local proof module: FirstPortFrameShared -/
section
set_option autoImplicit false
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

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity)

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

lemma external_firstPortFrame_eq :
    ((D.namedCutPortFrames q w old T p0).reindex
      (D.external_firstPortColumns q w).symm
      (finCongr (D.external_firstPortParentRank q w)).symm).linearEquiv = w.firstFrame := by
  have ec : w.firstColumns.symm.trans
      (Equiv.sigmaCongr (Equiv.refl ((w.shape.atomicBand.kind 0).table.Child (w.shape.atomicBand.kind 0).input))
        (fun c => finCongr (congrArg (fun d => d.rank (w.shape.atomicBand.kind 0).input (some c))
          (D.namedCut_orig_localRanks q w 0)))) =
      (D.external_firstPortColumns q w).symm := by
    apply Equiv.ext
    intro i
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Fin.ext
      rfl
  have ep : (finCongr w.firstParent_rank).symm.trans
      (finCongr (congrArg (fun d => d.rank (w.shape.atomicBand.kind 0).input none)
        (D.namedCut_orig_localRanks q w 0))) =
      (finCongr (D.external_firstPortParentRank q w)).symm := by
    ext i
    rfl
  have hh := LocalRanks.external_transportFrames_reindex (D.namedCut_orig_localRanks q w 0)
    (w.vertexFrames 0) (w.shape.atomicBand.kind 0).input
  have hh2 := congrArg (fun u => (u.reindex w.firstColumns.symm (finCongr w.firstParent_rank).symm).linearEquiv) hh
  erw [MatrixIso.reindex_reindex_eq, ec, ep] at hh2
  exact hh2

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram

end


/- Local proof module: FirstNegativeFrameShared -/
section
set_option autoImplicit false
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
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "s0" => BandGraft.originalPort A q B 0 true
local notation "pold" => (Subtype.val (D.ports.portAt false q))
local notation "pn" => (Subtype.val (BandGraft.oldPort A q B q false))

lemma external_firstNegativePortFrame_eq
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    ((D.namedCutPortFrames q w (D.portFrame g) T pn).reindex
      (D.external_firstNegativePortColumns q w).symm
      (finCongr (show ((C).vertexRanks (pn).1).rank (pn).2 none = D.rank (D.ports.facet ⟨q,none⟩) from by
        have hh := congrArg (fun d => d.rank (pold).2 none)
          (D.refinedCut_old_vertexRanks q w.shape rfl w.rowRanks w.colRanks (pold).1)
        exact hh.trans (congrArg (fun e : S × Bool => D.rank (D.ports.facet ⟨e.1,none⟩))
          (D.ports.attach_portAt q false)))).symm).linearEquiv =
      D.namedSeamFrame q (g (.frame q false)) := by
  have hh := LocalRanks.external_transportFrames_reindex
    (D.refinedCut_old_vertexRanks q w.shape rfl w.rowRanks w.colRanks (pold).1).symm
    (fun z => D.portFrame g ⟨(pold).1,z⟩) (pold).2
  have ho := D.external_namedFrame_port_at g pold q false (D.ports.attach_portAt q false)
  have hh2 := congrArg (fun u => ((u.reindex (D.external_portColumns pold).symm (Equiv.refl _)).reindex
    (D.external_seamColumnsTransport (congrArg Prod.fst (D.ports.attach_portAt q false))).symm
    (finCongr (congrArg (fun z => D.rank (D.ports.facet ⟨z,none⟩))
      (congrArg Prod.fst (D.ports.attach_portAt q false)))).symm).linearEquiv) hh
  have ec : (((D.external_seamColumnsTransport (congrArg Prod.fst (D.ports.attach_portAt q false))).symm.trans
      (D.external_portColumns pold).symm).trans
      (Equiv.sigmaCongr (Equiv.refl ((D.ports.kind (pold).1).table.Child (pold).2)) (fun c =>
        finCongr (congrArg (fun d => d.rank (pold).2 (some c))
          (D.refinedCut_old_vertexRanks q w.shape rfl w.rowRanks w.colRanks (pold).1).symm)))) =
      (D.external_firstNegativePortColumns q w).symm := by
    have aux {α β : Type} (e f : α ≃ β) (h : e.symm=f.symm) : e=f := by
      have hh := congrArg Equiv.symm h
      exact hh
    apply aux
    apply Equiv.ext
    intro i
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Fin.ext
      rfl
  erw [MatrixIso.reindex_reindex_eq,MatrixIso.reindex_reindex_eq] at hh2
  have hfinal := hh2.trans ho
  convert hfinal using 1
  · congr 2
    exact ec.symm

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram

end


/- Local proof module: FirstSeamShared -/
section
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

end


/- Local proof module: GraftShortUnit -/
section
set_option maxHeartbeats 0
namespace OAI.IntegralCharacterVarieties.OccurrenceIncidence
noncomputable section
open scoped Classical Matrix
open VertexTable SurfacePresentation.Diagram
variable {F S V W I R : Type} {arity : S → ℕ} [CommRing R]
    (A : PortAssembly F S V arity) {kind : W → Kind}
    (P : PortPatch kind I Bool Bool) (d : (w : W) → Decoration (kind w) F)
    (q : S) (hi : P.SignatureMatch d)
    (hp : ∀ b,portSignature d (P.plus (.inr b)).val=A.seamSignature q)
    (hm : ∀ b,portSignature d (P.minus (.inr b)).val=A.seamSignature q)
local notation "E" => graftSideEquiv A P d q hi hp hm
local notation "a" => graftLabelArity A P d q hi hp hm
variable (rank : F → ℕ)
    (old : (s : Side S arity) → FacetUnit (R:=R) rank (A.facet s))
    (short : Bool → (i : Option (Fin (arity q))) → FacetUnit (R:=R) rank (A.facet ⟨q,i⟩))

lemma external_graftSideValues_short_one (b : Bool)
    (hone : ∀ i,short b i=1) (i : Option (Fin (a (.inr (.inr b))))) :
    graftSideValues A P d q hi hp hm rank old short (E ⟨.inr (.inr b),i⟩)=1 := by
  rw [graftSideValues_coord]
  unfold graftLabelValues
  simp only [hone]
  generalize_proofs ht
  have castOne {nn mm : ℕ} (hn : nn=mm)
      (ht : (Matrix (Fin nn) (Fin nn) R)ˣ=(Matrix (Fin mm) (Fin mm) R)ˣ) :
      cast ht (1 : (Matrix (Fin nn) (Fin nn) R)ˣ)=1 := by
    subst mm
    rfl
  apply castOne
  have hc := graft_short_color A P d q hi hp hm b (i.map (finCongr ht))
  have hi' : (i.map (finCongr ht)).map
      (finCongr (graftLabelArity_short A P d q hi hp hm b).symm)=i := by
    cases i with
    | none => rfl
    | some i => rfl
  have hc' : (graftAssembly A P d q hi hp hm).facet
      (E ⟨.inr (.inr b),i⟩)=A.facet ⟨q,i.map (finCongr ht)⟩ := by
    change (graftAssembly A P d q hi hp hm).facet ⟨graftPlus A P (.inr (.inr b)),i⟩=_
    erw [hi'] at hc
    exact hc
  exact congrArg rank hc'.symm

end
end OAI.IntegralCharacterVarieties.OccurrenceIncidence
end


/- Local proof module: BandFirstShortValues -/
section
set_option maxHeartbeats 0
namespace OAI.IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
noncomputable section
open scoped Classical Matrix
open VertexTable SurfacePresentation.Diagram
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
    (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
    (rank : F → ℕ)
    (old : (s : Side S arity) → FacetUnit (R:=R) rank (A.facet s))
    (short : Bool → (i : Option (Fin (arity q))) → FacetUnit (R:=R) rank (A.facet ⟨q,i⟩))
lemma external_bandValues_first_one (hone : ∀ i,short false i=1)
    (i : Option (Fin ((wiring A q B).seamArity (originalPort A q B 0 true)))) :
    bandValues A q B rank old short ⟨originalPort A q B 0 true,i⟩=1 := by
  exact external_graftSideValues_short_one A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun j => by rw [B.double_signature_plus]; cases j <;> rfl)
    (fun j => by rw [B.double_signature_minus]; cases j <;> rfl)
    rank old short false hone i
end
end OAI.IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
end


/- Local proof module: RefinedFirstShortAtPortV2 -/
section
set_option maxHeartbeats 0
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {r : ℕ} (d : TwoFlagBand.RankShape (arity q) (arity q) r)
    (hp : D.rank (D.ports.facet ⟨q,none⟩)=r)
    (hc : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.row i))
    (hc' : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.col i))
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q d)
local notation "B" => D.ports.refinedBandForSeam q d
local notation "C" => D.refinedCutDiagram q d hp hc hc'
local notation "s0" => BandGraft.originalSide A q B 0

lemma external_refinedFirstShortSideValuesAtPortV2 (old : D.SideValues (R:=K))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
    (i : Option (Fin ((BandGraft.wiring A q B).seamArity
      (BandGraft.originalPort A q B 0 true)))) :
    D.refinedCutSideValues q d hp hc hc' old J Y
      ⟨BandGraft.originalPort A q B 0 true,i⟩=1 := by
  exact BandGraft.external_bandValues_first_one A q B
    (D.ports.refinedRank q d D.rank) (D.cutOldSideValues q old J) (D.cutShortSideValues q Y)
    (by intro j; cases j <;> rfl) i

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: MarkedLiftFirstSide -/
section
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
end


/- Local proof module: ProducedFirstShortSharedInferredV2 -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option quotPrecheck false
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K] [Algebra R K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (hg : 0<D.genus (D.bandCutParent q))
    (P : D.Punctures R) (x : D.Solution P K)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
local notation "w" => D.producedCutBand q hg P x b0 i0
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q (w).shape)
local notation "B" => D.ports.refinedBandForSeam q (w).shape
local notation "C" => D.producedMarkedDiagram q hproper hmax hg P x b0 i0
local notation "v" => D.producedMarkedValues q hproper hmax hg P x b0 i0
local notation "ss" => BandGraft.originalPort A q B 0 true
local notation "CC" => D.refinedCutDiagram q (w).shape rfl (w).rowRanks (w).colRanks
local notation "cv" => D.external_markedAsCutValues q (w).shape rfl (w).rowRanks (w).colRanks hproper hmax v
local notation "g" => D.producedCutSeed q hg P x b0

local notation "J" => D.producedCutJ q hg P x b0 i0
local notation "T" => D.producedCutT q hg P x b0 i0
local notation "Y" => (T⁻¹ * J⁻¹ *
  (show (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
    (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ from g (.side ⟨q,none⟩)) * T)

def external_producedFirstSide_one_shared
    (ii : Option (Fin ((BandGraft.wiring A q B).seamArity ss))) :=
  D.external_markedLiftFirstSide_one q (w).shape rfl (w).rowRanks (w).colRanks
    hproper hmax (algebraMap R K) x.val.val b0 i0
    (D.bandCutHandleT q hg P x) (D.bandCutHandleA q hg P x)
    (D.producedMarkedFrames q hproper hmax hg P x b0 i0) ii

def external_producedFirstShortEquation_shared :=
  D.external_markedSeam_of_cut q (w).shape rfl (w).rowRanks (w).colRanks
    hproper hmax v (algebraMap R K) ss
    ((CC).external_unitSideSeam ss (algebraMap R K) cv
      (fun ii => D.external_producedFirstSide_one_shared q hproper hmax hg P x b0 i0 ii)
      (D.external_firstActualFlagFromPortFrames_shared q w g (MatrixIso.unit T) cv
        (D.parent_producedCutPortFrame q hproper hmax hg P x b0 i0) rfl))
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: ParentSelectedLastPortFixed -/
section
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
end


/- Local proof module: ParentSelectedEndpointsModular -/
section
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
local notation "ss" => BandGraft.oldPort A q B q true
local notation "pp" => (Subtype.val (BandGraft.oldPort A q B q true))
local notation "nn" => (Subtype.val (BandGraft.originalPort A q B (Fin.last (B).length) false))

lemma parent_selectedPositiveAttach : (C).ports.attach pp=(ss,true) := by
  exact (BandGraft.wiring A q B).endOf_portAt (ss,true)

lemma parent_selectedNegativeAttach : (C).ports.attach nn=(ss,false) := by
  have hh := (BandGraft.wiring A q B).endOf_portAt (ss,false)
  change (BandGraft.wiring A q B).endOf ((BandGraft.wiring A q B).wire ss).val = _ at hh
  erw [BandGraft.wire_last] at hh
  exact hh

lemma parent_selectedPositivePortParentRank :
    ((C).vertexRanks (pp).1).rank (pp).2 none = D.rank (D.ports.facet ⟨q,none⟩) := by
  have hh := congrArg (fun d => d.rank (Subtype.val (D.ports.portAt true q)).2 none)
    (D.refinedCut_old_vertexRanks q w.shape rfl w.rowRanks w.colRanks
      (Subtype.val (D.ports.portAt true q)).1)
  exact hh.trans (congrArg (fun e : S × Bool => D.rank (D.ports.facet ⟨e.1,none⟩))
    (D.ports.attach_portAt q true))

def parent_selectedCommonColumns :=
    (D.external_oldEndpointNamedColumns q w q true).trans
      ((C).external_seamColumnsTransport (congrArg Prod.fst (D.parent_selectedPositiveAttach q w)))

def parent_selectedCommonParent :=
  (finCongr (D.parent_selectedPositivePortParentRank q w)).symm.trans
    (finCongr (congrArg (fun z => (C).rank ((C).ports.facet ⟨z,none⟩))
      (congrArg Prod.fst (D.parent_selectedPositiveAttach q w))))

lemma parent_selectedCommonColumns_grade
    (i : (j : Fin (arity q)) × Fin (D.childDim q j)) :
    (D.parent_selectedCommonColumns q w i).1.val = i.1.val := by
  exact D.external_oldEndpointNamedColumns_grade q w q true i

lemma parent_selectedPositiveEndpoint_eq
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    (((C).external_endpointNamedMatrix (D.namedCutPortFrames q w (D.portFrame g) T)
      pp ss true (D.parent_selectedPositiveAttach q w)).reindex
      (D.parent_selectedCommonColumns q w) (D.parent_selectedCommonParent q w)).linearEquiv =
        D.namedSeamFrame q (g (.frame q true)) := by
  have hh := (C).external_endpointNamedMatrix_normalized
    (D.namedCutPortFrames q w (D.portFrame g) T) pp ss true
    (D.parent_selectedPositiveAttach q w) (D.external_oldEndpointPortColumns q w q true).symm
    (finCongr (D.parent_selectedPositivePortParentRank q w)).symm
  exact (congrArg MatrixIso.linearEquiv hh).trans (D.external_oldEndpointPortFrame_eq q w q true g T)

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
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
local notation "ss" => BandGraft.oldPort A q B q true
local notation "pp" => (Subtype.val (BandGraft.oldPort A q B q true))
local notation "nn" => (Subtype.val (BandGraft.originalPort A q B (Fin.last (B).length) false))


lemma parent_selectedLastNamedColumns_snd
    (i : (j : Fin (arity q)) × Fin (D.childDim q j)) :
    (D.parent_selectedLastNamedColumns q w i).2.val = i.2.val := by
  unfold parent_selectedLastNamedColumns
  change ((C).external_portColumns nn ((D.parent_selectedLastPortColumns q w).symm i)).2.val = _
  rw [(C).external_portColumns_snd]
  exact external_sigmaFinCongr_symm_snd w.lastChild
    (fun c => ((C).vertexRanks (nn).1).rank (nn).2 (some c))
    (D.childDim q) (D.parent_selectedLastColumnRank q w) i

lemma parent_selectedPositiveNamedColumns_snd
    (i : (j : Fin (arity q)) × Fin (D.childDim q j)) :
    (D.external_oldEndpointNamedColumns q w q true i).2.val = i.2.val := by
  unfold external_oldEndpointNamedColumns
  change ((C).external_portColumns pp ((D.external_oldEndpointPortColumns q w q true).symm i)).2.val = _
  rw [(C).external_portColumns_snd]
  exact external_sigmaFinCongr_symm_snd (D.external_oldEndpointChild q true)
    (fun c => ((C).vertexRanks (pp).1).rank (pp).2 (some c))
    (D.childDim q) (D.external_oldEndpointChildRank q w q true) i

lemma parent_selectedCommonColumns_negative :
    D.parent_selectedCommonColumns q w =
      (D.parent_selectedLastNamedColumns q w).trans
        ((C).external_seamColumnsTransport
          (congrArg Prod.fst (D.parent_selectedNegativeAttach q w))) := by
  apply Equiv.ext
  intro i
  have hp := D.parent_selectedCommonColumns_grade q w i
  have hn := D.parent_selectedLastNamedColumns_grade q w i
  have he : (D.parent_selectedCommonColumns q w i).1 =
      (((D.parent_selectedLastNamedColumns q w).trans
        ((C).external_seamColumnsTransport
          (congrArg Prod.fst (D.parent_selectedNegativeAttach q w)))) i).1 := by
    apply Fin.ext
    exact hp.trans hn.symm
  apply Sigma.ext he
  apply (Fin.heq_ext_iff (congrArg ((C).childDim ss) he)).2
  have hp2 := D.parent_selectedPositiveNamedColumns_snd q w i
  have hn2 := D.parent_selectedLastNamedColumns_snd q w i
  have hpt := (C).external_seamColumnsTransport_snd
    (congrArg Prod.fst (D.parent_selectedPositiveAttach q w))
    (D.external_oldEndpointNamedColumns q w q true i)
  have hnt := (C).external_seamColumnsTransport_snd
    (congrArg Prod.fst (D.parent_selectedNegativeAttach q w))
      (D.parent_selectedLastNamedColumns q w i)
  exact (hpt.trans hp2).trans (hnt.trans hn2).symm

lemma parent_selectedNegativeEndpoint_eq
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    (((C).external_endpointNamedMatrix (D.namedCutPortFrames q w (D.portFrame g) T)
      nn ss false (D.parent_selectedNegativeAttach q w)).reindex
      (D.parent_selectedCommonColumns q w) (D.parent_selectedCommonParent q w)).linearEquiv =
        w.lastFrame := by
  have hp : D.parent_selectedCommonParent q w =
      (finCongr (D.parent_selectedLastPortParentRank q w)).symm.trans
        (finCongr (congrArg (fun z => (C).rank ((C).ports.facet ⟨z,none⟩))
          (congrArg Prod.fst (D.parent_selectedNegativeAttach q w)))) := by
    apply Equiv.ext
    intro i
    rfl
  have hh := (C).external_endpointNamedMatrix_normalized
    (D.namedCutPortFrames q w (D.portFrame g) T) nn ss false
    (D.parent_selectedNegativeAttach q w) (D.parent_selectedLastPortColumns q w).symm
    (finCongr (D.parent_selectedLastPortParentRank q w)).symm
  have hc := D.parent_selectedCommonColumns_negative q w
  have h1 := congrArg MatrixIso.linearEquiv hh
  erw [← hc,← hp] at h1
  exact h1.trans (D.parent_selectedLastPortFrame_eq q w (D.portFrame g) T)

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram

end


/- Local proof module: ParentSelectedSeam -/
section
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
local notation "ss" => BandGraft.oldPort A q B q true
local notation "pp" => Subtype.val (BandGraft.oldPort A q B q true)
local notation "nn" => Subtype.val (BandGraft.originalPort A q B (Fin.last (B).length) false)
local notation "e" => D.parent_selectedCommonColumns q w
local notation "f0" => D.parent_selectedCommonParent q w
lemma parent_selectedSeam
    {R : Type} [CommRing R] (φ : R →+* K)
    (v : (z : (C).Generator) →
      (Matrix (Fin ((C).generatorRank z)) (Fin ((C).generatorRank z)) K)ˣ)
    (g : (z : D.Generator) →
      (Matrix (Fin (D.generatorRank z)) (Fin (D.generatorRank z)) K)ˣ)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
    (J : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
    (hframes : ∀ p,(C).portFrame v p=D.namedCutPortFrames q w (D.portFrame g) T p)
    (hparent : (MatrixIso.unit (v (.side ⟨ss,none⟩))).reindex f0 f0=MatrixIso.unit J)
    (hchild : ((MatrixIso.block (fun j : Fin ((BandGraft.wiring A q B).seamArity ss) =>
      MatrixIso.unit (v (.side ⟨ss,some j⟩))⁻¹)).reindex e e).linearEquiv=
      D.namedChildInverse q g)
    (hflag : SameFramedFlag (fun i : (j : Fin (arity q)) × Fin (D.childDim q j) => i.1.val)
      (w.lastFrame.trans (MatrixIso.unit J).linearEquiv)
      ((D.namedChildInverse q g).trans (D.namedSeamFrame q (g (.frame q true))))) :
    SameFramedFlag ((C).seamGrade ss)
      (matrixUnitEquiv (((C).seamLeft ss).eval φ v))
      (matrixUnitEquiv (((C).seamRight ss).eval φ v)) := by
  have nframe : (((MatrixIso.unit (v (.frame ss false))).reindex
      (blockIndex ((C).childDim ss)).symm (finCongr ((C).seamRank ss))).reindex e f0).linearEquiv =
      w.lastFrame := by
    rw [← (C).external_endpointActualMatrix v _ hframes nn ss false
      (D.parent_selectedNegativeAttach q w)]
    exact D.parent_selectedNegativeEndpoint_eq q w g T
  have pframe : (((MatrixIso.unit (v (.frame ss true))).reindex
      (blockIndex ((C).childDim ss)).symm (finCongr ((C).seamRank ss))).reindex e f0).linearEquiv =
      D.namedSeamFrame q (g (.frame q true)) := by
    rw [← (C).external_endpointActualMatrix v _ hframes pp ss true
      (D.parent_selectedPositiveAttach q w)]
    exact D.parent_selectedPositiveEndpoint_eq q w g T
  apply (C).external_seam_of_commonCoordinates ss φ v e f0
  erw [nframe,pframe,hparent,hchild]
  have hgrade : (fun i => (e i).1.val)=(fun i => i.1.val) := by
    funext i
    exact D.parent_selectedCommonColumns_grade q w i
  rw [hgrade]
  exact hflag
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: ParentSelectedSideEndpointCoordinates -/
section
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
local notation "ss" => BandGraft.oldPort A q B q true
lemma parent_selectedSideColumns_eq :
    D.external_oldSideColumns q w.shape rfl w.rowRanks w.colRanks q =
      D.parent_selectedCommonColumns q w := by
  apply Equiv.ext
  intro i
  have he : (D.external_oldSideColumns q w.shape rfl w.rowRanks w.colRanks q i).1 =
      (D.parent_selectedCommonColumns q w i).1 := by
    apply Fin.ext
    exact (D.parent_selectedCommonColumns_grade q w i).symm
  apply Sigma.ext he
  apply (Fin.heq_ext_iff (congrArg ((C).childDim ss) he)).2
  have h1 := (C).external_seamColumnsTransport_snd
    (congrArg Prod.fst (D.parent_selectedPositiveAttach q w))
    (D.external_oldEndpointNamedColumns q w q true i)
  have h2 := D.parent_selectedPositiveNamedColumns_snd q w i
  exact (h1.trans h2).symm
lemma parent_selectedSideParent_eq :
    D.external_oldSideParent q w.shape rfl w.rowRanks w.colRanks q =
      D.parent_selectedCommonParent q w := by
  apply Equiv.ext
  intro i
  rfl
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: ParentSelectedFromSides -/
section
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
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "ss" => BandGraft.oldPort A q B q true
lemma parent_selectedSeam_fromSides
    {R : Type} [CommRing R] (φ : R →+* K)
    (v : (z : (C).Generator) →
      (Matrix (Fin ((C).generatorRank z)) (Fin ((C).generatorRank z)) K)ˣ)
    (g : (z : D.Generator) →
      (Matrix (Fin (D.generatorRank z)) (Fin (D.generatorRank z)) K)ˣ)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
    (hframes : ∀ p,(C).portFrame v p=D.namedCutPortFrames q w (D.portFrame g) T p)
    (hside : ∀ a, v (.side a)=D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks
      (fun a => g (.side a)) J Y a)
    (hflag : SameFramedFlag (fun i : (j : Fin (arity q)) × Fin (D.childDim q j) => i.1.val)
      (w.lastFrame.trans (MatrixIso.unit J).linearEquiv)
      ((D.namedChildInverse q g).trans (D.namedSeamFrame q (g (.frame q true))))) :
    SameFramedFlag ((C).seamGrade ss)
      (matrixUnitEquiv (((C).seamLeft ss).eval φ v))
      (matrixUnitEquiv (((C).seamRight ss).eval φ v)) := by
  apply D.parent_selectedSeam q w φ v g T J hframes
  · rw [hside]
    rw [← D.parent_selectedSideParent_eq q w]
    exact D.parent_selectedSideTransport q w.shape rfl w.rowRanks w.colRanks
      (fun a => g (.side a)) J Y
  · simp only [hside]
    rw [← D.parent_selectedSideColumns_eq q w]
    exact congrArg MatrixIso.linearEquiv
      (D.external_oldChildInverseTransport q w.shape rfl w.rowRanks w.colRanks q
        (fun a => g (.side a)) J Y)
  · exact hflag
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: ParentSelectedFlagAlgebra -/
section
namespace OAI.IntegralCharacterVarieties
noncomputable section
variable {R α V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  (a : α → ℕ)

lemma parent_sameFramedFlag_trans {e f g : (α → R) ≃ₗ[R] V}
    (h1 : SameFramedFlag a e f) (h2 : SameFramedFlag a f g) : SameFramedFlag a e g := by
  refine ⟨fun k => (h1.1 k).trans (h2.1 k), ?_⟩
  intro k v hv
  exact (h1.2 k v hv).trans (h2.2 k v (by rw [← h1.1 (k+1)]; exact hv))

lemma parent_sameFramedFlag_post {e f : (α → R) ≃ₗ[R] V}
    (h : SameFramedFlag a e f) (t : V ≃ₗ[R] W) :
    SameFramedFlag a (e.trans t) (f.trans t) := by
  apply (sameFramedFlag_iff a _ _).mpr
  have he : (e.trans t).trans (f.trans t).symm = e.trans f.symm := by
    apply LinearEquiv.ext
    intro v
    simp
  rw [he]
  exact (sameFramedFlag_iff a e f).mp h

lemma parent_selectedFlag_algebra
    {e f p : (α → R) ≃ₗ[R] V} (j : V ≃ₗ[R] V)
    (hfirst : SameFramedFlag a e (f.trans j.symm))
    (hseed : SameFramedFlag a f p) :
    SameFramedFlag a (e.trans j) p := by
  have hh := parent_sameFramedFlag_post a hfirst j
  have he : (f.trans j.symm).trans j = f := by
    apply LinearEquiv.ext
    intro v
    simp
  rw [he] at hh
  exact parent_sameFramedFlag_trans a hh hseed
end
end OAI.IntegralCharacterVarieties
end


/- Local proof module: ParentSelectedBandFlag -/
section
set_option maxHeartbeats 0
set_option quotPrecheck false
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K] [Algebra R K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (hg : 0 < D.genus (D.bandCutParent q))
    (P : D.Punctures R) (x : D.Solution P K)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
local notation "w" => D.producedCutBand q hg P x b0 i0
local notation "seed" => D.producedCutSeed q hg P x b0

lemma parent_selectedBandFlag :
    SameFramedFlag (fun i : (j : Fin (arity q)) × Fin (D.childDim q j) => i.1.val)
      ((w).lastFrame.trans (MatrixIso.unit (D.producedCutJ q hg P x b0 i0)).linearEquiv)
      ((D.namedChildInverse q seed).trans
        (D.namedSeamFrame q (seed (.frame q true)))) := by
  exact parent_selectedFlag_algebra _
    (MatrixIso.unit (D.producedCutJ q hg P x b0 i0)).linearEquiv
    (w).lastFrame_holds (D.producedCutSeed_namedSeam q hg P x b0 q)

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: ParentProducedSelectedSeamInferredV2 -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option quotPrecheck false
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable TwoFlagBand MatrixExpression HomTransport NamedBandGrades
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K] [Algebra R K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (hg : 0<D.genus (D.bandCutParent q))
    (P : D.Punctures R) (x : D.Solution P K)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
local notation "w" => D.producedCutBand q hg P x b0 i0
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q (w).shape)
local notation "B" => D.ports.refinedBandForSeam q (w).shape
local notation "CC" => D.refinedCutDiagram q (w).shape rfl (w).rowRanks (w).colRanks
local notation "MM" => D.producedMarkedDiagram q hproper hmax hg P x b0 i0
local notation "z" => D.producedMarkedValues q hproper hmax hg P x b0 i0
local notation "seed" => D.producedCutSeed q hg P x b0
local notation "cv" => D.external_markedAsCutValues q (w).shape rfl (w).rowRanks (w).colRanks hproper hmax z
local notation "J" => D.producedCutJ q hg P x b0 i0
local notation "T" => D.producedCutT q hg P x b0 i0
local notation "Y" => (T⁻¹*J⁻¹*(show (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
  (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ from seed (.side ⟨q,none⟩))*T)
local notation "ss" => BandGraft.oldPort A q B q true
def parent_producedSelectedSeamComplete :=
  D.external_markedSeam_of_cut q (w).shape rfl (w).rowRanks (w).colRanks
    hproper hmax z (algebraMap R K) ss
    (D.parent_selectedSeam_fromSides q w (algebraMap R K) cv seed (MatrixIso.unit T) J Y
      (D.parent_producedCutPortFrame q hproper hmax hg P x b0 i0)
      (D.parent_producedMarkedSideValue q hproper hmax hg P x b0 i0)
      (D.parent_selectedBandFlag q hg P x b0 i0))
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: MirrorPrincipalBridge -/
section
set_option maxHeartbeats 0

namespace OAI.IntegralCharacterVarieties.MatrixIso
noncomputable section
open scoped Classical
variable {R α β γ δ : Type*} [CommRing R] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
lemma external_reindex_injective (a : γ ≃ α) (b : δ ≃ β) :
    Function.Injective (fun x : MatrixIso R α β => x.reindex a b) := by
  intro x y h
  have hh := congrArg (fun z => z.reindex a.symm b.symm) h
  simpa only [reindex_reindex_eq, Equiv.symm_trans_self, reindex_refl_eq] using hh
end
end OAI.IntegralCharacterVarieties.MatrixIso

namespace OAI.IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
noncomputable section
open scoped Classical
open TwoFlagBand OccurrenceIncidence VertexTable
variable {K : Type} [Field K] {n r : ℕ} {s : Fin n → ℕ}
    {f h : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K)}
    (w : IdentifiedBand s f h)

lemma external_principal_color (v : Fin (w.shape.atomicBand.length+1))
    (p : (w.shape.atomicBand.kind v).table.Port)
    (hp : p=(w.shape.atomicBand.kind v).input ∨ p=(w.shape.atomicBand.kind v).output) :
    (w.shape.atomicBand.decoration v).color ⟨p,none⟩=none := by
  rcases hp with rfl|rfl
  · exact w.shape.atomicBand.parent_input v
  · exact w.shape.atomicBand.parent_output v

lemma external_principal_rank (v : Fin (w.shape.atomicBand.length+1))
    (p : (w.shape.atomicBand.kind v).table.Port)
    (hp : p=(w.shape.atomicBand.kind v).input ∨ p=(w.shape.atomicBand.kind v).output) :
    (w.shape.vertexAtoms v).rank ⟨p,none⟩=r :=
  (w.shape.vertexAtoms_rank v _).trans
    (congrArg (freshRank r w.shape.secondaryRank) (w.external_principal_color v p hp))

lemma external_mirror_basis_normalized (T : MatrixIso K (Fin r) (Fin r))
    (v : Fin (w.shape.atomicBand.length+1))
    (z : (p : (w.shape.atomicBand.kind v).table.Port) × Option ((w.shape.atomicBand.kind v).table.Child p))
    (hz : (w.shape.atomicBand.decoration v).color z=none)
    (hr : (w.shape.vertexAtoms v).mirror.rank ((w.shape.atomicBand.kind v).mirrorEnd z)=r) :
    ((w.mirrorVertexBases T v).basis ((w.shape.atomicBand.kind v).mirrorEnd z).1
      ((w.shape.atomicBand.kind v).mirrorEnd z).2).reindex
        (finCongr hr).symm (finCongr hr).symm =
      (w.colorGauge none).trans T.symm := by
  let e := (w.shape.atomicBand.kind v).mirrorEnd
  have hc : (w.shape.atomicBand.decoration v).color (e.symm (e z))=none :=
    (congrArg (w.shape.atomicBand.decoration v).color (e.symm_apply_apply z)).trans hz
  have hh := MatrixIso.finite_basis_transport (freshRank r w.shape.secondaryRank) (w.mirrorColorGauge T)
    none ((w.shape.atomicBand.decoration v).color (e.symm (e z)))
    r ((w.shape.vertexAtoms v).mirror.rank (e z))
    rfl (w.shape.vertexAtoms_rank v (e.symm (e z))) hc.symm hr.symm
  change (((w.mirrorColorGauge T ((w.shape.atomicBand.decoration v).color (e.symm (e z)))).reindex
    (finCongr (w.shape.vertexAtoms_rank v (e.symm (e z))))
    (finCongr (w.shape.vertexAtoms_rank v (e.symm (e z))))).reindex
    (finCongr hr.symm) (finCongr hr.symm))=(w.mirrorColorGauge T none)
  exact hh.trans (by apply MatrixIso.ext <;> rfl)

lemma external_mirror_principal_basis (T : MatrixIso K (Fin r) (Fin r))
    (v : Fin (w.shape.atomicBand.length+1))
    (p : (w.shape.atomicBand.kind v).table.Port)
    (hp : p=(w.shape.atomicBand.kind v).input ∨ p=(w.shape.atomicBand.kind v).output) :
    let ep := finCongr ((w.shape.vertexAtoms v).rank_of_atoms (w.shape.vertexAtoms v).mirror
      ((w.shape.vertexAtoms v).mirror_atoms ⟨p,none⟩).symm)
    ((w.mirrorVertexBases T v).basis ((w.shape.atomicBand.kind v).mirrorPort p) none).reindex ep ep =
      ((w.vertexBases v).basis p none).trans
        (T.symm.reindex (finCongr (w.external_principal_rank v p hp))
          (finCongr (w.external_principal_rank v p hp))) := by
  dsimp only
  let atom := w.shape.vertexAtoms v
  let k := w.shape.atomicBand.kind v
  let rankP := w.external_principal_rank v p hp
  let rankM := atom.rank_of_atoms atom.mirror (atom.mirror_atoms ⟨p,none⟩).symm
  let ep := finCongr rankM
  let er := finCongr rankP
  have hr : atom.mirror.rank (k.mirrorEnd ⟨p,none⟩)=r := rankM.symm.trans rankP
  have hn := w.external_mirror_basis_normalized T v ⟨p,none⟩
    (w.external_principal_color v p hp) hr
  have hb := w.basis_at_color v p none none (w.external_principal_color v p hp) rankP
  have tnorm : (T.symm.reindex er er).reindex er.symm er.symm=T.symm := by
    apply MatrixIso.ext <;> rfl
  have rhsNorm := MatrixIso.reindex_trans ((w.vertexBases v).basis p none)
    (T.symm.reindex er er) er.symm er.symm er.symm
  have rhsSimple : (((w.vertexBases v).basis p none).trans
      (T.symm.reindex er er)).reindex er.symm er.symm =
      (w.colorGauge none).trans T.symm :=
    rhsNorm.trans (congrArg₂ MatrixIso.trans hb tnorm)
  exact MatrixIso.external_reindex_injective er.symm er.symm (hn.trans rhsSimple.symm)

lemma external_mirror_principal_frame (T : MatrixIso K (Fin r) (Fin r))
    (v : Fin (w.shape.atomicBand.length+1))
    (p : (w.shape.atomicBand.kind v).table.Port)
    (hp : p=(w.shape.atomicBand.kind v).input ∨ p=(w.shape.atomicBand.kind v).output) :
    (w.mirrorVertexFrames T v ((w.shape.atomicBand.kind v).mirrorPort p)).reindex
      ((w.shape.vertexAtoms v).seamColumns (w.shape.vertexAtoms v).mirror
        p ((w.shape.atomicBand.kind v).mirrorPort p) ((w.shape.atomicBand.kind v).mirrorChild p)
        (fun a => ((w.shape.vertexAtoms v).mirror_atoms ⟨p,some a⟩).symm))
      (finCongr ((w.shape.vertexAtoms v).rank_of_atoms (w.shape.vertexAtoms v).mirror
        ((w.shape.vertexAtoms v).mirror_atoms ⟨p,none⟩).symm))=
      (w.vertexFrames v p).trans
        (T.symm.reindex (finCongr (w.external_principal_rank v p hp))
          (finCongr (w.external_principal_rank v p hp))) := by
  let D := w.shape.vertexAtoms v
  let E := D.mirror
  let G := w.vertexBases v
  let H := w.mirrorVertexBases T v
  let q := (w.shape.atomicBand.kind v).mirrorPort p
  let c := (w.shape.atomicBand.kind v).mirrorChild p
  let hc := fun a => (D.mirror_atoms ⟨p,some a⟩).symm
  let ec := D.seamColumns E p q c hc
  have hb : (H.columns q).reindex ec ec=G.columns p := by
    change (MatrixIso.block _).reindex (Equiv.sigmaCongr _ _) (Equiv.sigmaCongr _ _)=_
    rw [MatrixIso.block_reindex_sigma]
    apply congrArg MatrixIso.block
    funext a
    exact w.mirror_basis T v ⟨p,some a⟩ (w.child_color_ne v p a)
  change ((H.columns q).symm.trans (E.frame q) |>.trans (H.basis q none)).reindex _ _=_
  rw [MatrixIso.bases_reindex, hb,
    D.frame_reindex E p q c (D.mirror_atoms ⟨p,none⟩).symm hc]
  have hpB := w.external_mirror_principal_basis T v p hp
  dsimp only at hpB
  exact (congrArg (fun b => ((G.columns p).symm.trans (D.frame p)).trans b) hpB).trans
    (MatrixIso.trans_assoc _ _ _).symm

end
end OAI.IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand

end


/- Local proof module: ParentMirrorPrincipalNormalizedV2 -/
section
set_option maxHeartbeats 0
namespace OAI.IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
noncomputable section
open scoped Classical Matrix
open TwoFlagBand OccurrenceIncidence VertexTable
variable {K : Type} [Field K] {n r : ℕ} {s : Fin n → ℕ}
    {f h : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K)}
    (w : IdentifiedBand s f h)

lemma parent_mirrorPrincipalNormalized
    (T : MatrixIso K (Fin r) (Fin r))
    (v : Fin (w.shape.atomicBand.length+1))
    (p : (w.shape.atomicBand.kind v).table.Port)
    (hp : p=(w.shape.atomicBand.kind v).input ∨ p=(w.shape.atomicBand.kind v).output)
    (e : (w.shape.vertexAtoms v).localRanks.Columns p ≃ ((i : Fin n) × Fin (s i))) :
    (((w.mirrorVertexFrames T v ((w.shape.atomicBand.kind v).mirrorPort p)).reindex
      (e.symm.trans ((w.shape.vertexAtoms v).seamColumns (w.shape.vertexAtoms v).mirror
        p ((w.shape.atomicBand.kind v).mirrorPort p) ((w.shape.atomicBand.kind v).mirrorChild p)
        (fun a => ((w.shape.vertexAtoms v).mirror_atoms ⟨p,some a⟩).symm)))
      ((finCongr (w.external_principal_rank v p hp)).symm.trans
        (finCongr ((w.shape.vertexAtoms v).rank_of_atoms (w.shape.vertexAtoms v).mirror
          ((w.shape.vertexAtoms v).mirror_atoms ⟨p,none⟩).symm)))).linearEquiv) =
    (((w.vertexFrames v p).reindex e.symm
      (finCongr (w.external_principal_rank v p hp)).symm).linearEquiv).trans
      T.linearEquiv.symm := by
  letI : Fintype ((w.shape.vertexAtoms v).localRanks.Columns p) :=
    (w.shape.vertexAtoms v).localRanks.fintypeColumns p
  have hh := w.external_mirror_principal_frame T v p hp
  have hz := congrArg (fun M => (M.reindex e.symm
    (finCongr (w.external_principal_rank v p hp)).symm).linearEquiv) hh
  rw [MatrixIso.reindex_reindex_eq] at hz
  have hr := MatrixIso.reindex_trans (w.vertexFrames v p)
    (T.symm.reindex (finCongr (w.external_principal_rank v p hp))
      (finCongr (w.external_principal_rank v p hp))) e.symm
    (finCongr (w.external_principal_rank v p hp)).symm
    (finCongr (w.external_principal_rank v p hp)).symm
  have ht : (T.symm.reindex (finCongr (w.external_principal_rank v p hp))
      (finCongr (w.external_principal_rank v p hp))).reindex
        (finCongr (w.external_principal_rank v p hp)).symm
        (finCongr (w.external_principal_rank v p hp)).symm = T.symm := by
    rw [MatrixIso.reindex_reindex_eq, Equiv.symm_trans_self, MatrixIso.reindex_refl_eq]
  have hlin : T.symm.linearEquiv=T.linearEquiv.symm := by rfl
  erw [hr,ht] at hz
  have hcomp : ((w.vertexFrames v p).reindex e.symm
      (finCongr (w.external_principal_rank v p hp)).symm |>.trans T.symm).linearEquiv =
      (((w.vertexFrames v p).reindex e.symm
        (finCongr (w.external_principal_rank v p hp)).symm).linearEquiv).trans T.linearEquiv.symm := by
    apply LinearEquiv.ext
    intro x
    exact MatrixIso.linearEquiv_trans_apply _ _ x
  exact hz.trans hcomp
end
end OAI.IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
end


/- Local proof module: ParentWrapRawFrames -/
section
set_option maxHeartbeats 0
namespace OAI.IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
noncomputable section
open scoped Classical Matrix
open TwoFlagBand OccurrenceIncidence VertexTable
variable {K : Type} [Field K] {n r : ℕ} {s : Fin n → ℕ}
    {f h : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K)}
    (w : IdentifiedBand s f h)

def parent_mirrorFirstColumns : ((i : Fin n) × Fin (s i)) ≃
    (w.shape.vertexAtoms 0).mirror.localRanks.Columns
      ((w.shape.atomicBand.kind 0).mirrorPort (w.shape.atomicBand.kind 0).input) :=
  w.firstColumns.symm.trans ((w.shape.vertexAtoms 0).seamColumns (w.shape.vertexAtoms 0).mirror
    (w.shape.atomicBand.kind 0).input
    ((w.shape.atomicBand.kind 0).mirrorPort (w.shape.atomicBand.kind 0).input)
    ((w.shape.atomicBand.kind 0).mirrorChild _)
    (fun a => ((w.shape.vertexAtoms 0).mirror_atoms ⟨(w.shape.atomicBand.kind 0).input,some a⟩).symm))
def parent_mirrorFirstParent : Fin r ≃
    (w.shape.vertexAtoms 0).mirror.localRanks.Parent
      ((w.shape.atomicBand.kind 0).mirrorPort (w.shape.atomicBand.kind 0).input) :=
  (finCongr w.firstParent_rank).symm.trans
    (finCongr ((w.shape.vertexAtoms 0).rank_of_atoms (w.shape.vertexAtoms 0).mirror
      ((w.shape.vertexAtoms 0).mirror_atoms ⟨(w.shape.atomicBand.kind 0).input,none⟩).symm))
lemma parent_mirrorFirstFrame (T : MatrixIso K (Fin r) (Fin r)) :
    ((w.mirrorVertexFrames T 0
      ((w.shape.atomicBand.kind 0).mirrorPort (w.shape.atomicBand.kind 0).input)).reindex
      (w.parent_mirrorFirstColumns) (w.parent_mirrorFirstParent)).linearEquiv =
      w.firstFrame.trans T.linearEquiv.symm := by
  exact w.parent_mirrorPrincipalNormalized T 0 (w.shape.atomicBand.kind 0).input
    (Or.inl rfl) w.firstColumns

def parent_mirrorLastColumns : ((i : Fin n) × Fin (s i)) ≃
    (w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).mirror.localRanks.Columns
      ((w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).mirrorPort (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output) :=
  w.lastColumns.symm.trans ((w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).seamColumns (w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).mirror
    (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output
    ((w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).mirrorPort (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output)
    ((w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).mirrorChild _)
    (fun a => ((w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).mirror_atoms ⟨(w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output,some a⟩).symm))
def parent_mirrorLastParent : Fin r ≃
    (w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).mirror.localRanks.Parent
      ((w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).mirrorPort (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output) :=
  (finCongr w.lastParent_rank).symm.trans
    (finCongr ((w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).rank_of_atoms (w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).mirror
      ((w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).mirror_atoms ⟨(w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output,none⟩).symm))
lemma parent_mirrorLastFrame (T : MatrixIso K (Fin r) (Fin r)) :
    ((w.mirrorVertexFrames T (Fin.last w.shape.atomicBand.length)
      ((w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).mirrorPort (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output)).reindex
      (w.parent_mirrorLastColumns) (w.parent_mirrorLastParent)).linearEquiv =
      w.lastFrame.trans T.linearEquiv.symm := by
  exact w.parent_mirrorPrincipalNormalized T (Fin.last w.shape.atomicBand.length) (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output
    (Or.inr rfl) w.lastColumns

end
end OAI.IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
end


/- Local proof module: ParentWrapPortFrames -/
section
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
end


/- Local proof module: ParentWrapEndpoints -/
section
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

def parent_wrapFirstNamedColumns : ((i : Fin (arity q)) × Fin (D.childDim q i)) ≃
    ((i : Fin ((BandGraft.wiring A q B).seamArity ss)) × Fin ((C).childDim ss i)) :=
  ((D.parent_wrapFirstPortColumns q w).trans ((C).external_portColumns nn)).trans
    ((C).external_seamColumnsTransport (congrArg Prod.fst (D.parent_wrapNegativeAttach q w)))
lemma parent_wrapFirstNamedColumns_grade
    (i : (j : Fin (arity q)) × Fin (D.childDim q j)) :
    (D.parent_wrapFirstNamedColumns q w i).1.val = i.1.val := by
  change (((w.shape.atomicBand.kind 0).mirror.childEnumeration
      ((w.shape.atomicBand.kind 0).mirrorPort (w.shape.atomicBand.kind 0).input))
      (((w.shape.atomicBand.kind 0).mirrorChild _) (w.firstChild.symm i.1))).val = _
  rw [Kind.mirror_childEnumeration]
  change (w.firstChild (w.firstChild.symm i.1)).val = i.1.val
  rw [Equiv.apply_symm_apply]
lemma parent_wrapFirstNamedColumns_snd
    (i : (j : Fin (arity q)) × Fin (D.childDim q j)) :
    (D.parent_wrapFirstNamedColumns q w i).2.val = i.2.val := by
  change (w.firstColumns.symm i).2.val = i.2.val
  exact external_sigmaFinCongr_symm_snd w.firstChild _ _ (w.firstChild_rank) i

def parent_wrapLastNamedColumns : ((i : Fin (arity q)) × Fin (D.childDim q i)) ≃
    ((i : Fin ((BandGraft.wiring A q B).seamArity ss)) × Fin ((C).childDim ss i)) :=
  ((D.parent_wrapLastPortColumns q w).trans ((C).external_portColumns pp)).trans
    ((C).external_seamColumnsTransport (congrArg Prod.fst (D.parent_wrapPositiveAttach q w)))
lemma parent_wrapLastNamedColumns_grade
    (i : (j : Fin (arity q)) × Fin (D.childDim q j)) :
    (D.parent_wrapLastNamedColumns q w i).1.val = i.1.val := by
  change (((w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).mirror.childEnumeration
      ((w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).mirrorPort (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output))
      (((w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).mirrorChild _) (w.lastChild.symm i.1))).val = _
  rw [Kind.mirror_childEnumeration]
  change (w.lastChild (w.lastChild.symm i.1)).val = i.1.val
  rw [Equiv.apply_symm_apply]
lemma parent_wrapLastNamedColumns_snd
    (i : (j : Fin (arity q)) × Fin (D.childDim q j)) :
    (D.parent_wrapLastNamedColumns q w i).2.val = i.2.val := by
  change (w.lastColumns.symm i).2.val = i.2.val
  exact external_sigmaFinCongr_symm_snd w.lastChild _ _ (w.lastChild_rank) i

def parent_wrapCommonParent :=
  (D.parent_wrapFirstPortParent q w).trans
    (finCongr (congrArg (fun z => (C).rank ((C).ports.facet ⟨z,none⟩))
      (congrArg Prod.fst (D.parent_wrapNegativeAttach q w))))
lemma parent_wrapNamedColumns_eq :
    D.parent_wrapFirstNamedColumns q w=D.parent_wrapLastNamedColumns q w := by
  apply Equiv.ext
  intro i
  have he : (D.parent_wrapFirstNamedColumns q w i).1=(D.parent_wrapLastNamedColumns q w i).1 := by
    apply Fin.ext
    exact (D.parent_wrapFirstNamedColumns_grade q w i).trans
      (D.parent_wrapLastNamedColumns_grade q w i).symm
  apply Sigma.ext he
  apply (Fin.heq_ext_iff (congrArg ((C).childDim ss) he)).2
  exact (D.parent_wrapFirstNamedColumns_snd q w i).trans
    (D.parent_wrapLastNamedColumns_snd q w i).symm
lemma parent_wrapCommonParent_positive :
    D.parent_wrapCommonParent q w =
      (D.parent_wrapLastPortParent q w).trans
        (finCongr (congrArg (fun z => (C).rank ((C).ports.facet ⟨z,none⟩))
          (congrArg Prod.fst (D.parent_wrapPositiveAttach q w)))) := by
  apply Equiv.ext
  intro i
  rfl

lemma parent_wrapNegativeEndpoint (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    (((C).external_endpointNamedMatrix (D.namedCutPortFrames q w old T)
      nn ss false (D.parent_wrapNegativeAttach q w)).reindex
      (D.parent_wrapFirstNamedColumns q w) (D.parent_wrapCommonParent q w)).linearEquiv =
      w.firstFrame.trans T.linearEquiv.symm := by
  have hh := (C).external_endpointNamedMatrix_normalized
    (D.namedCutPortFrames q w old T) nn ss false (D.parent_wrapNegativeAttach q w)
    (D.parent_wrapFirstPortColumns q w) (D.parent_wrapFirstPortParent q w)
  exact (congrArg MatrixIso.linearEquiv hh).trans (D.parent_wrapFirstPortFrame q w old T)

lemma parent_wrapPositiveEndpoint (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    (((C).external_endpointNamedMatrix (D.namedCutPortFrames q w old T)
      pp ss true (D.parent_wrapPositiveAttach q w)).reindex
      (D.parent_wrapFirstNamedColumns q w) (D.parent_wrapCommonParent q w)).linearEquiv =
      w.lastFrame.trans T.linearEquiv.symm := by
  erw [D.parent_wrapNamedColumns_eq q w,D.parent_wrapCommonParent_positive q w]
  have hh := (C).external_endpointNamedMatrix_normalized
    (D.namedCutPortFrames q w old T) pp ss true (D.parent_wrapPositiveAttach q w)
    (D.parent_wrapLastPortColumns q w) (D.parent_wrapLastPortParent q w)
  exact (congrArg MatrixIso.linearEquiv hh).trans (D.parent_wrapLastPortFrame q w old T)

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: ParentWrapSeam -/
section
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
local notation "e" => D.parent_wrapFirstNamedColumns q w
local notation "f0" => D.parent_wrapCommonParent q w
lemma parent_wrapSeam
    {R : Type} [CommRing R] (φ : R →+* K)
    (g : (z : (C).Generator) →
      (Matrix (Fin ((C).generatorRank z)) (Fin ((C).generatorRank z)) K)ˣ)
    (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
    (Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
    (hframes : ∀ p,(C).portFrame g p=D.namedCutPortFrames q w old T p)
    (hparent : (MatrixIso.unit (g (.side ⟨ss,none⟩))).reindex f0 f0=MatrixIso.unit Y)
    (hchild : ((MatrixIso.block (fun j : Fin ((BandGraft.wiring A q B).seamArity ss) =>
      MatrixIso.unit (g (.side ⟨ss,some j⟩))⁻¹)).reindex e e).linearEquiv=
      LinearEquiv.refl K _)
    (hflag : SameFramedFlag (fun i : (j : Fin (arity q)) × Fin (D.childDim q j) => i.1.val)
      ((w.firstFrame.trans T.linearEquiv.symm).trans (MatrixIso.unit Y).linearEquiv)
      (w.lastFrame.trans T.linearEquiv.symm)) :
    SameFramedFlag ((C).seamGrade ss)
      (matrixUnitEquiv (((C).seamLeft ss).eval φ g))
      (matrixUnitEquiv (((C).seamRight ss).eval φ g)) := by
  have nframe : (((MatrixIso.unit (g (.frame ss false))).reindex
      (blockIndex ((C).childDim ss)).symm (finCongr ((C).seamRank ss))).reindex e f0).linearEquiv =
      w.firstFrame.trans T.linearEquiv.symm := by
    rw [← (C).external_endpointActualMatrix g _ hframes nn ss false
      (D.parent_wrapNegativeAttach q w)]
    exact D.parent_wrapNegativeEndpoint q w old T
  have pframe : (((MatrixIso.unit (g (.frame ss true))).reindex
      (blockIndex ((C).childDim ss)).symm (finCongr ((C).seamRank ss))).reindex e f0).linearEquiv =
      w.lastFrame.trans T.linearEquiv.symm := by
    rw [← (C).external_endpointActualMatrix g _ hframes pp ss true
      (D.parent_wrapPositiveAttach q w)]
    exact D.parent_wrapPositiveEndpoint q w old T
  apply (C).external_seam_of_commonCoordinates ss φ g e f0
  erw [nframe,pframe,hparent,hchild]
  have hgrade : (fun i => (e i).1.val)=(fun i => i.1.val) := by
    funext i
    exact D.parent_wrapFirstNamedColumns_grade q w i
  rw [hgrade]
  simpa only [LinearEquiv.refl_trans] using hflag
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: ParentWrapSideTransport -/
section
set_option maxHeartbeats 0
set_option quotPrecheck false
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {r : ℕ} (d : TwoFlagBand.RankShape (arity q) (arity q) r)
    (hp : D.rank (D.ports.facet ⟨q,none⟩)=r)
    (hc : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.row i))
    (hc' : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.col i))
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q d)
local notation "B" => D.ports.refinedBandForSeam q d
local notation "C" => D.refinedCutDiagram q d hp hc hc'
local notation "ss" => BandGraft.mirrorOutput A q B (Fin.last (B).length)

lemma parent_wrapSideArity : (BandGraft.wiring A q B).seamArity ss = arity q :=
  graftLabelArity_short A (B).doublePatch (doubleDecoration (B).decoration) q
    ((B).patch.double_signatureMatch (B).decoration (B).patch_signatureMatch (B).shortFirst (B).shortLast)
    (fun i => by rw [(B).double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [(B).double_signature_minus]; cases i <;> rfl) true

lemma parent_wrapSideRank (i : Option (Fin (arity q))) :
    (C).rank ((C).ports.facet ⟨ss,i.map (finCongr (D.parent_wrapSideArity q d).symm)⟩) =
      D.rank (D.ports.facet ⟨q,i⟩) := by
  exact congrArg (D.ports.refinedRank q d D.rank)
    (graft_short_color A (B).doublePatch (doubleDecoration (B).decoration) q
      ((B).patch.double_signatureMatch (B).decoration (B).patch_signatureMatch (B).shortFirst (B).shortLast)
      (fun i => by rw [(B).double_signature_plus]; cases i <;> rfl)
      (fun i => by rw [(B).double_signature_minus]; cases i <;> rfl) true i)

lemma parent_wrapSideValue
    (old : D.SideValues (R:=K))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
    (i : Option (Fin (arity q))) :
    rebaseUnit (D.parent_wrapSideRank q d hp hc hc' i)
      (D.refinedCutSideValues q d hp hc hc' old J Y
        ⟨ss,i.map (finCongr (D.parent_wrapSideArity q d).symm)⟩) =
      D.cutShortSideValues q Y true i := by
  exact graftSideValues_short A (B).doublePatch (doubleDecoration (B).decoration) q
    ((B).patch.double_signatureMatch (B).decoration (B).patch_signatureMatch (B).shortFirst (B).shortLast)
    (fun i => by rw [(B).double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [(B).double_signature_minus]; cases i <;> rfl)
    (D.ports.refinedRank q d D.rank) (D.cutOldSideValues q old J)
    (D.cutShortSideValues q Y) true i

def parent_wrapSideColumns : ((i : Fin (arity q)) × Fin (D.childDim q i)) ≃
    ((j : Fin ((BandGraft.wiring A q B).seamArity ss)) × Fin ((C).childDim ss j)) :=
  Equiv.sigmaCongr (finCongr (D.parent_wrapSideArity q d).symm)
    (fun i => finCongr (D.parent_wrapSideRank q d hp hc hc' (some i)).symm)
def parent_wrapSideParent := (finCongr (D.parent_wrapSideRank q d hp hc hc' none)).symm

lemma parent_wrapParentTransport
    (old : D.SideValues (R:=K))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ) :
    (MatrixIso.unit (D.refinedCutSideValues q d hp hc hc' old J Y ⟨ss,none⟩)).reindex
      (D.parent_wrapSideParent q d hp hc hc')
      (D.parent_wrapSideParent q d hp hc hc') = MatrixIso.unit Y := by
  have h := D.parent_wrapSideValue q d hp hc hc' old J Y none
  change rebaseUnit _ _ = Y at h
  have hi := rebaseUnit_iso (D.parent_wrapSideRank q d hp hc hc' none)
    (D.refinedCutSideValues q d hp hc hc' old J Y ⟨ss,none⟩)
  erw [h] at hi
  exact hi.symm

lemma parent_wrapChildInverseTransport
    (old : D.SideValues (R:=K))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ) :
    (MatrixIso.block (fun j : Fin ((BandGraft.wiring A q B).seamArity ss) =>
      MatrixIso.unit (D.refinedCutSideValues q d hp hc hc' old J Y ⟨ss,some j⟩)⁻¹)).reindex
      (D.parent_wrapSideColumns q d hp hc hc')
      (D.parent_wrapSideColumns q d hp hc hc') =
      MatrixIso.block (fun i : Fin (arity q) =>
        MatrixIso.unit (1 : (Matrix (Fin (D.childDim q i)) (Fin (D.childDim q i)) K)ˣ)) := by
  erw [MatrixIso.block_reindex_sigma]
  congr 1
  funext i
  have h := D.parent_wrapSideValue q d hp hc hc' old J Y (some i)
  change rebaseUnit _ _ = 1 at h
  have hi := rebaseUnit_iso (D.parent_wrapSideRank q d hp hc hc' (some i))
    ((D.refinedCutSideValues q d hp hc hc' old J Y
      ⟨ss,some ((finCongr (D.parent_wrapSideArity q d).symm) i)⟩)⁻¹)
  erw [map_inv, h, inv_one] at hi
  exact hi.symm

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: ParentBlockIdentity -/
section
set_option maxHeartbeats 0
namespace OAI.IntegralCharacterVarieties.MatrixIso
noncomputable section
open scoped Classical Matrix
variable {K ι : Type*} [Field K] [Fintype ι] {d : ι → Type*} [∀ i,Fintype (d i)] [∀ i,DecidableEq (d i)]
lemma parent_blockUnitOne_linear :
    (MatrixIso.block (fun i : ι =>
      MatrixIso.unit (1 : (Matrix (d i) (d i) K)ˣ))).linearEquiv =
      LinearEquiv.refl K _ := by
  have hv : (MatrixIso.block (fun i : ι =>
      MatrixIso.unit (1 : (Matrix (d i) (d i) K)ˣ))).val=1 := by
    simp only [MatrixIso.block, MatrixIso.unit, Units.val_one]
    exact Matrix.blockDiagonal'_one
  apply LinearEquiv.ext
  intro v
  exact (congrArg (fun M : Matrix _ _ K => M *ᵥ v) hv).trans (Matrix.one_mulVec v)
end
end OAI.IntegralCharacterVarieties.MatrixIso
end


/- Local proof module: ParentWrapSideEndpointCoordinates -/
section
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
lemma parent_wrapSideColumns_eq :
    D.parent_wrapSideColumns q w.shape rfl w.rowRanks w.colRanks =
      D.parent_wrapFirstNamedColumns q w := by
  apply Equiv.ext
  intro i
  have he : (D.parent_wrapSideColumns q w.shape rfl w.rowRanks w.colRanks i).1 =
      (D.parent_wrapFirstNamedColumns q w i).1 := by
    apply Fin.ext
    exact (D.parent_wrapFirstNamedColumns_grade q w i).symm
  apply Sigma.ext he
  apply (Fin.heq_ext_iff (congrArg ((C).childDim ss) he)).2
  exact (D.parent_wrapFirstNamedColumns_snd q w i).symm
lemma parent_wrapSideParent_eq :
    D.parent_wrapSideParent q w.shape rfl w.rowRanks w.colRanks =
      D.parent_wrapCommonParent q w := by
  apply Equiv.ext
  intro i
  rfl
lemma parent_wrapChildIdentity
    (old : D.SideValues (R:=K))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ) :
    ((MatrixIso.block (fun j : Fin ((BandGraft.wiring A q B).seamArity ss) =>
      MatrixIso.unit (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks old J Y
        ⟨ss,some j⟩)⁻¹)).reindex
      (D.parent_wrapFirstNamedColumns q w) (D.parent_wrapFirstNamedColumns q w)).linearEquiv=
      LinearEquiv.refl K _ := by
  rw [← D.parent_wrapSideColumns_eq q w]
  rw [D.parent_wrapChildInverseTransport q w.shape rfl w.rowRanks w.colRanks old J Y]
  exact MatrixIso.parent_blockUnitOne_linear (K:=K) (ι:=Fin (arity q))
    (d:=fun i => Fin (D.childDim q i))

end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: ParentWrapFromSides -/
section
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
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "ss" => BandGraft.mirrorOutput A q B (Fin.last (B).length)
lemma parent_wrapSeam_fromSides
    {R : Type} [CommRing R] (φ : R →+* K)
    (v : (z : (C).Generator) →
      (Matrix (Fin ((C).generatorRank z)) (Fin ((C).generatorRank z)) K)ˣ)
    (g : (z : D.Generator) →
      (Matrix (Fin (D.generatorRank z)) (Fin (D.generatorRank z)) K)ˣ)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
    (hframes : ∀ p,(C).portFrame v p=D.namedCutPortFrames q w (D.portFrame g) T p)
    (hside : ∀ a, v (.side a)=D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks
      (fun a => g (.side a)) J Y a)
    (hflag : SameFramedFlag (fun i : (j : Fin (arity q)) × Fin (D.childDim q j) => i.1.val)
      ((w.firstFrame.trans T.linearEquiv.symm).trans (MatrixIso.unit Y).linearEquiv)
      (w.lastFrame.trans T.linearEquiv.symm)) :
    SameFramedFlag ((C).seamGrade ss)
      (matrixUnitEquiv (((C).seamLeft ss).eval φ v))
      (matrixUnitEquiv (((C).seamRight ss).eval φ v)) := by
  apply D.parent_wrapSeam q w φ v (D.portFrame g) T Y hframes
  · rw [hside]
    rw [← D.parent_wrapSideParent_eq q w]
    exact D.parent_wrapParentTransport q w.shape rfl w.rowRanks w.colRanks
      (fun a => g (.side a)) J Y
  · simp only [hside]
    exact D.parent_wrapChildIdentity q w (fun a => g (.side a)) J Y
  · exact hflag
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: ParentWrapFlagAlgebra -/
section
namespace OAI.IntegralCharacterVarieties
noncomputable section
variable {R α V : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] (a : α → ℕ)

lemma parent_wrapFlag_algebra
    {f l : (α → R) ≃ₗ[R] V} (p j t : V ≃ₗ[R] V)
    (h : SameFramedFlag a l ((f.trans p).trans j.symm)) :
    SameFramedFlag a
      ((f.trans t.symm).trans (((t.trans p).trans j.symm).trans t.symm))
      (l.trans t.symm) := by
  have hs : SameFramedFlag a ((f.trans p).trans j.symm) l := by
    refine ⟨fun k => (h.1 k).symm, ?_⟩
    intro k v hv
    exact (h.2 k v (by rw [h.1 (k+1)]; exact hv)).symm
  have hp := parent_sameFramedFlag_post a hs t.symm
  have he : (f.trans t.symm).trans (((t.trans p).trans j.symm).trans t.symm) =
      ((f.trans p).trans j.symm).trans t.symm := by
    apply LinearEquiv.ext
    intro v
    simp
  rw [he]
  exact hp
end
end OAI.IntegralCharacterVarieties
end


/- Local proof module: ParentWrapBandFlagV3 -/
section
set_option maxHeartbeats 0
namespace OAI.IntegralCharacterVarieties
noncomputable section
open scoped Classical Matrix
variable {K α β : Type*} [Field K] [Fintype β] [DecidableEq β]

lemma parent_wrapUnitFlag (a : α → ℕ)
    (f l : (α → K) ≃ₗ[K] (β → K))
    (P J T : (Matrix β β K)ˣ)
    (h : SameFramedFlag a l
      ((f.trans (MatrixIso.unit P).linearEquiv).trans (MatrixIso.unit J).linearEquiv.symm)) :
    SameFramedFlag a
      ((f.trans (MatrixIso.unit T).linearEquiv.symm).trans
        (MatrixIso.unit (T⁻¹*J⁻¹*P*T)).linearEquiv)
      (l.trans (MatrixIso.unit T).linearEquiv.symm) := by
  have hy : (MatrixIso.unit (T⁻¹*J⁻¹*P*T)).linearEquiv =
      (((MatrixIso.unit T).linearEquiv.trans (MatrixIso.unit P).linearEquiv).trans
        (MatrixIso.unit J).linearEquiv.symm).trans (MatrixIso.unit T).linearEquiv.symm := by
    simp only [MatrixIso.unit_mul, MatrixIso.unit_inv]
    apply LinearEquiv.ext
    intro v
    simp only [MatrixIso.linearEquiv_trans_apply, LinearEquiv.trans_apply]
    rfl
  rw [hy]
  exact parent_wrapFlag_algebra a (MatrixIso.unit P).linearEquiv
    (MatrixIso.unit J).linearEquiv (MatrixIso.unit T).linearEquiv h
end
end OAI.IntegralCharacterVarieties
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K] [Algebra R K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (hg : 0 < D.genus (D.bandCutParent q))
    (P : D.Punctures R) (x : D.Solution P K)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
local notation "w" => D.producedCutBand q hg P x b0 i0
local notation "g" => D.producedCutSeed q hg P x b0
local notation "J" => D.producedCutJ q hg P x b0 i0
local notation "T" => D.producedCutT q hg P x b0 i0
lemma parent_producedWrapFlag :
    SameFramedFlag (fun i : (j : Fin (arity q)) × Fin (D.childDim q j) => i.1.val)
      (((w).firstFrame.trans (MatrixIso.unit T).linearEquiv.symm).trans
        (MatrixIso.unit (T⁻¹*J⁻¹*(show (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
          (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ from g (.side ⟨q,none⟩))*T)).linearEquiv)
      ((w).lastFrame.trans (MatrixIso.unit T).linearEquiv.symm) := by
  have h := (w).lastFrame_holds
  have hf := (w).firstFrame_holds
  have hh := parent_sameFramedFlag_post _ hf (D.namedParentLinear q g)
  have hh' := parent_sameFramedFlag_post _ hh (MatrixIso.unit J).linearEquiv.symm
  have hsym : SameFramedFlag (fun i : (j : Fin (arity q)) × Fin (D.childDim q j) => i.1.val)
      (((D.namedSeamFrame q (g (.frame q false))).trans
          (D.namedParentLinear q g)).trans (MatrixIso.unit J).linearEquiv.symm)
      (((w).firstFrame.trans (D.namedParentLinear q g)).trans
          (MatrixIso.unit J).linearEquiv.symm) := by
    refine ⟨fun k => (hh'.1 k).symm, ?_⟩
    intro k v hv
    exact (hh'.2 k v (by rw [hh'.1 (k+1)]; exact hv)).symm
  exact parent_wrapUnitFlag _ (w).firstFrame (w).lastFrame
    ((show (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
          (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ from g (.side ⟨q,none⟩))) J T (parent_sameFramedFlag_trans _ h hsym)
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: ParentProducedWrapSeamInferredV2 -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option quotPrecheck false
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable TwoFlagBand MatrixExpression HomTransport NamedBandGrades
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K] [Algebra R K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (hg : 0<D.genus (D.bandCutParent q))
    (P : D.Punctures R) (x : D.Solution P K)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
local notation "w" => D.producedCutBand q hg P x b0 i0
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q (w).shape)
local notation "B" => D.ports.refinedBandForSeam q (w).shape
local notation "CC" => D.refinedCutDiagram q (w).shape rfl (w).rowRanks (w).colRanks
local notation "MM" => D.producedMarkedDiagram q hproper hmax hg P x b0 i0
local notation "z" => D.producedMarkedValues q hproper hmax hg P x b0 i0
local notation "seed" => D.producedCutSeed q hg P x b0
local notation "cv" => D.external_markedAsCutValues q (w).shape rfl (w).rowRanks (w).colRanks hproper hmax z
local notation "J" => D.producedCutJ q hg P x b0 i0
local notation "T" => D.producedCutT q hg P x b0 i0
local notation "Y" => (T⁻¹*J⁻¹*(show (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
  (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ from seed (.side ⟨q,none⟩))*T)
local notation "ss" => BandGraft.mirrorOutput A q B (Fin.last (B).length)
def parent_producedWrapSeamComplete :=
  D.external_markedSeam_of_cut q (w).shape rfl (w).rowRanks (w).colRanks
    hproper hmax z (algebraMap R K) ss
    (D.parent_wrapSeam_fromSides q w (algebraMap R K) cv seed (MatrixIso.unit T) J Y
      (D.parent_producedCutPortFrame q hproper hmax hg P x b0 i0)
      (D.parent_producedMarkedSideValue q hproper hmax hg P x b0 i0)
      (D.parent_producedWrapFlag q hg P x b0 i0))
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


/- Local proof module: AllSeamsAssemblyInferredV2 -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option quotPrecheck false
namespace OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
noncomputable section
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K] [Algebra R K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (hg : 0<D.genus (D.bandCutParent q))
    (P : D.Punctures R) (x : D.Solution P K)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
local notation "w" => D.producedCutBand q hg P x b0 i0
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q (w).shape)
local notation "B" => D.ports.refinedBandForSeam q (w).shape
local notation "C" => D.producedMarkedDiagram q hproper hmax hg P x b0 i0
local notation "v" => D.producedMarkedValues q hproper hmax hg P x b0 i0
local notation "ss" => BandGraft.originalPort A q B 0 true
local notation "CC" => D.refinedCutDiagram q (w).shape rfl (w).rowRanks (w).colRanks
local notation "cv" => D.external_markedAsCutValues q (w).shape rfl (w).rowRanks (w).colRanks hproper hmax v
local notation "g" => D.producedCutSeed q hg P x b0

theorem producedMarkedValues_allSeams :
    D.ProducedMarkedSeamEquations q hproper hmax hg P x b0 i0 := by
  dsimp only [ProducedMarkedSeamEquations]
  exact D.external_allSeamsFromBranches q hproper hmax hg P x b0 i0
    (D.external_producedOldSeam_dataV2 q hproper hmax hg P x b0 i0)
    (D.parent_producedSelectedSeamComplete q hproper hmax hg P x b0 i0)
    (D.external_producedOriginalInternalSeam_data q hproper hmax hg P x b0 i0)
    (D.external_producedMirrorInternalSeam_data q hproper hmax hg P x b0 i0)
    (D.external_producedTransversePlus_dataSeam q hproper hmax hg P x b0 i0)
    (D.external_producedTransverseMinus_dataSeam q hproper hmax hg P x b0 i0)
    (D.external_producedFirstShortEquation_shared q hproper hmax hg P x b0 i0)
    (D.parent_producedWrapSeamComplete q hproper hmax hg P x b0 i0)
end
end OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram
end


#check OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.producedMarkedValues_allSeams
#print axioms OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.producedMarkedValues_allSeams
