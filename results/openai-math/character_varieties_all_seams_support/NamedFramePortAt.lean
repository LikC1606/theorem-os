import FrameIndexBridge

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
