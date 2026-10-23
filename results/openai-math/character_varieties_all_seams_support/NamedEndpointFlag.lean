import NamedFramePortAt

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
