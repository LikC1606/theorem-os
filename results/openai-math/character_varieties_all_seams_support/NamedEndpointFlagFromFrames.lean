import NamedEndpointCancel
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
