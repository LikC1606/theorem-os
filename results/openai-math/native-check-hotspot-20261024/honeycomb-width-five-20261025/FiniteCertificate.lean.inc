def potential (w : List Vertex) : ℕ := (table.lookup w).getD 0

def states : List (List Vertex) := table.map Prod.fst

def rowOK (w : List Vertex) : Prop :=
  w ≠ [] ∧ 0 < potential w ∧
    (∀ c ∈ candidates w, normalize (slide w c) ∈ states) ∧
    1000 * (∑ c ∈ candidates w, potential (normalize (slide w c))) ≤ 1847 * potential w

instance (w : List Vertex) : Decidable (rowOK w) := by
  unfold rowOK
  infer_instance


