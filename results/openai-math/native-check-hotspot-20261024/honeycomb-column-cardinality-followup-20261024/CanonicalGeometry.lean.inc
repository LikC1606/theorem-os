inductive Vertex where
  | up (i j : ℤ)
  | down (i j : ℤ)
  deriving DecidableEq

def adjacent : Vertex → Vertex → Prop
  | .up i j, .down k l =>
      (k = i ∧ l = j - 1) ∨ (k = i ∧ l = j) ∨ (k = i - 1 ∧ l = j)
  | .down k l, .up i j =>
      (k = i ∧ l = j - 1) ∨ (k = i ∧ l = j) ∨ (k = i - 1 ∧ l = j)
  | _, _ => False

noncomputable def layer (vertex : Vertex) : ℤ :=
  Vertex.rec (fun _ vertical => vertical) (fun _ vertical => vertical) vertex

structure BridgePath (h : ℕ) where
  vertices : List Vertex
  distinct : vertices.Nodup
  connected : vertices.IsChain adjacent
  source : vertices.head? = some (.up 0 0)
  terminal : ∃ i : ℤ, vertices.getLast? = some (.down i ((h : ℤ) - 1))
  inStrip : ∀ v ∈ vertices, 0 ≤ layer v ∧ layer v < (h : ℤ)

/-- Integer column coordinate of the frozen honeycomb vertices. -/
def bridgeBoxColumn : Vertex → ℤ
  | .up i j => 2 * i + j
  | .down i j => 2 * i + j + 1

/-- A path lies in the two-column-slab box indexed by `-R, ..., R`. -/
def bridgeInColumnBox {h : ℕ} (R : ℕ) (p : BridgePath h) : Prop :=
  ∀ v ∈ p.vertices,
    -(2 * (R : ℤ)) ≤ bridgeBoxColumn v ∧
      bridgeBoxColumn v ≤ 2 * (R : ℤ) + 1

