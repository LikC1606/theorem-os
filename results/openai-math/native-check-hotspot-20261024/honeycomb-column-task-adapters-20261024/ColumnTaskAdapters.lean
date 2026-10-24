import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Chain

set_option Elab.async false
set_option stderrAsMessages false

namespace OAI.PolynomialVacuumBridge.Corridor

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


/-- At a fixed honeycomb vertex, a neighboring vertex is determined by its column.
This checks all three edges of the frozen adjacency relation. -/
theorem bridgeAdjacent_unique_of_column {u v w : Vertex}
    (huv : adjacent u v) (huw : adjacent u w)
    (hcolumn : bridgeBoxColumn v = bridgeBoxColumn w) : v = w := by
  cases u <;> cases v <;> cases w <;>
    simp only [adjacent, bridgeBoxColumn] at huv huw hcolumn
  all_goals
    rcases huv with ⟨hv1, hv2⟩ | ⟨hv1, hv2⟩ | ⟨hv1, hv2⟩
    all_goals
      rcases huw with ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩
      all_goals congr 1 <;> omega

/-- With a common initial vertex, the complete column word determines a chain's tail. -/
theorem bridgeChain_tail_eq_of_columnWord {root : Vertex} {vs ws : List Vertex}
    (hvs : (root :: vs).IsChain adjacent)
    (hws : (root :: ws).IsChain adjacent)
    (hword : vs.map bridgeBoxColumn = ws.map bridgeBoxColumn) : vs = ws := by
  induction vs generalizing root ws with
  | nil =>
      cases ws with
      | nil => rfl
      | cons w ws => cases hword
  | cons v vs ih =>
      cases ws with
      | nil => cases hword
      | cons w ws =>
          have hwords : bridgeBoxColumn v = bridgeBoxColumn w ∧
              vs.map bridgeBoxColumn = ws.map bridgeBoxColumn := by
            simpa only [List.map_cons, List.cons.injEq] using hword
          have hvw : v = w := bridgeAdjacent_unique_of_column
            (List.isChain_cons_cons.mp hvs).1
            (List.isChain_cons_cons.mp hws).1 hwords.1
          subst w
          exact congrArg (List.cons v) (ih
            (List.isChain_cons_cons.mp hvs).2
            (List.isChain_cons_cons.mp hws).2 hwords.2)

/-- Absolute integer columns of the canonical vertex list, including the source. -/
def bridgeColumnWord {h : ℕ} (p : BridgePath h) : List ℤ :=
  p.vertices.map bridgeBoxColumn

theorem bridgeVertices_eq_of_columnWord {h : ℕ} (p q : BridgePath h)
    (hword : bridgeColumnWord p = bridgeColumnWord q) :
    p.vertices = q.vertices := by
  have hpsource := p.source
  have hqsource := q.source
  have hpchain := p.connected
  have hqchain := q.connected
  unfold bridgeColumnWord at hword
  cases hp : p.vertices with
  | nil => simp only [hp, List.head?_nil, reduceCtorEq] at hpsource
  | cons v vs =>
      cases hq : q.vertices with
      | nil => simp only [hq, List.head?_nil, reduceCtorEq] at hqsource
      | cons w ws =>
          have hv : v = Vertex.up 0 0 := by
            simpa only [hp, List.head?_cons, Option.some.injEq] using hpsource
          have hw : w = Vertex.up 0 0 := by
            simpa only [hq, List.head?_cons, Option.some.injEq] using hqsource
          subst v
          subst w
          apply congrArg (List.cons (Vertex.up 0 0))
          apply bridgeChain_tail_eq_of_columnWord
            (by simpa only [hp] using hpchain)
            (by simpa only [hq] using hqchain)
          exact (List.cons.inj (by simpa only [hp, hq, List.map_cons] using hword)).2

/-- Distinct canonical paths have distinct column words. No strip-count estimate is assumed. -/
theorem bridgeColumnWord_injective (h : ℕ) :
    Function.Injective (bridgeColumnWord (h := h)) := by
  intro p q hword
  have hvertices := bridgeVertices_eq_of_columnWord p q hword
  cases p
  cases q
  cases hvertices
  rfl

#print axioms bridgeAdjacent_unique_of_column
#print axioms bridgeChain_tail_eq_of_columnWord
#print axioms bridgeVertices_eq_of_columnWord
#print axioms bridgeColumnWord_injective

theorem bridgePath_eq_of_column_eq : ∀ {h : ℕ} {p q : OAI.PolynomialVacuumBridge.Corridor.BridgePath h}, p.vertices.map (fun v : OAI.PolynomialVacuumBridge.Corridor.Vertex => match v with | .up i j => 2 * i + j | .down i j => 2 * i + j + 1) = q.vertices.map (fun v : OAI.PolynomialVacuumBridge.Corridor.Vertex => match v with | .up i j => 2 * i + j | .down i j => 2 * i + j + 1) → p = q := by
  intro h p q hword
  exact bridgeColumnWord_injective h hword

theorem bridgeColumnStep_unique : ∀ {a b d : OAI.PolynomialVacuumBridge.Corridor.Vertex}, OAI.PolynomialVacuumBridge.Corridor.adjacent a b → OAI.PolynomialVacuumBridge.Corridor.adjacent a d → (match b with | .up i j => 2 * i + j | .down i j => 2 * i + j + 1) = (match d with | .up i j => 2 * i + j | .down i j => 2 * i + j + 1) → b = d := by
  intro a b d hab had hcolumn
  exact bridgeAdjacent_unique_of_column hab had hcolumn

#print axioms bridgePath_eq_of_column_eq
#print axioms bridgeColumnStep_unique

end OAI.PolynomialVacuumBridge.Corridor
