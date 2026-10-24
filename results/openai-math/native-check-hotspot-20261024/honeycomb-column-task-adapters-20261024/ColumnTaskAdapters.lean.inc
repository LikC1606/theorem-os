theorem bridgePath_eq_of_column_eq : ∀ {h : ℕ} {p q : OAI.PolynomialVacuumBridge.Corridor.BridgePath h}, p.vertices.map (fun v : OAI.PolynomialVacuumBridge.Corridor.Vertex => match v with | .up i j => 2 * i + j | .down i j => 2 * i + j + 1) = q.vertices.map (fun v : OAI.PolynomialVacuumBridge.Corridor.Vertex => match v with | .up i j => 2 * i + j | .down i j => 2 * i + j + 1) → p = q := by
  intro h p q hword
  exact bridgeColumnWord_injective h hword

theorem bridgeColumnStep_unique : ∀ {a b d : OAI.PolynomialVacuumBridge.Corridor.Vertex}, OAI.PolynomialVacuumBridge.Corridor.adjacent a b → OAI.PolynomialVacuumBridge.Corridor.adjacent a d → (match b with | .up i j => 2 * i + j | .down i j => 2 * i + j + 1) = (match d with | .up i j => 2 * i + j | .down i j => 2 * i + j + 1) → b = d := by
  intro a b d hab had hcolumn
  exact bridgeAdjacent_unique_of_column hab had hcolumn

