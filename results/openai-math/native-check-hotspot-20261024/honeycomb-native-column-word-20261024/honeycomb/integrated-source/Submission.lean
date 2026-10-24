import Mathlib

namespace OAI

namespace PolynomialVacuumBridge.Corridor

inductive Vertex where
  | up (i j : ℤ)
  | down (i j : ℤ)
  deriving DecidableEq

noncomputable def position : Vertex → ℝ × ℝ
  | .up i j => ((i : ℝ) + (j : ℝ) / 2,
      ((j : ℝ) + 1 / 3) * (Real.sqrt 3 / 2))
  | .down i j => ((i : ℝ) + (j : ℝ) / 2 + 1 / 2,
      ((j : ℝ) + 2 / 3) * (Real.sqrt 3 / 2))

def adjacent : Vertex → Vertex → Prop
  | .up i j, .down k l =>
      (k = i ∧ l = j - 1) ∨ (k = i ∧ l = j) ∨ (k = i - 1 ∧ l = j)
  | .down k l, .up i j =>
      (k = i ∧ l = j - 1) ∨ (k = i ∧ l = j) ∨ (k = i - 1 ∧ l = j)
  | _, _ => False

noncomputable def criticalActivity : ℝ := (2 * Real.cos (Real.pi / 8))⁻¹
noncomputable def layer (vertex : Vertex) : ℤ :=
  Vertex.rec (fun _ vertical => vertical) (fun _ vertical => vertical) vertex

structure BridgePath (h : ℕ) where
  vertices : List Vertex
  distinct : vertices.Nodup
  connected : vertices.IsChain adjacent
  source : vertices.head? = some (.up 0 0)
  terminal : ∃ i : ℤ, vertices.getLast? = some (.down i ((h : ℤ) - 1))
  inStrip : ∀ v ∈ vertices, 0 ≤ layer v ∧ layer v < (h : ℤ)

noncomputable def weight {h : ℕ} (p : BridgePath h) : ℝ :=
  criticalActivity ^ p.vertices.length

noncomputable def firstLengthWeight {h : ℕ} (p : BridgePath h) : ℝ :=
  (p.vertices.length : ℝ) * weight p

noncomputable def bridgeMass (h : ℕ) : ℝ := ∑' p : BridgePath h, weight p
noncomputable def InLogCorridor {h : ℕ} (p : BridgePath h) : Prop :=
  ∀ v ∈ p.vertices, |(position v).1| ≤ (h : ℝ) * (Real.log (h : ℝ)) ^ 2

def ConfinedBridgePath (h : ℕ) := {p : BridgePath h // InLogCorridor p}

noncomputable def confinedMass (h : ℕ) : ℝ :=
  ∑' p : ConfinedBridgePath h, weight p.val
def FiniteBridgeSums : Prop :=
  ∀ h : ℕ, 1 ≤ h →
    Summable (weight (h := h)) ∧ Summable (firstLengthWeight (h := h)) ∧
    Summable (fun p : BridgePath h => firstLengthWeight p / bridgeMass h) ∧
    Summable (fun p : ConfinedBridgePath h => weight p.val) ∧
    Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val) ∧
    Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val / confinedMass h)


lemma bridgeCriticalActivity_pos : 0 < criticalActivity := by
  have hmem : Real.pi / 8 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have hc : 0 < Real.cos (Real.pi / 8) := Real.cos_pos_of_mem_Ioo hmem
  unfold criticalActivity
  positivity
lemma bridgeCriticalActivity_mul_mu :
    criticalActivity * (2 * Real.cos (Real.pi / 8)) = 1 := by
  have hmem : Real.pi / 8 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have hc : 0 < Real.cos (Real.pi / 8) := Real.cos_pos_of_mem_Ioo hmem
  have hne : Real.cos (Real.pi / 8) ≠ 0 := ne_of_gt hc
  unfold criticalActivity
  field_simp
lemma bridgeHead?_ne_nil {l : List Vertex} {v : Vertex} (h : l.head? = some v) : l ≠ [] := by
  intro hnil
  rw [hnil] at h
  simp at h
lemma bridgeOne_le_length {h : ℕ} (p : BridgePath h) : 1 ≤ p.vertices.length := by
  have hne : p.vertices ≠ [] := bridgeHead?_ne_nil p.source
  have := List.length_pos_iff.mpr hne
  omega
lemma bridgeWeight_nonneg {h : ℕ} (p : BridgePath h) : 0 ≤ weight p :=
  pow_nonneg (le_of_lt bridgeCriticalActivity_pos) _
lemma bridgeWeight_le_firstLengthWeight {h : ℕ} (p : BridgePath h) :
    weight p ≤ firstLengthWeight p := by
  have hn : (1 : ℝ) ≤ (p.vertices.length : ℝ) := by
    exact_mod_cast bridgeOne_le_length p
  have hw : 0 ≤ weight p := bridgeWeight_nonneg p
  unfold firstLengthWeight
  nlinarith
lemma bridgeSummable_weight_of_summable_firstLengthWeight {h : ℕ}
    (hL : Summable (firstLengthWeight (h := h))) :
    Summable (weight (h := h)) :=
  Summable.of_nonneg_of_le (fun p => bridgeWeight_nonneg p)
    (fun p => bridgeWeight_le_firstLengthWeight p) hL
lemma bridgeSummable_firstLengthWeight_of_profile {h : ℕ} {u : ℕ → ℝ}
    (hu : ∀ n, 0 ≤ u n)
    (hsum : Summable (fun n : ℕ => (n : ℝ) * u n * criticalActivity ^ n))
    (hcount : ∀ (n : ℕ) (s : Finset (BridgePath h)),
      (∀ p ∈ s, p.vertices.length = n) → (s.card : ℝ) ≤ u n) :
    Summable (firstLengthWeight (h := h)) := by
  have hα : 0 ≤ criticalActivity := le_of_lt bridgeCriticalActivity_pos
  refine summable_of_sum_le (c := ∑' n : ℕ, (n : ℝ) * u n * criticalActivity ^ n)
    (fun p => ?_) (fun s => ?_)
  · unfold firstLengthWeight weight
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hα _)
  · set L : ℕ → ℝ := fun n => (n : ℝ) * u n * criticalActivity ^ n with hL
    have hmap : ∀ p ∈ s, p.vertices.length ∈ s.image (fun p => p.vertices.length) :=
      fun p hp => Finset.mem_image_of_mem _ hp
    rw [← Finset.sum_fiberwise_of_maps_to hmap (fun p => firstLengthWeight p)]
    have hstep : ∀ n ∈ s.image (fun p => p.vertices.length),
        ∑ p ∈ s with p.vertices.length = n, firstLengthWeight p ≤ L n := by
      intro n _
      have hcongr : ∑ p ∈ s with p.vertices.length = n, firstLengthWeight p
          = ((s.filter (fun p => p.vertices.length = n)).card : ℝ) *
              ((n : ℝ) * criticalActivity ^ n) := by
        rw [Finset.sum_congr rfl (fun p hp => ?_), Finset.sum_const, nsmul_eq_mul]
        have hpn : p.vertices.length = n := (Finset.mem_filter.mp hp).2
        simp only [firstLengthWeight, weight, hpn]
      have hfib : ∀ p ∈ s.filter (fun p => p.vertices.length = n), p.vertices.length = n :=
        fun p hp => (Finset.mem_filter.mp hp).2
      have hcard : ((s.filter (fun p => p.vertices.length = n)).card : ℝ) ≤ u n :=
        hcount n _ hfib
      have hfac : (0 : ℝ) ≤ (n : ℝ) * criticalActivity ^ n :=
        mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hα n)
      rw [hcongr]
      calc ((s.filter (fun p => p.vertices.length = n)).card : ℝ) *
              ((n : ℝ) * criticalActivity ^ n)
          ≤ u n * ((n : ℝ) * criticalActivity ^ n) :=
            mul_le_mul_of_nonneg_right hcard hfac
        _ = L n := by simp only [hL]; ring
    refine le_trans (Finset.sum_le_sum hstep) ?_
    exact Summable.sum_le_tsum _ (fun n _ => by
      simp only [hL]
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hu n)) (pow_nonneg hα n)) hsum
lemma bridgeSummable_firstLengthWeight_of_mu_bound {h : ℕ} {C β : ℝ}
    (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hlt : β < 2 * Real.cos (Real.pi / 8))
    (hcount : ∀ (n : ℕ) (s : Finset (BridgePath h)),
      (∀ p ∈ s, p.vertices.length = n) → (s.card : ℝ) ≤ C * β ^ n) :
    Summable (firstLengthWeight (h := h)) := by
  have hmul : β * criticalActivity < 1 := by
    calc β * criticalActivity
        < (2 * Real.cos (Real.pi / 8)) * criticalActivity :=
          mul_lt_mul_of_pos_right hlt bridgeCriticalActivity_pos
      _ = 1 := by rw [mul_comm]; exact bridgeCriticalActivity_mul_mu
  have hb : ‖β * criticalActivity‖ < 1 := by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hβ (le_of_lt bridgeCriticalActivity_pos))]
    exact hmul
  have hgeom : Summable (fun n : ℕ => (n : ℝ) * (C * β ^ n) * criticalActivity ^ n) := by
    have h1 : Summable (fun n : ℕ => C * ((n : ℝ) ^ 1 * (β * criticalActivity) ^ n)) :=
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hb).mul_left C
    refine h1.congr fun n => ?_
    rw [pow_one, mul_pow]
    ring
  exact bridgeSummable_firstLengthWeight_of_profile
    (fun n => mul_nonneg hC (pow_nonneg hβ n)) hgeom hcount
lemma bridgeFiniteBridgeSums_of_firstLengthWeight
    (hL : ∀ h : ℕ, 1 ≤ h → Summable (firstLengthWeight (h := h))) : FiniteBridgeSums := by
  intro h hh
  have hw : Summable (weight (h := h)) :=
    bridgeSummable_weight_of_summable_firstLengthWeight (hL h hh)
  have hc : Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val) :=
    (hL h hh).subtype (fun p : BridgePath h => InLogCorridor p)
  exact ⟨hw, hL h hh, (hL h hh).div_const (bridgeMass h),
    hw.subtype (fun p : BridgePath h => InLogCorridor p), hc,
    hc.div_const (confinedMass h)⟩
theorem finite_bridge_sums_of_stripGrowthBelowMu
    (H : ∀ h : ℕ, 1 ≤ h → ∃ C β : ℝ, 0 ≤ C ∧ 0 ≤ β ∧
      β < 2 * Real.cos (Real.pi / 8) ∧
      ∀ (n : ℕ) (s : Finset (BridgePath h)),
        (∀ p ∈ s, p.vertices.length = n) → (s.card : ℝ) ≤ C * β ^ n) :
    FiniteBridgeSums := by
  refine bridgeFiniteBridgeSums_of_firstLengthWeight fun h hh => ?_
  obtain ⟨C, β, hC, hβ, hlt, hcount⟩ := H h hh
  exact bridgeSummable_firstLengthWeight_of_mu_bound hC hβ hlt hcount
lemma bridgeColumnStep_unique :
    ∀ {a b d : Vertex}, adjacent a b → adjacent a d →
      (match b with | .up i j => 2 * i + j | .down i j => 2 * i + j + 1) =
      (match d with | .up i j => 2 * i + j | .down i j => 2 * i + j + 1) →
      b = d := by
  intro a b d hab had hcode
  cases a with
  | up i j =>
      cases b with
      | up i' j' =>
          simp only [adjacent] at hab
      | down k l =>
          cases d with
          | up i' j' =>
              simp only [adjacent] at had
          | down k' l' =>
              simp only [adjacent] at hab had
              rcases hab with ⟨hk, hl⟩ | ⟨hk, hl⟩ | ⟨hk, hl⟩ <;>
              rcases had with ⟨hk', hl'⟩ | ⟨hk', hl'⟩ | ⟨hk', hl'⟩ <;>
              simp only at hcode
              all_goals
                rw [Vertex.down.injEq]
                constructor <;> omega
  | down k l =>
      cases b with
      | up i j =>
          cases d with
          | up i' j' =>
              simp only [adjacent] at hab had
              rcases hab with ⟨hk, hl⟩ | ⟨hk, hl⟩ | ⟨hk, hl⟩ <;>
              rcases had with ⟨hk', hl'⟩ | ⟨hk', hl'⟩ | ⟨hk', hl'⟩ <;>
              simp only at hcode
              all_goals
                rw [Vertex.up.injEq]
                constructor <;> omega
          | down k' l' =>
              simp only [adjacent] at had
      | down k' l' =>
          simp only [adjacent] at hab
lemma bridgePath_tail_eq_of_column_map :
    ∀ (a : Vertex) {l₁ l₂ : List Vertex},
      List.IsChain adjacent (a :: l₁) →
      List.IsChain adjacent (a :: l₂) →
      (a :: l₁).map (fun v : Vertex => match v with
        | .up i j => 2 * i + j
        | .down i j => 2 * i + j + 1) =
      (a :: l₂).map (fun v : Vertex => match v with
        | .up i j => 2 * i + j
        | .down i j => 2 * i + j + 1) →
      l₁ = l₂ := by
  intro a l₁
  induction l₁ generalizing a with
  | nil =>
      intro l₂ _ _ hmap
      cases l₂ with
      | nil => rfl
      | cons d l₂ =>
          simp only [List.map_cons, List.map_nil, List.cons.injEq, true_and] at hmap
          cases hmap
  | cons b l₁ ih =>
      intro l₂ hchain₁ hchain₂ hmap
      cases l₂ with
      | nil =>
          simp only [List.map_cons, List.map_nil, List.cons.injEq, true_and] at hmap
          cases hmap
      | cons d l₂ =>
          simp only [List.map_cons, List.cons.injEq, true_and] at hmap
          obtain ⟨hhead, htail⟩ := hmap
          have hab : adjacent a b := (List.isChain_cons_cons.mp hchain₁).1
          have had : adjacent a d := (List.isChain_cons_cons.mp hchain₂).1
          have hbd : b = d := bridgeColumnStep_unique hab had hhead
          subst d
          have htail' : (b :: l₁).map (fun v : Vertex => match v with
                | .up i j => 2 * i + j
                | .down i j => 2 * i + j + 1) =
              (b :: l₂).map (fun v : Vertex => match v with
                | .up i j => 2 * i + j
                | .down i j => 2 * i + j + 1) := by
            simp only [List.map_cons, htail]
          exact congrArg (fun l => b :: l)
            (ih b (List.isChain_cons_cons.mp hchain₁).2
              (List.isChain_cons_cons.mp hchain₂).2 htail')
lemma bridgePath_eq_of_column_eq {h : ℕ} {p q : BridgePath h} :
    p.vertices.map (fun v : Vertex => match v with
      | .up i j => 2 * i + j
      | .down i j => 2 * i + j + 1) =
    q.vertices.map (fun v : Vertex => match v with
      | .up i j => 2 * i + j
      | .down i j => 2 * i + j + 1) →
    p = q := by
  intro hmap
  obtain ⟨l₁, hp⟩ := List.head?_eq_some_iff.mp p.source
  obtain ⟨l₂, hq⟩ := List.head?_eq_some_iff.mp q.source
  have hchain₁ : List.IsChain adjacent (Vertex.up 0 0 :: l₁) := by
    rw [← hp]
    exact p.connected
  have hchain₂ : List.IsChain adjacent (Vertex.up 0 0 :: l₂) := by
    rw [← hq]
    exact q.connected
  have hmap' : (Vertex.up 0 0 :: l₁).map (fun v : Vertex => match v with
        | .up i j => 2 * i + j
        | .down i j => 2 * i + j + 1) =
      (Vertex.up 0 0 :: l₂).map (fun v : Vertex => match v with
        | .up i j => 2 * i + j
        | .down i j => 2 * i + j + 1) := by
    rw [← hp, ← hq]
    exact hmap
  have hl : l₁ = l₂ := bridgePath_tail_eq_of_column_map (Vertex.up 0 0)
    hchain₁ hchain₂ hmap'
  have hv : p.vertices = q.vertices := by
    rw [hp, hq, hl]
  cases p with
  | mk pv pd pc ps pt pi =>
      cases q with
      | mk qv qd qc qs qt qi =>
          simp only at hv
          subst qv
          simp
theorem finite_bridge_sums : FiniteBridgeSums := by
  sorry

end PolynomialVacuumBridge.Corridor

end OAI
