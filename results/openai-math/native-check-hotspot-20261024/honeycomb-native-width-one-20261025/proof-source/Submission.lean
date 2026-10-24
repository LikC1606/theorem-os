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
def hexX : Vertex → ℤ
  | .up i j => 2 * i + j
  | .down i j => 2 * i + j + 1

lemma eq_of_hexX_layer {v w : Vertex} (hX : hexX v = hexX w) (hj : layer v = layer w) :
    v = w := by
  cases v with
  | up i j =>
    cases w with
    | up i' j' =>
      simp only [hexX, layer] at hX hj
      subst hj
      have : i = i' := by omega
      subst this; rfl
    | down i' j' =>
      simp only [hexX, layer] at hX hj
      omega
  | down i j =>
    cases w with
    | up i' j' =>
      simp only [hexX, layer] at hX hj
      omega
    | down i' j' =>
      simp only [hexX, layer] at hX hj
      subst hj
      have : i = i' := by omega
      subst this; rfl

lemma hexX_step {a b : Vertex} (hl : layer a = layer b) (hab : adjacent a b) :
    hexX b = hexX a + 1 ∨ hexX b = hexX a - 1 := by
  cases a with
  | up i j => cases b with
    | up _ _ => simp [adjacent] at hab
    | down k l =>
      simp only [adjacent] at hab
      have hl' : j = l := hl
      simp only [hexX]
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  | down k l => cases b with
    | down _ _ => simp [adjacent] at hab
    | up i j =>
      simp only [adjacent] at hab
      have hl' : l = j := hl
      simp only [hexX]
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

lemma hexX_up_zero : hexX (.up 0 0) = 0 := rfl

lemma head?_eq_getElem?_zero {α : Type*} (l : List α) : l.head? = l[0]? := by
  cases l <;> rfl

lemma ne_nil_of_vertices_nonempty {h : ℕ} (p : BridgePath h) : p.vertices ≠ [] := by
  intro hnil
  have hsrc := p.source
  rw [hnil] at hsrc
  simp at hsrc

lemma int_walk_monotone {n : ℕ} {f : ℕ → ℤ}
    (hinj : ∀ i j, i < n → j < n → f i = f j → i = j)
    (hstep : ∀ i, i + 1 < n → f (i + 1) = f i + 1 ∨ f (i + 1) = f i - 1) :
    (∀ i, i < n → f i = f 0 + (i : ℤ)) ∨ (∀ i, i < n → f i = f 0 - (i : ℤ)) := by
  have no_flip : ∀ k, k + 2 < n → ¬(f (k+1) = f k + 1 ∧ f (k+2) = f (k+1) - 1) ∧
      ¬(f (k+1) = f k - 1 ∧ f (k+2) = f (k+1) + 1) := by
    intro k hk
    constructor
    · rintro ⟨h1, h2⟩
      have hval : f (k+2) = f k := by rw [h2, h1]; ring
      exact absurd (hinj (k+2) k (by omega) (by omega) hval) (by omega)
    · rintro ⟨h1, h2⟩
      have hval : f (k+2) = f k := by rw [h2, h1]; ring
      exact absurd (hinj (k+2) k (by omega) (by omega) hval) (by omega)
  rcases Nat.lt_or_ge n 2 with hn | hn
  · left
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0; simp
  · rcases hstep 0 (by omega) with hplus | hminus
    · left
      have allplus : ∀ j, j + 1 < n → f (j+1) = f j + 1 := by
        intro j
        induction j with
        | zero => intro _; exact hplus
        | succ k ihk =>
          intro hjk
          have hprev : f (k+1) = f k + 1 := ihk (by omega)
          rcases hstep (k+1) hjk with h | h
          · exact h
          · exact absurd ⟨hprev, h⟩ (no_flip k (by omega)).1
      intro i
      induction i using Nat.strong_induction_on with
      | _ i ih =>
        intro hi
        match i with
        | 0 => simp
        | k + 1 =>
          have hk : f (k+1) = f k + 1 := allplus k (by omega)
          have hk' : f k = f 0 + (k : ℤ) := ih k (by omega) (by omega)
          rw [hk, hk']
          push_cast
          ring
    · right
      have allminus : ∀ j, j + 1 < n → f (j+1) = f j - 1 := by
        intro j
        induction j with
        | zero => intro _; exact hminus
        | succ k ihk =>
          intro hjk
          have hprev : f (k+1) = f k - 1 := ihk (by omega)
          rcases hstep (k+1) hjk with h | h
          · exact absurd ⟨hprev, h⟩ (no_flip k (by omega)).2
          · exact h
      intro i
      induction i using Nat.strong_induction_on with
      | _ i ih =>
        intro hi
        match i with
        | 0 => simp
        | k + 1 =>
          have hk : f (k+1) = f k - 1 := allminus k (by omega)
          have hk' : f k = f 0 - (k : ℤ) := ih k (by omega) (by omega)
          rw [hk, hk']
          push_cast
          ring

lemma chain_hexX_walk {l : List Vertex}
    (hchain : l.IsChain adjacent) (hnd : l.Nodup)
    (hlay : ∀ v ∈ l, layer v = 0) :
    (∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length),
        hexX (l[i]'hi) = hexX (l[j]'hj) → i = j) ∧
    (∀ (i : ℕ) (hi : i + 1 < l.length),
        hexX (l[i+1]'hi) = hexX (l[i]'(by omega)) + 1 ∨
        hexX (l[i+1]'hi) = hexX (l[i]'(by omega)) - 1) := by
  constructor
  · intro i j hi hj hX
    have hli : layer (l[i]'hi) = 0 := hlay _ (List.getElem_mem (l := l) hi)
    have hlj : layer (l[j]'hj) = 0 := hlay _ (List.getElem_mem (l := l) hj)
    have hveq : l[i]'hi = l[j]'hj := eq_of_hexX_layer hX (by rw [hli, hlj])
    by_contra hne
    exact absurd hveq (fun h => hne ((hnd.getElem_inj (hi := hi) (hj := hj)).mp h))
  · intro i hi
    have h1 : adjacent (l[i]'(by omega)) (l[i+1]'hi) := hchain.getElem i hi
    have hl1 : layer (l[i]'(by omega)) = 0 := hlay _ (List.getElem_mem (l := l) (by omega))
    have hl2 : layer (l[i+1]'hi) = 0 := hlay _ (List.getElem_mem (l := l) (by omega))
    exact hexX_step (by rw [hl1, hl2]) h1

lemma BridgePath.ext_vertices {h : ℕ} {p q : BridgePath h} (hv : p.vertices = q.vertices) :
    p = q := by
  cases p with
  | mk vp dp cp sp tp ip =>
    cases q with
    | mk vq dq cq sq tq iq =>
      simp only at hv
      subst hv
      congr 1

lemma layer_eq_zero_of_bridge1 {p : BridgePath 1} (v : Vertex) (hv : v ∈ p.vertices) :
    layer v = 0 := by
  have h := p.inStrip v hv
  have h1 : layer v < ((1 : ℕ) : ℤ) := h.2
  have h2 : 0 ≤ layer v := h.1
  omega

lemma length_pos_of_bridge {h : ℕ} (p : BridgePath h) : 0 < p.vertices.length :=
  List.length_pos_iff.mpr (ne_nil_of_vertices_nonempty p)

noncomputable def bridge1CoordFun (p : BridgePath 1) : ℕ → ℤ :=
  fun i => hexX (p.vertices.getD i (.up 0 0))

lemma bridge1CoordFun_eq (p : BridgePath 1) {i : ℕ} (hi : i < p.vertices.length) :
    bridge1CoordFun p i = hexX (p.vertices[i]'hi) := by
  unfold bridge1CoordFun
  rw [List.getD_eq_getElem]

lemma bridge1_start (p : BridgePath 1) {h : 0 < p.vertices.length} :
    hexX (p.vertices[0]'h) = 0 := by
  have hsrc : p.vertices[0]? = some (.up 0 0) := by
    rw [← head?_eq_getElem?_zero]; exact p.source
  have e1 : p.vertices[0]? = some (p.vertices[0]'h) := List.getElem?_eq_getElem h
  rw [e1] at hsrc
  have hv : p.vertices[0]'h = .up 0 0 := Option.some.inj hsrc
  rw [hv]; exact hexX_up_zero

lemma bridge1_hexX (p : BridgePath 1) :
    (∀ (i : ℕ) (_hi : i < p.vertices.length), bridge1CoordFun p i = (i : ℤ)) ∨
    (∀ (i : ℕ) (_hi : i < p.vertices.length), bridge1CoordFun p i = -(i : ℤ)) := by
  have hlen : 0 < p.vertices.length := length_pos_of_bridge p
  obtain ⟨hinj, hstep⟩ :=
    chain_hexX_walk p.connected p.distinct (fun v hv => layer_eq_zero_of_bridge1 v hv)
  have hinj' : ∀ i j, i < p.vertices.length → j < p.vertices.length →
      bridge1CoordFun p i = bridge1CoordFun p j → i = j := by
    intro i j hi hj hf
    rw [bridge1CoordFun_eq p hi, bridge1CoordFun_eq p hj] at hf
    exact hinj i j hi hj hf
  have hstep' : ∀ i, i + 1 < p.vertices.length →
      bridge1CoordFun p (i+1) = bridge1CoordFun p i + 1 ∨
      bridge1CoordFun p (i+1) = bridge1CoordFun p i - 1 := by
    intro i hi
    rw [bridge1CoordFun_eq p hi, bridge1CoordFun_eq p (by omega)]
    exact hstep i hi
  have hc0 : bridge1CoordFun p 0 = 0 := by
    rw [bridge1CoordFun_eq p hlen]; exact bridge1_start p
  obtain hm | hm := int_walk_monotone (n := p.vertices.length) hinj' hstep'
  · left
    intro i hi
    have h := hm i hi
    rw [hc0] at h
    simpa using h
  · right
    intro i hi
    have h := hm i hi
    rw [hc0] at h
    simpa using h

lemma bridge1_length_ge_two (p : BridgePath 1) : 2 ≤ p.vertices.length := by
  have hpos := length_pos_of_bridge p
  obtain ⟨i, hi⟩ := p.terminal
  rcases Nat.lt_or_ge p.vertices.length 2 with h | h
  · have hlen1 : p.vertices.length = 1 := by omega
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen1
    have hhead : p.vertices.head? = some a := by rw [ha]; rfl
    rw [p.source] at hhead
    have hav : a = Vertex.up 0 0 := Option.some.inj hhead.symm
    have hlast : p.vertices.getLast? = some a := by rw [ha]; rfl
    rw [hi] at hlast
    have hcontra : Vertex.down i (((1 : ℕ) : ℤ) - 1) = Vertex.up 0 0 := by
      have hd : Vertex.down i (((1 : ℕ) : ℤ) - 1) = a := Option.some.inj hlast
      rw [hd, hav]
    exact absurd hcontra (by simp)
  · exact h

lemma bridge1_second (p : BridgePath 1) :
    bridge1CoordFun p 1 = 1 ∨ bridge1CoordFun p 1 = -1 := by
  have h2 := bridge1_length_ge_two p
  rcases bridge1_hexX p with hp | hp
  · left; have := hp 1 (by omega); simpa using this
  · right; have := hp 1 (by omega); simpa using this

lemma bridge1_det {p q : BridgePath 1}
    (hlen : p.vertices.length = q.vertices.length)
    (hsecond : bridge1CoordFun p 1 = bridge1CoordFun q 1) :
    p.vertices = q.vertices := by
  have h2q : 2 ≤ q.vertices.length := by have := bridge1_length_ge_two q; omega
  have hlen' : 2 ≤ p.vertices.length := bridge1_length_ge_two p
  have sign : ∀ i, i < p.vertices.length → bridge1CoordFun p i = bridge1CoordFun q i := by
    intro i hi
    rcases bridge1_hexX p with hp | hp <;> rcases bridge1_hexX q with hq | hq
    · rw [hp i hi, hq i (by omega)]
    · exfalso
      have h1 := hp 1 (by omega)
      have h2' := hq 1 (by omega)
      rw [h1, h2'] at hsecond
      omega
    · exfalso
      have h1 := hp 1 (by omega)
      have h2' := hq 1 (by omega)
      rw [h1, h2'] at hsecond
      omega
    · rw [hp i hi, hq i (by omega)]
  refine List.ext_getElem hlen ?_
  intro i hi hiq
  have hlp : layer (p.vertices[i]'hi) = 0 :=
    layer_eq_zero_of_bridge1 _ (List.getElem_mem (l := p.vertices) hi)
  have hlq : layer (q.vertices[i]'hiq) = 0 :=
    layer_eq_zero_of_bridge1 _ (List.getElem_mem (l := q.vertices) hiq)
  refine eq_of_hexX_layer ?_ (by rw [hlp, hlq])
  rw [← bridge1CoordFun_eq p hi, ← bridge1CoordFun_eq q hiq]
  exact sign i hi

theorem bridge1_card_le_two (n : ℕ) (s : Finset (BridgePath 1))
    (hlen : ∀ p ∈ s, p.vertices.length = n) : s.card ≤ 2 := by
  have hinj : Set.InjOn (fun p : BridgePath 1 => bridge1CoordFun p 1) (s : Set (BridgePath 1)) := by
    intro p hp q hq heq
    have hpn : p.vertices.length = n := hlen p hp
    have hqn : q.vertices.length = n := hlen q hq
    exact BridgePath.ext_vertices (bridge1_det (by omega) heq)
  have hmaps : Set.MapsTo (fun p : BridgePath 1 => bridge1CoordFun p 1) (s : Set (BridgePath 1))
      ({-1, 1} : Finset ℤ) := by
    intro p _
    rcases bridge1_second p with h | h <;> simp [h]
  calc s.card ≤ ({-1, 1} : Finset ℤ).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ 2 := Finset.card_le_two

theorem stripGrowthAtOne :
    ∃ C β : ℝ, 0 ≤ C ∧ 0 ≤ β ∧ β < 2 * Real.cos (Real.pi / 8) ∧
      ∀ (n : ℕ) (s : Finset (BridgePath 1)),
        (∀ p ∈ s, p.vertices.length = n) → (s.card : ℝ) ≤ C * β ^ n := by
  refine ⟨2, 1, by norm_num, by norm_num, ?_, ?_⟩
  · have hpos : 0 < Real.cos (Real.pi / 8) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [Real.pi_pos]
    have h2 : Real.sqrt 2 < 2 := by
      calc Real.sqrt 2 < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
        _ = 2 := by norm_num
    have hle : Real.sqrt (2 + Real.sqrt 2) < 2 := by
      calc Real.sqrt (2 + Real.sqrt 2) < Real.sqrt 4 :=
            Real.sqrt_lt_sqrt (by positivity) (by linarith)
        _ = 2 := by norm_num
    have hgt : 1 < Real.sqrt (2 + Real.sqrt 2) := by
      have h1 : (1 : ℝ) < 2 + Real.sqrt 2 := by
        have := Real.sqrt_nonneg 2; linarith
      calc (1 : ℝ) = Real.sqrt 1 := by simp
        _ < Real.sqrt (2 + Real.sqrt 2) := Real.sqrt_lt_sqrt (by norm_num) h1
    rw [Real.cos_pi_div_eight]
    linarith
  · intro n s hs
    have hcard : s.card ≤ 2 := bridge1_card_le_two n s hs
    have hcast : ((s.card : ℝ)) ≤ 2 := by exact_mod_cast hcard
    simpa using hcast

theorem width_one_summability :
    Summable (weight (h := 1)) ∧ Summable (firstLengthWeight (h := 1)) := by
  obtain ⟨C, β, hC, hβ, hlt, hcount⟩ := stripGrowthAtOne
  have hL : Summable (firstLengthWeight (h := 1)) :=
    bridgeSummable_firstLengthWeight_of_mu_bound hC hβ hlt hcount
  exact ⟨bridgeSummable_weight_of_summable_firstLengthWeight hL, hL⟩

theorem finite_bridge_sums_at_one :
    Summable (weight (h := 1)) ∧ Summable (firstLengthWeight (h := 1)) ∧
    Summable (fun p : BridgePath 1 => firstLengthWeight p / bridgeMass 1) ∧
    Summable (fun p : ConfinedBridgePath 1 => weight p.val) ∧
    Summable (fun p : ConfinedBridgePath 1 => firstLengthWeight p.val) ∧
    Summable (fun p : ConfinedBridgePath 1 => firstLengthWeight p.val / confinedMass 1) := by
  obtain ⟨hw, hL⟩ := width_one_summability
  have hc : Summable (fun p : ConfinedBridgePath 1 => firstLengthWeight p.val) :=
    hL.subtype (fun p : BridgePath 1 => InLogCorridor p)
  exact ⟨hw, hL, hL.div_const (bridgeMass 1), hw.subtype _,
    hc, hc.div_const (confinedMass 1)⟩


theorem finite_bridge_sums : FiniteBridgeSums := by
  sorry

end PolynomialVacuumBridge.Corridor

end OAI
