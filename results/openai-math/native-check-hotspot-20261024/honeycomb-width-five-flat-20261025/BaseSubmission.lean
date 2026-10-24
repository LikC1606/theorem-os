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
def widthThreeInside (v : Vertex) : Prop := 0 ≤ layer v ∧ layer v < 3

def widthThreeNeighbors : Vertex → Finset Vertex
  | .up i j => if j = 0 then {.down i 0, .down (i-1) 0}
      else if j = 1 then {.down i 1, .down (i-1) 1, .down i 0}
      else if j = 2 then {.down i 2, .down (i-1) 2, .down i 1} else ∅
  | .down i j => if j = 0 then {.up i 0, .up (i+1) 0, .up i 1}
      else if j = 1 then {.up i 1, .up (i+1) 1, .up i 2}
      else if j = 2 then {.up i 2, .up (i+1) 2} else ∅

lemma widthThreeInside_cases {v : Vertex} (h : widthThreeInside v) :
    (∃ i, v = .up i 0) ∨ (∃ i, v = .down i 0) ∨
    (∃ i, v = .up i 1) ∨ (∃ i, v = .down i 1) ∨
    (∃ i, v = .up i 2) ∨ (∃ i, v = .down i 2) := by
  cases v with
  | up i j =>
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by simp only [widthThreeInside, layer] at h; omega
    rcases hj with rfl | rfl | rfl
    · exact Or.inl ⟨i,rfl⟩
    · exact Or.inr (Or.inr (Or.inl ⟨i,rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i,rfl⟩))))
  | down i j =>
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by simp only [widthThreeInside, layer] at h; omega
    rcases hj with rfl | rfl | rfl
    · exact Or.inr (Or.inl ⟨i,rfl⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i,rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i,rfl⟩))))

lemma widthThreeMem_neighbors {a b : Vertex} (ha : widthThreeInside a) :
    b ∈ widthThreeNeighbors a ↔ adjacent a b ∧ widthThreeInside b := by
  rcases widthThreeInside_cases ha with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ <;>
  cases b <;> simp [widthThreeNeighbors, adjacent, widthThreeInside, layer, Vertex.up.injEq, Vertex.down.injEq] <;> omega

def widthThreeShift (t : ℤ) : Vertex → Vertex
  | .up i j => .up (t+i) j
  | .down i j => .down (t+i) j

lemma widthThreeShift_injective (t : ℤ) : Function.Injective (widthThreeShift t) := by
  intro a b he
  cases a <;> cases b <;> simp [widthThreeShift,Vertex.up.injEq,Vertex.down.injEq] at he ⊢ <;> tauto

lemma widthThreeNeighbors_shift (t : ℤ) (b : Vertex) :
    widthThreeNeighbors (widthThreeShift t b) = (widthThreeNeighbors b).image (widthThreeShift t) := by
  cases b <;> simp only [widthThreeShift,widthThreeNeighbors] <;> split_ifs <;>
    simp [widthThreeShift,add_sub_assoc,add_assoc]

lemma widthThreeErase_neighbors_shift (t : ℤ) (a b : Vertex) :
    (widthThreeNeighbors (widthThreeShift t b)).erase (widthThreeShift t a) = ((widthThreeNeighbors b).erase a).image (widthThreeShift t) := by
  classical
  rw [widthThreeNeighbors_shift]
  ext v
  constructor
  · intro h
    obtain ⟨hv,hin⟩ := Finset.mem_erase.mp h
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hin
    apply Finset.mem_image.mpr
    exact ⟨c,Finset.mem_erase.mpr ⟨fun he => hv (congrArg (widthThreeShift t) he),hc⟩,rfl⟩
  · intro h
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_erase.mpr ⟨fun he => (Finset.mem_erase.mp hc).1 (widthThreeShift_injective t he),
      Finset.mem_image.mpr ⟨c,(Finset.mem_erase.mp hc).2,rfl⟩⟩

def widthThreeCount (a b : Vertex) : ℕ → ℕ
  | 0 => 1
  | n+1 => ∑ c ∈ (widthThreeNeighbors b).erase a, widthThreeCount b c n

lemma widthThreeCount_shift (t : ℤ) (n : ℕ) (a b : Vertex) :
    widthThreeCount (widthThreeShift t a) (widthThreeShift t b) n = widthThreeCount a b n := by
  classical
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    rw [widthThreeCount,widthThreeErase_neighbors_shift,Finset.sum_image]
    · exact Finset.sum_congr rfl (fun c _ => ih b c)
    · intro c hc d hd he
      exact widthThreeShift_injective t he

lemma widthThreeCount_five {a b : Vertex} (ha : widthThreeInside a) (hb : widthThreeInside b)
    (hab : adjacent a b) : widthThreeCount a b 5 ≤ 20 := by
  have ha_mem : a ∈ widthThreeNeighbors b := (widthThreeMem_neighbors hb).2 ⟨by
    cases a <;> cases b <;> exact hab,ha⟩
  rcases widthThreeInside_cases hb with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩
  all_goals
    simp [widthThreeNeighbors] at ha_mem
    rcases ha_mem with rfl | rfl | rfl
    all_goals
      rw [← widthThreeCount_shift (-i) 5]
      simp only [widthThreeShift,sub_eq_add_neg,neg_add_cancel,neg_add_cancel_left]
      decide

lemma widthThreeNeighbors_card {b : Vertex} (hb : widthThreeInside b) : (widthThreeNeighbors b).card ≤ 3 := by
  rcases widthThreeInside_cases hb with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ <;>
    simp [widthThreeNeighbors,Vertex.up.injEq,Vertex.down.injEq]
  all_goals first
    | exact Finset.card_le_three
    | exact Finset.card_le_two.trans (by omega)

lemma widthThreeErase_neighbors_card {a b : Vertex} (ha : widthThreeInside a) (hb : widthThreeInside b)
    (hab : adjacent a b) : ((widthThreeNeighbors b).erase a).card ≤ 2 := by
  have ha_mem : a ∈ widthThreeNeighbors b := (widthThreeMem_neighbors hb).2 ⟨by
    cases a <;> cases b <;> exact hab,ha⟩
  have h := Finset.card_erase_add_one ha_mem
  have hc := widthThreeNeighbors_card hb
  omega

lemma widthThreeCount_degree_bound (n : ℕ) (a b : Vertex)
    (ha : widthThreeInside a) (hb : widthThreeInside b) (hab : adjacent a b) : widthThreeCount a b n ≤ 2^n := by
  induction n generalizing a b with
  | zero => simp [widthThreeCount]
  | succ n ih =>
    calc widthThreeCount a b (n+1)
        ≤ ∑ _c ∈ (widthThreeNeighbors b).erase a, 2^n := by
          apply Finset.sum_le_sum
          intro c hc
          have hbc := (widthThreeMem_neighbors hb).1 (Finset.mem_erase.mp hc).2
          exact ih b c hb hbc.2 hbc.1
      _ = ((widthThreeNeighbors b).erase a).card * 2^n := by simp
      _ ≤ 2 * 2^n := Nat.mul_le_mul_right _ (widthThreeErase_neighbors_card ha hb hab)
      _ = 2^(n+1) := by ring

lemma widthThreeCount_add_bound (k n B : ℕ)
    (H : ∀ a b, widthThreeInside a → widthThreeInside b → adjacent a b → widthThreeCount a b n ≤ B)
    (a b : Vertex) (ha : widthThreeInside a) (hb : widthThreeInside b) (hab : adjacent a b) :
    widthThreeCount a b (k+n) ≤ widthThreeCount a b k * B := by
  induction k generalizing a b with
  | zero => simpa [widthThreeCount] using H a b ha hb hab
  | succ k ih =>
    rw [show k+1+n = (k+n)+1 by omega,widthThreeCount]
    calc (∑ c ∈ (widthThreeNeighbors b).erase a, widthThreeCount b c (k+n))
        ≤ ∑ c ∈ (widthThreeNeighbors b).erase a, widthThreeCount b c k * B := by
          apply Finset.sum_le_sum
          intro c hc
          have hbc := (widthThreeMem_neighbors hb).1 (Finset.mem_erase.mp hc).2
          exact ih b c hb hbc.2 hbc.1
      _ = widthThreeCount a b (k+1) * B := by rw [widthThreeCount,Finset.sum_mul]

lemma widthThreeCount_block_bound (n : ℕ) (a b : Vertex)
    (ha : widthThreeInside a) (hb : widthThreeInside b) (hab : adjacent a b) :
    widthThreeCount a b n ≤ 16 * 20^(n/5) := by
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases hn : n < 5
    · have hpow : 2^n ≤ 2^4 := Nat.pow_le_pow_right (by omega) (by omega)
      norm_num at hpow
      have hd := widthThreeCount_degree_bound n a b ha hb hab
      have he : n/5 = 0 := by omega
      simpa only [he,pow_zero,mul_one] using hd.trans hpow
    · let m := n-5
      have hm : m < n := by dsimp [m]; omega
      have H : ∀ c d, widthThreeInside c → widthThreeInside d → adjacent c d → widthThreeCount c d m ≤ 16*20^(m/5) := by
        intro c d hc hd hcd
        exact ih m hm c d hc hd hcd
      have hbnd := widthThreeCount_add_bound 5 m (16*20^(m/5)) H a b ha hb hab
      rw [show 5+m = n by dsimp [m]; omega] at hbnd
      calc widthThreeCount a b n ≤ widthThreeCount a b 5 * (16*20^(m/5)) := hbnd
        _ ≤ 20 * (16*20^(m/5)) := Nat.mul_le_mul_right _ (widthThreeCount_five ha hb hab)
        _ = 16 * 20^(n/5) := by
          rw [show n/5 = m/5+1 by dsimp [m]; omega,pow_succ]
          ring

def widthThreeContinuations (a b : Vertex) : ℕ → Finset (List Vertex)
  | 0 => {[]}
  | n+1 => ((widthThreeNeighbors b).erase a).biUnion fun c =>
      (widthThreeContinuations b c n).image fun l => c :: l

lemma widthThreeContinuations_card (n : ℕ) (a b : Vertex) :
    (widthThreeContinuations a b n).card ≤ widthThreeCount a b n := by
  induction n generalizing a b with
  | zero => simp [widthThreeContinuations,widthThreeCount]
  | succ n ih =>
    calc (widthThreeContinuations a b (n+1)).card
        ≤ ∑ c ∈ (widthThreeNeighbors b).erase a,
            ((widthThreeContinuations b c n).image fun l => c :: l).card := Finset.card_biUnion_le
      _ ≤ ∑ c ∈ (widthThreeNeighbors b).erase a, widthThreeCount b c n := by
          apply Finset.sum_le_sum
          intro c hc
          exact Finset.card_image_le.trans (ih b c)
      _ = widthThreeCount a b (n+1) := rfl

lemma widthThreeMem_continuations {a b : Vertex} {l : List Vertex}
    (hc : (a :: b :: l).IsChain adjacent)
    (hnd : (a :: b :: l).Nodup)
    (hin : ∀ v ∈ a :: b :: l, widthThreeInside v) :
    l ∈ widthThreeContinuations a b l.length := by
  induction l generalizing a b with
  | nil => simp [widthThreeContinuations]
  | cons c l ih =>
    have hcin : widthThreeInside c := hin c (by simp)
    have hcn : c ≠ a := by
      intro h
      exact (List.nodup_cons.mp hnd).1 (by simp [h])
    apply Finset.mem_biUnion.mpr
    refine ⟨c,Finset.mem_erase.mpr ⟨hcn,?_⟩,?_⟩
    · exact (widthThreeMem_neighbors (hin b (by simp))).2 ⟨hc.tail.rel,hcin⟩
    · apply Finset.mem_image.mpr
      refine ⟨l,?_,rfl⟩
      apply ih hc.tail hnd.tail
      intro v hv
      exact hin v (by simp only [List.mem_cons] at hv ⊢; tauto)

def widthThreeAllPaths (n : ℕ) : Finset (List Vertex) :=
  (widthThreeNeighbors (.up 0 0)).biUnion fun b =>
    (widthThreeContinuations (.up 0 0) b (n-2)).image fun l => (.up 0 0) :: b :: l

lemma widthThreeAllPaths_card (n : ℕ) : (widthThreeAllPaths n).card ≤ 32 * 20 ^ (n/5) := by
  have hs : widthThreeInside (.up 0 0) := by simp [widthThreeInside,layer]
  calc (widthThreeAllPaths n).card
      ≤ ∑ b ∈ widthThreeNeighbors (.up 0 0),
          ((widthThreeContinuations (.up 0 0) b (n-2)).image fun l => (.up 0 0) :: b :: l).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ widthThreeNeighbors (.up 0 0), 16 * 20 ^ ((n-2)/5) := by
        apply Finset.sum_le_sum
        intro b hb
        obtain ⟨hadj,hbin⟩ := (widthThreeMem_neighbors hs).1 hb
        exact Finset.card_image_le.trans ((widthThreeContinuations_card (n-2) _ _).trans
          (widthThreeCount_block_bound (n-2) _ _ hs hbin hadj))
    _ = 32 * 20 ^ ((n-2)/5) := by simp [widthThreeNeighbors]; ring
    _ ≤ 32 * 20 ^ (n/5) := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_right (by omega) (by omega)

lemma widthThreePath_mem_allPaths (p : BridgePath 3) : p.vertices ∈ widthThreeAllPaths p.vertices.length := by
  have hsrc := p.source
  have hterm := p.terminal
  cases hv : p.vertices with
  | nil => simp [hv] at hsrc
  | cons a l =>
    have ha : a = .up 0 0 := by simpa [hv] using hsrc
    subst a
    cases l with
    | nil =>
      rcases hterm with ⟨i,hi⟩
      simp [hv] at hi
    | cons b l =>
      have hc : ((.up 0 0) :: b :: l).IsChain adjacent := by simpa only [hv] using p.connected
      have hnd : ((.up 0 0) :: b :: l).Nodup := by simpa only [hv] using p.distinct
      have hin : ∀ v ∈ (.up 0 0) :: b :: l, widthThreeInside v := by
        intro v h
        have hvp : v ∈ p.vertices := by simpa only [hv] using h
        simpa only [widthThreeInside, Nat.cast_ofNat] using p.inStrip v hvp
      rw [widthThreeAllPaths]
      apply Finset.mem_biUnion.mpr
      refine ⟨b,(widthThreeMem_neighbors (hin _ (by simp))).2 ⟨hc.rel,hin b (by simp)⟩,?_⟩
      apply Finset.mem_image.mpr
      refine ⟨l,?_,by simpa only [hv]⟩
      have hlen : l.length + 1 + 1 - 2 = l.length := by omega
      simpa only [hv,List.length_cons,hlen] using widthThreeMem_continuations hc hnd hin

lemma widthThreePath_card (n : ℕ) (s : Finset (BridgePath 3))
    (hlen : ∀ p ∈ s, p.vertices.length = n) : s.card ≤ 32 * 20 ^ (n/5) := by
  classical
  have hm : Set.MapsTo (fun p : BridgePath 3 => p.vertices) (s : Set (BridgePath 3))
      (widthThreeAllPaths n : Set (List Vertex)) := by
    intro p hp
    change p.vertices ∈ widthThreeAllPaths n
    simpa only [hlen p hp] using widthThreePath_mem_allPaths p
  have hi : Set.InjOn (fun p : BridgePath 3 => p.vertices) (s : Set (BridgePath 3)) := by
    intro p hp q hq he
    cases p
    cases q
    cases he
    rfl
  exact (Finset.card_le_card_of_injOn _ hm hi).trans (widthThreeAllPaths_card n)

lemma widthThreeBeta_lt_mu : (11/6 : ℝ) < 2 * Real.cos (Real.pi / 8) := by
  have hsq2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have h2 : (7/5 : ℝ) < Real.sqrt 2 := by
    by_contra h
    have hle : Real.sqrt 2 ≤ (7/5 : ℝ) := le_of_not_gt h
    have hsqle := mul_le_mul hle hle (Real.sqrt_nonneg 2) (by norm_num : (0 : ℝ) ≤ 7/5)
    nlinarith
  have hroot : Real.sqrt ((11/6 : ℝ)^2) < Real.sqrt (2 + Real.sqrt 2) :=
    Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  rw [Real.sqrt_sq (by norm_num)] at hroot
  rw [Real.cos_pi_div_eight]
  nlinarith

lemma widthThreePath_card_real (n : ℕ) (s : Finset (BridgePath 3))
    (hlen : ∀ p ∈ s, p.vertices.length = n) :
    (s.card : ℝ) ≤ 32 * (11/6 : ℝ) ^ n := by
  have hcard : (s.card : ℝ) ≤ 32 * (20 : ℝ) ^ (n/5) := by
    exact_mod_cast widthThreePath_card n s hlen
  have hpow : (20 : ℝ)^(n/5) ≤ ((11/6 : ℝ)^5)^(n/5) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  calc (s.card : ℝ) ≤ 32 * (20 : ℝ) ^ (n/5) := hcard
    _ ≤ 32 * ((11/6 : ℝ)^5)^(n/5) := mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ = 32 * (11/6 : ℝ)^(5*(n/5)) := by rw [pow_mul]
    _ ≤ 32 * (11/6 : ℝ)^n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) (by norm_num)

theorem widthThreeStripGrowthAtThree :
    ∃ C β : ℝ, 0 ≤ C ∧ 0 ≤ β ∧ β < 2 * Real.cos (Real.pi / 8) ∧
      ∀ (n : ℕ) (s : Finset (BridgePath 3)),
        (∀ p ∈ s, p.vertices.length = n) → (s.card : ℝ) ≤ C * β ^ n := by
  exact ⟨32, (11/6 : ℝ), by norm_num, by norm_num, widthThreeBeta_lt_mu, widthThreePath_card_real⟩

theorem width_three_summability_diagnostic :
    Summable (weight (h := 3)) ∧ Summable (firstLengthWeight (h := 3)) := by
  obtain ⟨C, β, hC, hβ, hlt, hcount⟩ := widthThreeStripGrowthAtThree
  have hL : Summable (firstLengthWeight (h := 3)) :=
    bridgeSummable_firstLengthWeight_of_mu_bound hC hβ hlt hcount
  exact ⟨bridgeSummable_weight_of_summable_firstLengthWeight hL,hL⟩

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
def bridgeBoxColumn : Vertex → ℤ
  | .up i j => 2 * i + j
  | .down i j => 2 * i + j + 1
noncomputable def bridgeLayerColumnCode (v : Vertex) : ℤ × ℤ :=
  (layer v, bridgeBoxColumn v)
theorem bridgeLayerColumnCode_injective :
    Function.Injective bridgeLayerColumnCode := by
  intro v w h
  cases v <;> cases w <;>
    simp only [bridgeLayerColumnCode, layer, bridgeBoxColumn, Prod.mk.injEq] at h
  · congr 1 <;> omega
  · omega
  · omega
  · congr 1 <;> omega
theorem bridgeBoxColumn_eq_twice_position (v : Vertex) :
    (bridgeBoxColumn v : ℝ) = 2 * (position v).1 := by
  cases v <;> simp only [bridgeBoxColumn, position] <;> push_cast <;> ring
theorem bridgeBoundedVertices_finite (h : ℕ) (B : ℝ) :
    Set.Finite {v : Vertex |
      0 ≤ layer v ∧ layer v < (h : ℤ) ∧ |(position v).1| ≤ B} := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * B)
  have hfinite : Set.Finite
      ((Set.Ico (0 : ℤ) (h : ℤ)) ×ˢ Set.Icc (-(N : ℤ)) (N : ℤ)) :=
    (Set.finite_Ico _ _).prod (Set.finite_Icc _ _)
  apply (Set.Finite.preimage bridgeLayerColumnCode_injective.injOn hfinite).subset
  intro v hv
  have hcol : |(bridgeBoxColumn v : ℝ)| ≤ 2 * B := by
    rw [bridgeBoxColumn_eq_twice_position, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left hv.2.2 (by norm_num)
  have hcol' := abs_le.mp hcol
  have hlow : -(N : ℝ) ≤ (bridgeBoxColumn v : ℝ) := by linarith
  have hhigh : (bridgeBoxColumn v : ℝ) ≤ (N : ℝ) := by linarith
  exact ⟨⟨hv.1, hv.2.1⟩, by exact_mod_cast hlow, by exact_mod_cast hhigh⟩
def ConfinedBridgeVertex (h : ℕ) :=
  {v : Vertex | 0 ≤ layer v ∧ layer v < (h : ℤ) ∧
    |(position v).1| ≤ (h : ℝ) * (Real.log (h : ℝ)) ^ 2}
theorem bridgeConfinedVertex_finite (h : ℕ) : Finite (ConfinedBridgeVertex h) :=
  (bridgeBoundedVertices_finite h ((h : ℝ) * (Real.log (h : ℝ)) ^ 2)).to_subtype
noncomputable def bridgeConfinedVertexList {h : ℕ} (p : ConfinedBridgePath h) :
    List (ConfinedBridgeVertex h) :=
  p.val.vertices.attachWith _ (fun v hv =>
    ⟨(p.val.inStrip v hv).1, (p.val.inStrip v hv).2, p.property v hv⟩)
theorem bridgeConfinedVertexList_map_val {h : ℕ} (p : ConfinedBridgePath h) :
    (bridgeConfinedVertexList p).map Subtype.val = p.val.vertices :=
  List.attachWith_map_subtype_val _
theorem bridgeConfinedVertexList_nodup {h : ℕ} (p : ConfinedBridgePath h) :
    (bridgeConfinedVertexList p).Nodup := by
  apply List.Nodup.of_map Subtype.val
  rw [bridgeConfinedVertexList_map_val]
  exact p.val.distinct
theorem bridgeConfinedVertexList_injective (h : ℕ) :
    Function.Injective (bridgeConfinedVertexList (h := h)) := by
  intro p q heq
  apply Subtype.ext
  have hvertices : p.val.vertices = q.val.vertices := by
    simpa only [bridgeConfinedVertexList_map_val] using
      congrArg (List.map Subtype.val) heq
  cases p with
  | mk p hp =>
    cases q with
    | mk q hq =>
      cases p
      cases q
      cases hvertices
      rfl
theorem bridgeConfinedPath_finite (h : ℕ) : Finite (ConfinedBridgePath h) := by
  classical
  let _ := bridgeConfinedVertex_finite h
  let _ := Fintype.ofFinite (ConfinedBridgeVertex h)
  let encode : ConfinedBridgePath h →
      {vs : List (ConfinedBridgeVertex h) // vs.Nodup} :=
    fun p => ⟨bridgeConfinedVertexList p, bridgeConfinedVertexList_nodup p⟩
  exact Finite.of_injective encode (fun _ _ heq =>
    bridgeConfinedVertexList_injective h (congrArg Subtype.val heq))
theorem bridgeConfined_summable_weight (h : ℕ) :
    Summable (fun p : ConfinedBridgePath h => weight p.val) := by
  let _ := bridgeConfinedPath_finite h
  exact summable_of_hasFiniteSupport (Set.toFinite _)
theorem bridgeConfined_summable_firstLengthWeight (h : ℕ) :
    Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val) := by
  let _ := bridgeConfinedPath_finite h
  exact summable_of_hasFiniteSupport (Set.toFinite _)
theorem bridgeConfined_summable_normalizedFirstLengthWeight (h : ℕ) :
    Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val / confinedMass h) := by
  let _ := bridgeConfinedPath_finite h
  exact summable_of_hasFiniteSupport (Set.toFinite _)
theorem bridgeConfined_sums (h : ℕ) :
    Summable (fun p : ConfinedBridgePath h => weight p.val) ∧
    Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val) ∧
    Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val / confinedMass h) :=
  ⟨bridgeConfined_summable_weight h, bridgeConfined_summable_firstLengthWeight h,
    bridgeConfined_summable_normalizedFirstLengthWeight h⟩
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
def widthTwoInside (v : Vertex) : Prop := 0 ≤ layer v ∧ layer v < 2
noncomputable def widthTwoNeighbors : Vertex → Finset Vertex
  | .up i j => if j = 0 then {.down i 0, .down (i-1) 0}
      else if j = 1 then {.down i 1, .down (i-1) 1, .down i 0} else ∅
  | .down i j => if j = 0 then {.up i 0, .up (i+1) 0, .up i 1}
      else if j = 1 then {.up i 1, .up (i+1) 1} else ∅
lemma widthTwo_inside_cases {v : Vertex} (h : widthTwoInside v) :
    (∃ i, v = .up i 0) ∨ (∃ i, v = .down i 0) ∨
    (∃ i, v = .up i 1) ∨ (∃ i, v = .down i 1) := by
  cases v with
  | up i j =>
    have hj : j = 0 ∨ j = 1 := by simp only [widthTwoInside, layer] at h; omega
    rcases hj with rfl | rfl
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr (Or.inr (Or.inl ⟨i, rfl⟩))
  | down i j =>
    have hj : j = 0 ∨ j = 1 := by simp only [widthTwoInside, layer] at h; omega
    rcases hj with rfl | rfl
    · exact Or.inr (Or.inl ⟨i, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨i, rfl⟩))
lemma widthTwo_mem_neighbors {a b : Vertex} (ha : widthTwoInside a) :
    b ∈ widthTwoNeighbors a ↔ adjacent a b ∧ widthTwoInside b := by
  rcases widthTwo_inside_cases ha with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ <;>
  cases b <;> simp [widthTwoNeighbors, adjacent, widthTwoInside, layer, Vertex.up.injEq, Vertex.down.injEq] <;> omega
noncomputable def widthTwoNextPairs (a b : Vertex) : Finset (Vertex × Vertex) := by
  classical
  exact ((widthTwoNeighbors b).erase a).biUnion fun c =>
    ((widthTwoNeighbors c).erase b).image fun d => (c,d)
lemma widthTwo_nextPairs_card {a b : Vertex} (ha : widthTwoInside a) (hb : widthTwoInside b)
    (hab : adjacent a b) : (widthTwoNextPairs a b).card ≤ 3 := by
  classical
  have ha_mem : a ∈ widthTwoNeighbors b := (widthTwo_mem_neighbors hb).2 ⟨by
    cases a <;> cases b <;> exact hab, ha⟩
  rcases widthTwo_inside_cases hb with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩
  all_goals
    simp [widthTwoNeighbors] at ha_mem
    rcases ha_mem with rfl | rfl | rfl
    all_goals
      have hi : i - 1 ≠ i := by omega
      have hj : i ≠ i - 1 := by omega
      simp [widthTwoNextPairs, widthTwoNeighbors, Finset.erase_insert_of_ne, Finset.erase_eq_of_notMem,
        Vertex.up.injEq, Vertex.down.injEq, hi, hj]
      all_goals first
        | exact Finset.card_le_three
        | exact Finset.card_le_two.trans (by omega)
        | exact lt_of_le_of_lt Finset.card_le_two (by omega)
lemma widthTwo_neighbors_card {b : Vertex} (hb : widthTwoInside b) : (widthTwoNeighbors b).card ≤ 3 := by
  rcases widthTwo_inside_cases hb with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ <;>
    simp [widthTwoNeighbors, Vertex.up.injEq, Vertex.down.injEq]
  all_goals first
    | exact Finset.card_le_three
    | exact Finset.card_le_two.trans (by omega)
lemma widthTwo_erase_neighbors_card {a b : Vertex} (ha : widthTwoInside a) (hb : widthTwoInside b)
    (hab : adjacent a b) : ((widthTwoNeighbors b).erase a).card ≤ 2 := by
  have ha_mem : a ∈ widthTwoNeighbors b := (widthTwo_mem_neighbors hb).2 ⟨by
    cases a <;> cases b <;> exact hab, ha⟩
  have h := Finset.card_erase_add_one ha_mem
  have hc := widthTwo_neighbors_card hb
  omega
lemma widthTwo_nextPairs_valid {a b : Vertex} {cd : Vertex × Vertex}
    (hb : widthTwoInside b) (hcd : cd ∈ widthTwoNextPairs a b) :
    widthTwoInside cd.1 ∧ widthTwoInside cd.2 ∧ adjacent cd.1 cd.2 := by
  classical
  rcases Finset.mem_biUnion.mp hcd with ⟨c,hc,hd⟩
  rcases Finset.mem_image.mp hd with ⟨d,hdmem,rfl⟩
  have hcin : widthTwoInside c := ((widthTwo_mem_neighbors hb).1 (Finset.mem_erase.mp hc).2).2
  have hdin := (widthTwo_mem_neighbors hcin).1 (Finset.mem_erase.mp hdmem).2
  exact ⟨hcin,hdin.2,hdin.1⟩
noncomputable def widthTwoContinuations (a b : Vertex) : ℕ → Finset (List Vertex)
  | 0 => {[]}
  | 1 => ((widthTwoNeighbors b).erase a).image fun c => [c]
  | n + 2 => (widthTwoNextPairs a b).biUnion fun cd =>
      (widthTwoContinuations cd.1 cd.2 n).image fun l => cd.1 :: cd.2 :: l
lemma widthTwo_continuations_card (n : ℕ) (a b : Vertex)
    (ha : widthTwoInside a) (hb : widthTwoInside b) (hab : adjacent a b) :
    (widthTwoContinuations a b n).card ≤ 2 * 3 ^ (n / 2) := by
  classical
  induction n using Nat.twoStepInduction generalizing a b with
  | zero => simp [widthTwoContinuations]
  | one =>
    simpa [widthTwoContinuations] using
      (Finset.card_image_le.trans (widthTwo_erase_neighbors_card ha hb hab))
  | more n ih _ =>
    calc (widthTwoContinuations a b (n+2)).card
        ≤ ∑ cd ∈ widthTwoNextPairs a b,
            ((widthTwoContinuations cd.1 cd.2 n).image fun l => cd.1 :: cd.2 :: l).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _cd ∈ widthTwoNextPairs a b, 2 * 3 ^ (n/2) := by
          apply Finset.sum_le_sum
          intro cd hcd
          obtain ⟨hc,hd,hcda⟩ := widthTwo_nextPairs_valid hb hcd
          exact Finset.card_image_le.trans (ih cd.1 cd.2 hc hd hcda)
      _ = (widthTwoNextPairs a b).card * (2 * 3 ^ (n/2)) := by simp
      _ ≤ 3 * (2 * 3 ^ (n/2)) := Nat.mul_le_mul_right _ (widthTwo_nextPairs_card ha hb hab)
      _ = 2 * 3 ^ ((n+2)/2) := by
          rw [show (n+2)/2 = n/2+1 by omega, pow_succ]
          ring
lemma widthTwo_mem_continuations {a b : Vertex} {l : List Vertex}
    (hc : (a :: b :: l).IsChain adjacent)
    (hnd : (a :: b :: l).Nodup)
    (hin : ∀ v ∈ a :: b :: l, widthTwoInside v) :
    l ∈ widthTwoContinuations a b l.length := by
  classical
  induction l using List.twoStepInduction generalizing a b with
  | nil => simp [widthTwoContinuations]
  | singleton c =>
    apply Finset.mem_image.mpr
    refine ⟨c,Finset.mem_erase.mpr ⟨?_,?_⟩,rfl⟩
    · have hnot := (List.nodup_cons.mp hnd).1
      simpa using (fun h : c = a => hnot (by simp [h]))
    · exact (widthTwo_mem_neighbors (hin b (by simp))).2 ⟨hc.tail.rel,hin c (by simp)⟩
  | cons_cons c d l ih _ =>
    have hcin : widthTwoInside c := hin c (by simp)
    have hdin : widthTwoInside d := hin d (by simp)
    have hcn : c ≠ a := by
      intro h
      exact (List.nodup_cons.mp hnd).1 (by simp [h])
    have hdn : d ≠ b := by
      intro h
      exact (List.nodup_cons.mp hnd.tail).1 (by simp [h])
    have hpair : (c,d) ∈ widthTwoNextPairs a b := by
      apply Finset.mem_biUnion.mpr
      refine ⟨c,Finset.mem_erase.mpr ⟨hcn,?_⟩,?_⟩
      · exact (widthTwo_mem_neighbors (hin b (by simp))).2 ⟨hc.tail.rel,hcin⟩
      · exact Finset.mem_image.mpr ⟨d,Finset.mem_erase.mpr
          ⟨hdn,(widthTwo_mem_neighbors hcin).2 ⟨hc.tail.tail.rel,hdin⟩⟩,rfl⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨(c,d),hpair,Finset.mem_image.mpr ⟨l,?_,rfl⟩⟩
    apply ih hc.tail.tail hnd.tail.tail
    intro v hv
    exact hin v (by simp only [List.mem_cons] at hv ⊢; tauto)
noncomputable def widthTwoAllPaths (n : ℕ) : Finset (List Vertex) :=
  (widthTwoNeighbors (.up 0 0)).biUnion fun b =>
    (widthTwoContinuations (.up 0 0) b (n-2)).image fun l => (.up 0 0) :: b :: l
lemma widthTwo_allPaths_card (n : ℕ) : (widthTwoAllPaths n).card ≤ 4 * 3 ^ (n/2) := by
  classical
  have hs : widthTwoInside (.up 0 0) := by simp [widthTwoInside,layer]
  calc (widthTwoAllPaths n).card
      ≤ ∑ b ∈ widthTwoNeighbors (.up 0 0),
          ((widthTwoContinuations (.up 0 0) b (n-2)).image fun l => (.up 0 0) :: b :: l).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ widthTwoNeighbors (.up 0 0), 2 * 3 ^ ((n-2)/2) := by
        apply Finset.sum_le_sum
        intro b hb
        obtain ⟨hadj,hbin⟩ := (widthTwo_mem_neighbors hs).1 hb
        exact Finset.card_image_le.trans (widthTwo_continuations_card (n-2) _ _ hs hbin hadj)
    _ = 4 * 3 ^ ((n-2)/2) := by simp [widthTwoNeighbors]; ring
    _ ≤ 4 * 3 ^ (n/2) := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_right (by omega) (by omega)
lemma widthTwo_path_mem_allPaths (p : BridgePath 2) : p.vertices ∈ widthTwoAllPaths p.vertices.length := by
  classical
  have hsrc := p.source
  have hterm := p.terminal
  cases hv : p.vertices with
  | nil => simp [hv] at hsrc
  | cons a l =>
    have ha : a = .up 0 0 := by simpa [hv] using hsrc
    subst a
    cases l with
    | nil =>
      rcases hterm with ⟨i,hi⟩
      simp [hv] at hi
    | cons b l =>
      have hc : ((.up 0 0) :: b :: l).IsChain adjacent := by simpa only [hv] using p.connected
      have hnd : ((.up 0 0) :: b :: l).Nodup := by simpa only [hv] using p.distinct
      have hin : ∀ v ∈ (.up 0 0) :: b :: l, widthTwoInside v := by
        intro v h
        have hvp : v ∈ p.vertices := by simpa only [hv] using h
        simpa only [widthTwoInside, Nat.cast_ofNat] using p.inStrip v hvp
      rw [widthTwoAllPaths]
      apply Finset.mem_biUnion.mpr
      refine ⟨b,(widthTwo_mem_neighbors (hin _ (by simp))).2 ⟨hc.rel,hin b (by simp)⟩,?_⟩
      apply Finset.mem_image.mpr
      refine ⟨l,?_,by simpa only [hv]⟩
      have hlen : l.length + 1 + 1 - 2 = l.length := by omega
      simpa only [hv,List.length_cons,hlen] using widthTwo_mem_continuations hc hnd hin
lemma widthTwo_path_card (n : ℕ) (s : Finset (BridgePath 2))
    (hlen : ∀ p ∈ s, p.vertices.length = n) : s.card ≤ 4 * 3 ^ (n/2) := by
  classical
  have hm : Set.MapsTo (fun p : BridgePath 2 => p.vertices) (s : Set (BridgePath 2))
      (widthTwoAllPaths n : Set (List Vertex)) := by
    intro p hp
    change p.vertices ∈ widthTwoAllPaths n
    simpa only [hlen p hp] using widthTwo_path_mem_allPaths p
  have hi : Set.InjOn (fun p : BridgePath 2 => p.vertices) (s : Set (BridgePath 2)) := by
    intro p hp q hq he
    cases p
    cases q
    cases he
    rfl
  exact (Finset.card_le_card_of_injOn _ hm hi).trans (widthTwo_allPaths_card n)
lemma widthTwo_sqrt_three_lt_mu : Real.sqrt 3 < 2 * Real.cos (Real.pi / 8) := by
  have hsq2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have h2 : (1 : ℝ) < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hroot : Real.sqrt 3 < Real.sqrt (2 + Real.sqrt 2) :=
    Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  rw [Real.cos_pi_div_eight]
  nlinarith
lemma widthTwo_path_card_real (n : ℕ) (s : Finset (BridgePath 2))
    (hlen : ∀ p ∈ s, p.vertices.length = n) :
    (s.card : ℝ) ≤ 4 * Real.sqrt 3 ^ n := by
  have hcard : (s.card : ℝ) ≤ 4 * (3 : ℝ) ^ (n/2) := by
    exact_mod_cast widthTwo_path_card n s hlen
  have hge : (1 : ℝ) ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  calc (s.card : ℝ) ≤ 4 * (3 : ℝ) ^ (n/2) := hcard
    _ = 4 * Real.sqrt 3 ^ (2*(n/2)) := by
        rw [pow_mul,Real.sq_sqrt (by norm_num)]
    _ ≤ 4 * Real.sqrt 3 ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hge (by omega)) (by norm_num)
theorem widthTwo_stripGrowthAtTwo :
    ∃ C β : ℝ, 0 ≤ C ∧ 0 ≤ β ∧ β < 2 * Real.cos (Real.pi / 8) ∧
      ∀ (n : ℕ) (s : Finset (BridgePath 2)),
        (∀ p ∈ s, p.vertices.length = n) → (s.card : ℝ) ≤ C * β ^ n := by
  exact ⟨4, Real.sqrt 3, by norm_num, Real.sqrt_nonneg 3,
    widthTwo_sqrt_three_lt_mu, widthTwo_path_card_real⟩
theorem width_two_summability_diagnostic :
    Summable (weight (h := 2)) ∧ Summable (firstLengthWeight (h := 2)) := by
  obtain ⟨C, β, hC, hβ, hlt, hcount⟩ := widthTwo_stripGrowthAtTwo
  have hL : Summable (firstLengthWeight (h := 2)) :=
    bridgeSummable_firstLengthWeight_of_mu_bound hC hβ hlt hcount
  exact ⟨bridgeSummable_weight_of_summable_firstLengthWeight hL,hL⟩
theorem finite_bridge_sums : FiniteBridgeSums := by
  sorry

end PolynomialVacuumBridge.Corridor

end OAI
