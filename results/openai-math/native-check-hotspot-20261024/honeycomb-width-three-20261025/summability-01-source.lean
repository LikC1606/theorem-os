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

namespace WidthThree

def inside (v : Vertex) : Prop := 0 ≤ layer v ∧ layer v < 3

def neighbors : Vertex → Finset Vertex
  | .up i j => if j = 0 then {.down i 0, .down (i-1) 0}
      else if j = 1 then {.down i 1, .down (i-1) 1, .down i 0}
      else if j = 2 then {.down i 2, .down (i-1) 2, .down i 1} else ∅
  | .down i j => if j = 0 then {.up i 0, .up (i+1) 0, .up i 1}
      else if j = 1 then {.up i 1, .up (i+1) 1, .up i 2}
      else if j = 2 then {.up i 2, .up (i+1) 2} else ∅

lemma inside_cases {v : Vertex} (h : inside v) :
    (∃ i, v = .up i 0) ∨ (∃ i, v = .down i 0) ∨
    (∃ i, v = .up i 1) ∨ (∃ i, v = .down i 1) ∨
    (∃ i, v = .up i 2) ∨ (∃ i, v = .down i 2) := by
  cases v with
  | up i j =>
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by simp only [inside, layer] at h; omega
    rcases hj with rfl | rfl | rfl
    · exact Or.inl ⟨i,rfl⟩
    · exact Or.inr (Or.inr (Or.inl ⟨i,rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i,rfl⟩))))
  | down i j =>
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by simp only [inside, layer] at h; omega
    rcases hj with rfl | rfl | rfl
    · exact Or.inr (Or.inl ⟨i,rfl⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i,rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i,rfl⟩))))

lemma mem_neighbors {a b : Vertex} (ha : inside a) :
    b ∈ neighbors a ↔ adjacent a b ∧ inside b := by
  rcases inside_cases ha with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ <;>
  cases b <;> simp [neighbors, adjacent, inside, layer, Vertex.up.injEq, Vertex.down.injEq] <;> omega

def shift (t : ℤ) : Vertex → Vertex
  | .up i j => .up (t+i) j
  | .down i j => .down (t+i) j

lemma shift_injective (t : ℤ) : Function.Injective (shift t) := by
  intro a b he
  cases a <;> cases b <;> simp [shift,Vertex.up.injEq,Vertex.down.injEq] at he ⊢ <;> tauto

lemma neighbors_shift (t : ℤ) (b : Vertex) :
    neighbors (shift t b) = (neighbors b).image (shift t) := by
  cases b <;> simp only [shift,neighbors] <;> split_ifs <;>
    simp [shift,add_sub_assoc,add_assoc]

lemma erase_neighbors_shift (t : ℤ) (a b : Vertex) :
    (neighbors (shift t b)).erase (shift t a) = ((neighbors b).erase a).image (shift t) := by
  classical
  rw [neighbors_shift]
  ext v
  constructor
  · intro h
    obtain ⟨hv,hin⟩ := Finset.mem_erase.mp h
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hin
    apply Finset.mem_image.mpr
    exact ⟨c,Finset.mem_erase.mpr ⟨fun he => hv (congrArg (shift t) he),hc⟩,rfl⟩
  · intro h
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_erase.mpr ⟨fun he => (Finset.mem_erase.mp hc).1 (shift_injective t he),
      Finset.mem_image.mpr ⟨c,(Finset.mem_erase.mp hc).2,rfl⟩⟩

def count (a b : Vertex) : ℕ → ℕ
  | 0 => 1
  | n+1 => ∑ c ∈ (neighbors b).erase a, count b c n

lemma count_shift (t : ℤ) (n : ℕ) (a b : Vertex) :
    count (shift t a) (shift t b) n = count a b n := by
  classical
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    rw [count,erase_neighbors_shift,Finset.sum_image]
    · exact Finset.sum_congr rfl (fun c _ => ih b c)
    · intro c hc d hd he
      exact shift_injective t he

lemma count_five {a b : Vertex} (ha : inside a) (hb : inside b)
    (hab : adjacent a b) : count a b 5 ≤ 20 := by
  have ha_mem : a ∈ neighbors b := (mem_neighbors hb).2 ⟨by
    cases a <;> cases b <;> exact hab,ha⟩
  rcases inside_cases hb with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩
  all_goals
    simp [neighbors] at ha_mem
    rcases ha_mem with rfl | rfl | rfl
    all_goals
      rw [← count_shift (-i) 5]
      simp only [shift,sub_eq_add_neg,neg_add_cancel,neg_add_cancel_left]
      decide

lemma neighbors_card {b : Vertex} (hb : inside b) : (neighbors b).card ≤ 3 := by
  rcases inside_cases hb with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ <;>
    simp [neighbors,Vertex.up.injEq,Vertex.down.injEq]
  all_goals first
    | exact Finset.card_le_three
    | exact Finset.card_le_two.trans (by omega)

lemma erase_neighbors_card {a b : Vertex} (ha : inside a) (hb : inside b)
    (hab : adjacent a b) : ((neighbors b).erase a).card ≤ 2 := by
  have ha_mem : a ∈ neighbors b := (mem_neighbors hb).2 ⟨by
    cases a <;> cases b <;> exact hab,ha⟩
  have h := Finset.card_erase_add_one ha_mem
  have hc := neighbors_card hb
  omega

lemma count_degree_bound (n : ℕ) (a b : Vertex)
    (ha : inside a) (hb : inside b) (hab : adjacent a b) : count a b n ≤ 2^n := by
  induction n generalizing a b with
  | zero => simp [count]
  | succ n ih =>
    calc count a b (n+1)
        ≤ ∑ _c ∈ (neighbors b).erase a, 2^n := by
          apply Finset.sum_le_sum
          intro c hc
          have hbc := (mem_neighbors hb).1 (Finset.mem_erase.mp hc).2
          exact ih b c hb hbc.2 hbc.1
      _ = ((neighbors b).erase a).card * 2^n := by simp
      _ ≤ 2 * 2^n := Nat.mul_le_mul_right _ (erase_neighbors_card ha hb hab)
      _ = 2^(n+1) := by ring

lemma count_add_bound (k n B : ℕ)
    (H : ∀ a b, inside a → inside b → adjacent a b → count a b n ≤ B)
    (a b : Vertex) (ha : inside a) (hb : inside b) (hab : adjacent a b) :
    count a b (k+n) ≤ count a b k * B := by
  induction k generalizing a b with
  | zero => simpa [count] using H a b ha hb hab
  | succ k ih =>
    rw [show k+1+n = (k+n)+1 by omega,count]
    calc (∑ c ∈ (neighbors b).erase a, count b c (k+n))
        ≤ ∑ c ∈ (neighbors b).erase a, count b c k * B := by
          apply Finset.sum_le_sum
          intro c hc
          have hbc := (mem_neighbors hb).1 (Finset.mem_erase.mp hc).2
          exact ih b c hb hbc.2 hbc.1
      _ = count a b (k+1) * B := by rw [count,Finset.sum_mul]

lemma count_block_bound (n : ℕ) (a b : Vertex)
    (ha : inside a) (hb : inside b) (hab : adjacent a b) :
    count a b n ≤ 16 * 20^(n/5) := by
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases hn : n < 5
    · have hpow : 2^n ≤ 2^4 := Nat.pow_le_pow_right (by omega) (by omega)
      norm_num at hpow
      have hd := count_degree_bound n a b ha hb hab
      have he : n/5 = 0 := by omega
      simpa only [he,pow_zero,mul_one] using hd.trans hpow
    · let m := n-5
      have hm : m < n := by dsimp [m]; omega
      have H : ∀ c d, inside c → inside d → adjacent c d → count c d m ≤ 16*20^(m/5) := by
        intro c d hc hd hcd
        exact ih m hm c d hc hd hcd
      have hbnd := count_add_bound 5 m (16*20^(m/5)) H a b ha hb hab
      rw [show 5+m = n by dsimp [m]; omega] at hbnd
      calc count a b n ≤ count a b 5 * (16*20^(m/5)) := hbnd
        _ ≤ 20 * (16*20^(m/5)) := Nat.mul_le_mul_right _ (count_five ha hb hab)
        _ = 16 * 20^(n/5) := by
          rw [show n/5 = m/5+1 by dsimp [m]; omega,pow_succ]
          ring

def continuations (a b : Vertex) : ℕ → Finset (List Vertex)
  | 0 => {[]}
  | n+1 => ((neighbors b).erase a).biUnion fun c =>
      (continuations b c n).image fun l => c :: l

lemma continuations_card (n : ℕ) (a b : Vertex) :
    (continuations a b n).card ≤ count a b n := by
  induction n generalizing a b with
  | zero => simp [continuations,count]
  | succ n ih =>
    calc (continuations a b (n+1)).card
        ≤ ∑ c ∈ (neighbors b).erase a,
            ((continuations b c n).image fun l => c :: l).card := Finset.card_biUnion_le
      _ ≤ ∑ c ∈ (neighbors b).erase a, count b c n := by
          apply Finset.sum_le_sum
          intro c hc
          exact Finset.card_image_le.trans (ih b c)
      _ = count a b (n+1) := rfl

lemma mem_continuations {a b : Vertex} {l : List Vertex}
    (hc : (a :: b :: l).IsChain adjacent)
    (hnd : (a :: b :: l).Nodup)
    (hin : ∀ v ∈ a :: b :: l, inside v) :
    l ∈ continuations a b l.length := by
  induction l generalizing a b with
  | nil => simp [continuations]
  | cons c l ih =>
    have hcin : inside c := hin c (by simp)
    have hcn : c ≠ a := by
      intro h
      exact (List.nodup_cons.mp hnd).1 (by simp [h])
    apply Finset.mem_biUnion.mpr
    refine ⟨c,Finset.mem_erase.mpr ⟨hcn,?_⟩,?_⟩
    · exact (mem_neighbors (hin b (by simp))).2 ⟨hc.tail.rel,hcin⟩
    · apply Finset.mem_image.mpr
      refine ⟨l,?_,rfl⟩
      apply ih hc.tail hnd.tail
      intro v hv
      exact hin v (by simp only [List.mem_cons] at hv ⊢; tauto)

def allPaths (n : ℕ) : Finset (List Vertex) :=
  (neighbors (.up 0 0)).biUnion fun b =>
    (continuations (.up 0 0) b (n-2)).image fun l => (.up 0 0) :: b :: l

lemma allPaths_card (n : ℕ) : (allPaths n).card ≤ 32 * 20 ^ (n/5) := by
  have hs : inside (.up 0 0) := by simp [inside,layer]
  calc (allPaths n).card
      ≤ ∑ b ∈ neighbors (.up 0 0),
          ((continuations (.up 0 0) b (n-2)).image fun l => (.up 0 0) :: b :: l).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ neighbors (.up 0 0), 16 * 20 ^ ((n-2)/5) := by
        apply Finset.sum_le_sum
        intro b hb
        obtain ⟨hadj,hbin⟩ := (mem_neighbors hs).1 hb
        exact Finset.card_image_le.trans ((continuations_card (n-2) _ _).trans
          (count_block_bound (n-2) _ _ hs hbin hadj))
    _ = 32 * 20 ^ ((n-2)/5) := by simp [neighbors]; ring
    _ ≤ 32 * 20 ^ (n/5) := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_right (by omega) (by omega)

lemma path_mem_allPaths (p : BridgePath 3) : p.vertices ∈ allPaths p.vertices.length := by
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
      have hin : ∀ v ∈ (.up 0 0) :: b :: l, inside v := by
        intro v h
        have hvp : v ∈ p.vertices := by simpa only [hv] using h
        simpa only [inside, Nat.cast_ofNat] using p.inStrip v hvp
      rw [allPaths]
      apply Finset.mem_biUnion.mpr
      refine ⟨b,(mem_neighbors (hin _ (by simp))).2 ⟨hc.rel,hin b (by simp)⟩,?_⟩
      apply Finset.mem_image.mpr
      refine ⟨l,?_,by simpa only [hv]⟩
      have hlen : l.length + 1 + 1 - 2 = l.length := by omega
      simpa only [hv,List.length_cons,hlen] using mem_continuations hc hnd hin

lemma path_card (n : ℕ) (s : Finset (BridgePath 3))
    (hlen : ∀ p ∈ s, p.vertices.length = n) : s.card ≤ 32 * 20 ^ (n/5) := by
  classical
  have hm : Set.MapsTo (fun p : BridgePath 3 => p.vertices) (s : Set (BridgePath 3))
      (allPaths n : Set (List Vertex)) := by
    intro p hp
    change p.vertices ∈ allPaths n
    simpa only [hlen p hp] using path_mem_allPaths p
  have hi : Set.InjOn (fun p : BridgePath 3 => p.vertices) (s : Set (BridgePath 3)) := by
    intro p hp q hq he
    cases p
    cases q
    cases he
    rfl
  exact (Finset.card_le_card_of_injOn _ hm hi).trans (allPaths_card n)

lemma beta_lt_mu : (11/6 : ℝ) < 2 * Real.cos (Real.pi / 8) := by
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

lemma path_card_real (n : ℕ) (s : Finset (BridgePath 3))
    (hlen : ∀ p ∈ s, p.vertices.length = n) :
    (s.card : ℝ) ≤ 32 * (11/6 : ℝ) ^ n := by
  have hcard : (s.card : ℝ) ≤ 32 * (20 : ℝ) ^ (n/5) := by
    exact_mod_cast path_card n s hlen
  have hpow : (20 : ℝ)^(n/5) ≤ ((11/6 : ℝ)^5)^(n/5) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  calc (s.card : ℝ) ≤ 32 * (20 : ℝ) ^ (n/5) := hcard
    _ ≤ 32 * ((11/6 : ℝ)^5)^(n/5) := mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ = 32 * (11/6 : ℝ)^(5*(n/5)) := by rw [pow_mul]
    _ ≤ 32 * (11/6 : ℝ)^n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) (by norm_num)

theorem stripGrowthAtThree :
    ∃ C β : ℝ, 0 ≤ C ∧ 0 ≤ β ∧ β < 2 * Real.cos (Real.pi / 8) ∧
      ∀ (n : ℕ) (s : Finset (BridgePath 3)),
        (∀ p ∈ s, p.vertices.length = n) → (s.card : ℝ) ≤ C * β ^ n := by
  exact ⟨32, (11/6 : ℝ), by norm_num, by norm_num, beta_lt_mu, path_card_real⟩

end WidthThree

/-- An unconditional fixed-height-three result. -/
theorem width_three_summability_diagnostic :
    Summable (weight (h := 3)) ∧ Summable (firstLengthWeight (h := 3)) := by
  obtain ⟨C, β, hC, hβ, hlt, hcount⟩ := WidthThree.stripGrowthAtThree
  have hL : Summable (firstLengthWeight (h := 3)) :=
    bridgeSummable_firstLengthWeight_of_mu_bound hC hβ hlt hcount
  exact ⟨bridgeSummable_weight_of_summable_firstLengthWeight hL,hL⟩

#check @WidthThree.count_five
#print axioms WidthThree.count_five
#check @WidthThree.count_block_bound
#print axioms WidthThree.count_block_bound
#check @WidthThree.path_mem_allPaths
#print axioms WidthThree.path_mem_allPaths
#check @WidthThree.path_card
#print axioms WidthThree.path_card
#check @WidthThree.stripGrowthAtThree
#print axioms WidthThree.stripGrowthAtThree
#check @width_three_summability_diagnostic
#print axioms width_three_summability_diagnostic
end PolynomialVacuumBridge.Corridor
end OAI
