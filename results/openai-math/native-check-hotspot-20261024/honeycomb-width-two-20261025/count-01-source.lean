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

namespace WidthTwo

def inside (v : Vertex) : Prop := 0 ≤ layer v ∧ layer v < 2

noncomputable def neighbors : Vertex → Finset Vertex
  | .up i j => if j = 0 then {.down i 0, .down (i-1) 0}
      else if j = 1 then {.down i 1, .down (i-1) 1, .down i 0} else ∅
  | .down i j => if j = 0 then {.up i 0, .up (i+1) 0, .up i 1}
      else if j = 1 then {.up i 1, .up (i+1) 1} else ∅

lemma inside_cases {v : Vertex} (h : inside v) :
    (∃ i, v = .up i 0) ∨ (∃ i, v = .down i 0) ∨
    (∃ i, v = .up i 1) ∨ (∃ i, v = .down i 1) := by
  cases v with
  | up i j =>
    have hj : j = 0 ∨ j = 1 := by simp only [inside, layer] at h; omega
    rcases hj with rfl | rfl
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr (Or.inr (Or.inl ⟨i, rfl⟩))
  | down i j =>
    have hj : j = 0 ∨ j = 1 := by simp only [inside, layer] at h; omega
    rcases hj with rfl | rfl
    · exact Or.inr (Or.inl ⟨i, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨i, rfl⟩))

lemma mem_neighbors {a b : Vertex} (ha : inside a) :
    b ∈ neighbors a ↔ adjacent a b ∧ inside b := by
  rcases inside_cases ha with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ <;>
  cases b <;> simp [neighbors, adjacent, inside, layer, Vertex.up.injEq, Vertex.down.injEq] <;> omega

noncomputable def nextPairs (a b : Vertex) : Finset (Vertex × Vertex) := by
  classical
  exact ((neighbors b).erase a).biUnion fun c =>
    ((neighbors c).erase b).image fun d => (c,d)

lemma nextPairs_card {a b : Vertex} (ha : inside a) (hb : inside b)
    (hab : adjacent a b) : (nextPairs a b).card ≤ 3 := by
  classical
  have ha_mem : a ∈ neighbors b := (mem_neighbors hb).2 ⟨by
    cases a <;> cases b <;> exact hab, ha⟩
  rcases inside_cases hb with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩
  all_goals
    simp [neighbors] at ha_mem
    rcases ha_mem with rfl | rfl | rfl
    all_goals
      have hi : i - 1 ≠ i := by omega
      have hj : i ≠ i - 1 := by omega
      simp [nextPairs, neighbors, Finset.erase_insert_of_ne, Finset.erase_eq_of_notMem,
        Vertex.up.injEq, Vertex.down.injEq, hi, hj]
      all_goals first
        | exact Finset.card_le_three
        | exact Finset.card_le_two.trans (by omega)
        | exact lt_of_le_of_lt Finset.card_le_two (by omega)

lemma neighbors_card {b : Vertex} (hb : inside b) : (neighbors b).card ≤ 3 := by
  rcases inside_cases hb with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ <;>
    simp [neighbors, Vertex.up.injEq, Vertex.down.injEq]
  all_goals first
    | exact Finset.card_le_three
    | exact Finset.card_le_two.trans (by omega)

lemma erase_neighbors_card {a b : Vertex} (ha : inside a) (hb : inside b)
    (hab : adjacent a b) : ((neighbors b).erase a).card ≤ 2 := by
  have ha_mem : a ∈ neighbors b := (mem_neighbors hb).2 ⟨by
    cases a <;> cases b <;> exact hab, ha⟩
  have h := Finset.card_erase_add_one ha_mem
  have hc := neighbors_card hb
  omega

lemma nextPairs_valid {a b : Vertex} {cd : Vertex × Vertex}
    (hb : inside b) (hcd : cd ∈ nextPairs a b) :
    inside cd.1 ∧ inside cd.2 ∧ adjacent cd.1 cd.2 := by
  classical
  rcases Finset.mem_biUnion.mp hcd with ⟨c,hc,hd⟩
  rcases Finset.mem_image.mp hd with ⟨d,hd,rfl⟩
  have hcin : inside c := ((mem_neighbors hb).1 (Finset.mem_erase.mp hc).2).2
  have hdin := (mem_neighbors hcin).1 (Finset.mem_erase.mp hd).2
  exact ⟨hcin,hdin.2,hdin.1⟩

noncomputable def continuations (a b : Vertex) : ℕ → Finset (List Vertex)
  | 0 => {[]}
  | 1 => ((neighbors b).erase a).image fun c => [c]
  | n + 2 => (nextPairs a b).biUnion fun cd =>
      (continuations cd.1 cd.2 n).image fun l => cd.1 :: cd.2 :: l

lemma continuations_card (n : ℕ) (a b : Vertex)
    (ha : inside a) (hb : inside b) (hab : adjacent a b) :
    (continuations a b n).card ≤ 2 * 3 ^ (n / 2) := by
  classical
  induction n using Nat.twoStepInduction generalizing a b with
  | zero => simp [continuations]
  | one =>
    simpa only [continuations, Nat.one_div_two, pow_zero, mul_one] using
      (Finset.card_image_le.trans (erase_neighbors_card ha hb hab))
  | more n ih _ =>
    calc (continuations a b (n+2)).card
        ≤ ∑ cd ∈ nextPairs a b,
            ((continuations cd.1 cd.2 n).image fun l => cd.1 :: cd.2 :: l).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _cd ∈ nextPairs a b, 2 * 3 ^ (n/2) := by
          apply Finset.sum_le_sum
          intro cd hcd
          obtain ⟨hc,hd,hcda⟩ := nextPairs_valid hb hcd
          exact Finset.card_image_le.trans (ih cd.1 cd.2 hc hd hcda)
      _ = (nextPairs a b).card * (2 * 3 ^ (n/2)) := by simp
      _ ≤ 3 * (2 * 3 ^ (n/2)) := Nat.mul_le_mul_right _ (nextPairs_card ha hb hab)
      _ = 2 * 3 ^ ((n+2)/2) := by
          rw [show (n+2)/2 = n/2+1 by omega, pow_succ]
          ring

lemma mem_continuations {a b : Vertex} {l : List Vertex}
    (hc : (a :: b :: l).IsChain adjacent)
    (hnd : (a :: b :: l).Nodup)
    (hin : ∀ v ∈ a :: b :: l, inside v) :
    l ∈ continuations a b l.length := by
  classical
  induction l using List.twoStepInduction generalizing a b with
  | nil => simp [continuations]
  | singleton c =>
    apply Finset.mem_image.mpr
    refine ⟨c,Finset.mem_erase.mpr ⟨?_,?_⟩,rfl⟩
    · have hnot := (List.nodup_cons.mp hnd).1
      simpa using (fun h : c = a => hnot (by simp [h]))
    · exact (mem_neighbors (hin b (by simp))).2 ⟨hc.tail.rel,hin c (by simp)⟩
  | cons_cons c d l ih _ =>
    have hcin : inside c := hin c (by simp)
    have hdin : inside d := hin d (by simp)
    have hcn : c ≠ a := by
      intro h
      exact (List.nodup_cons.mp hnd).1 (by simp [h])
    have hdn : d ≠ b := by
      intro h
      exact (List.nodup_cons.mp hnd.tail).1 (by simp [h])
    have hpair : (c,d) ∈ nextPairs a b := by
      apply Finset.mem_biUnion.mpr
      refine ⟨c,Finset.mem_erase.mpr ⟨hcn,?_⟩,?_⟩
      · exact (mem_neighbors (hin b (by simp))).2 ⟨hc.tail.rel,hcin⟩
      · exact Finset.mem_image.mpr ⟨d,Finset.mem_erase.mpr
          ⟨hdn,(mem_neighbors hcin).2 ⟨hc.tail.tail.rel,hdin⟩⟩,rfl⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨(c,d),hpair,Finset.mem_image.mpr ⟨l,?_,rfl⟩⟩
    apply ih hc.tail.tail hnd.tail.tail
    intro v hv
    exact hin v (by simp only [List.mem_cons] at hv ⊢; tauto)

end WidthTwo

end PolynomialVacuumBridge.Corridor
end OAI
