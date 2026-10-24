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

namespace WidthFour

def inside (v : Vertex) : Prop := 0 ≤ layer v ∧ layer v < 4

noncomputable def neighbors : Vertex → Finset Vertex
  | .up i j => if j = 0 then {.down i 0, .down (i-1) 0}
      else if j = 1 then {.down i 1, .down (i-1) 1, .down i 0}
      else if j = 2 then {.down i 2, .down (i-1) 2, .down i 1}
      else if j = 3 then {.down i 3, .down (i-1) 3, .down i 2} else ∅
  | .down i j => if j = 0 then {.up i 0, .up (i+1) 0, .up i 1}
      else if j = 1 then {.up i 1, .up (i+1) 1, .up i 2}
      else if j = 2 then {.up i 2, .up (i+1) 2, .up i 3}
      else if j = 3 then {.up i 3, .up (i+1) 3} else ∅

lemma inside_cases {v : Vertex} (h : inside v) :
    (∃ i, v = .up i 0) ∨ (∃ i, v = .down i 0) ∨
    (∃ i, v = .up i 1) ∨ (∃ i, v = .down i 1) ∨
    (∃ i, v = .up i 2) ∨ (∃ i, v = .down i 2) ∨
    (∃ i, v = .up i 3) ∨ (∃ i, v = .down i 3) := by
  cases v with
  | up i j =>
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by simp only [inside, layer] at h; omega
    rcases hj with rfl | rfl | rfl | rfl <;> tauto
  | down i j =>
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by simp only [inside, layer] at h; omega
    rcases hj with rfl | rfl | rfl | rfl <;> tauto

lemma mem_neighbors {a b : Vertex} (ha : inside a) :
    b ∈ neighbors a ↔ adjacent a b ∧ inside b := by
  rcases inside_cases ha with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ |
    ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ <;>
  cases b <;> simp [neighbors, adjacent, inside, layer, Vertex.up.injEq, Vertex.down.injEq] <;> omega

/-- Positive rational comparison rate strictly below the canonical connective constant. -/
noncomputable def beta : ℝ := 1847 / 1000

/-- Integer potentials for each valid incoming edge of the four-layer strip.
The potential is translation invariant and distinguishes vertical from horizontal arrivals. -/
noncomputable def edgeWeight (a b : Vertex) : ℝ :=
  match b with
  | .up _ j => if layer a = j-1 then
        (if j = 1 then 64 else if j = 2 then 56 else 33)
      else (if j = 0 then 29 else if j = 1 then 50 else if j = 2 then 58 else 52)
  | .down _ j => if layer a = j+1 then
        (if j = 0 then 33 else if j = 1 then 56 else 64)
      else (if j = 0 then 52 else if j = 1 then 58 else if j = 2 then 50 else 29)

lemma edgeWeight_ge_one (a b : Vertex) : 1 ≤ edgeWeight a b := by
  cases b <;> simp only [edgeWeight] <;> split_ifs <;> norm_num

lemma edgeWeight_le_sixtyFour (a b : Vertex) : edgeWeight a b ≤ 64 := by
  cases b <;> simp only [edgeWeight] <;> split_ifs <;> norm_num

lemma beta_ge_one : 1 ≤ beta := by norm_num [beta]

/-- Every incoming edge obeys the finite rational potential certificate. -/
lemma potential_step {a b : Vertex} (ha : inside a) (hb : inside b)
    (hab : adjacent a b) :
    ∑ c ∈ (neighbors b).erase a, edgeWeight b c ≤ beta * edgeWeight a b := by
  classical
  have ha_mem : a ∈ neighbors b := (mem_neighbors hb).2 ⟨by
    cases a <;> cases b <;> exact hab, ha⟩
  rcases inside_cases hb with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ |
    ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩
  all_goals
    simp [neighbors] at ha_mem
    rcases ha_mem with rfl | rfl | rfl
    all_goals
      have h₁ : i - 1 ≠ i := by omega
      have h₂ : i ≠ i - 1 := by omega
      have h₃ : i + 1 ≠ i := by omega
      have h₄ : i ≠ i + 1 := by omega
      norm_num [neighbors, edgeWeight, layer, beta, Vertex.up.injEq,
        Vertex.down.injEq, h₁, h₂, h₃, h₄]

noncomputable def continuations (a b : Vertex) : ℕ → Finset (List Vertex)
  | 0 => {[]}
  | n + 1 => ((neighbors b).erase a).biUnion fun c =>
      (continuations b c n).image fun l => c :: l

lemma continuations_card (n : ℕ) (a b : Vertex)
    (ha : inside a) (hb : inside b) (hab : adjacent a b) :
    ((continuations a b n).card : ℝ) ≤ edgeWeight a b * beta ^ n := by
  classical
  induction n generalizing a b with
  | zero => simpa only [continuations, Finset.card_singleton, Nat.cast_one, pow_zero, mul_one]
      using edgeWeight_ge_one a b
  | succ n ih =>
    calc ((continuations a b (n+1)).card : ℝ)
        ≤ ∑ c ∈ (neighbors b).erase a,
            (((continuations b c n).image fun l => c :: l).card : ℝ) := by
          exact_mod_cast (Finset.card_biUnion_le :
            (((neighbors b).erase a).biUnion fun c =>
              (continuations b c n).image fun l => c :: l).card ≤ _)
      _ ≤ ∑ c ∈ (neighbors b).erase a, edgeWeight b c * beta ^ n := by
          apply Finset.sum_le_sum
          intro c hc
          have hcin := (mem_neighbors hb).1 (Finset.mem_erase.mp hc).2
          have hcard : (((continuations b c n).image fun l => c :: l).card : ℝ)
              ≤ ((continuations b c n).card : ℝ) := by exact_mod_cast Finset.card_image_le
          exact hcard.trans (ih b c hb hcin.2 hcin.1)
      _ = (∑ c ∈ (neighbors b).erase a, edgeWeight b c) * beta ^ n := by
          rw [Finset.sum_mul]
      _ ≤ (beta * edgeWeight a b) * beta ^ n :=
          mul_le_mul_of_nonneg_right (potential_step ha hb hab)
            (pow_nonneg (le_trans (by norm_num) beta_ge_one) n)
      _ = edgeWeight a b * beta ^ (n+1) := by rw [pow_succ]; ring

lemma mem_continuations {a b : Vertex} {l : List Vertex}
    (hc : (a :: b :: l).IsChain adjacent)
    (hnd : (a :: b :: l).Nodup)
    (hin : ∀ v ∈ a :: b :: l, inside v) :
    l ∈ continuations a b l.length := by
  classical
  induction l generalizing a b with
  | nil => simp [continuations]
  | cons c l ih =>
    have hcin : inside c := hin c (by simp)
    have hcn : c ≠ a := by
      intro h
      exact (List.nodup_cons.mp hnd).1 (by simp [h])
    have hmem : c ∈ (neighbors b).erase a :=
      Finset.mem_erase.mpr ⟨hcn,(mem_neighbors (hin b (by simp))).2 ⟨hc.tail.rel,hcin⟩⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨c,hmem,Finset.mem_image.mpr ⟨l,?_,rfl⟩⟩
    apply ih hc.tail hnd.tail
    intro v hv
    exact hin v (by simp only [List.mem_cons] at hv ⊢; tauto)

noncomputable def allPaths (n : ℕ) : Finset (List Vertex) :=
  (neighbors (.up 0 0)).biUnion fun b =>
    (continuations (.up 0 0) b (n-2)).image fun l => (.up 0 0) :: b :: l

lemma allPaths_card (n : ℕ) : ((allPaths n).card : ℝ) ≤ 128 * beta ^ n := by
  classical
  have hs : inside (.up 0 0) := by simp [inside,layer]
  calc ((allPaths n).card : ℝ)
      ≤ ∑ b ∈ neighbors (.up 0 0),
          (((continuations (.up 0 0) b (n-2)).image fun l => (.up 0 0) :: b :: l).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le :
          ((neighbors (.up 0 0)).biUnion fun b =>
            (continuations (.up 0 0) b (n-2)).image fun l => (.up 0 0) :: b :: l).card ≤ _)
    _ ≤ ∑ b ∈ neighbors (.up 0 0), 64 * beta ^ (n-2) := by
        apply Finset.sum_le_sum
        intro b hb
        obtain ⟨hadj,hbin⟩ := (mem_neighbors hs).1 hb
        have hcard : (((continuations (.up 0 0) b (n-2)).image
              fun l => (.up 0 0) :: b :: l).card : ℝ)
            ≤ ((continuations (.up 0 0) b (n-2)).card : ℝ) := by exact_mod_cast Finset.card_image_le
        exact (hcard.trans (continuations_card (n-2) _ _ hs hbin hadj)).trans
          (mul_le_mul_of_nonneg_right (edgeWeight_le_sixtyFour _ _)
            (pow_nonneg (le_trans (by norm_num) beta_ge_one) _))
    _ = 128 * beta ^ (n-2) := by simp [neighbors]; ring
    _ ≤ 128 * beta ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ beta_ge_one (by omega)) (by norm_num)

lemma path_mem_allPaths (p : BridgePath 4) : p.vertices ∈ allPaths p.vertices.length := by
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

lemma path_card_real (n : ℕ) (s : Finset (BridgePath 4))
    (hlen : ∀ p ∈ s, p.vertices.length = n) :
    (s.card : ℝ) ≤ 128 * beta ^ n := by
  classical
  have hm : Set.MapsTo (fun p : BridgePath 4 => p.vertices) (s : Set (BridgePath 4))
      (allPaths n : Set (List Vertex)) := by
    intro p hp
    change p.vertices ∈ allPaths n
    simpa only [hlen p hp] using path_mem_allPaths p
  have hi : Set.InjOn (fun p : BridgePath 4 => p.vertices) (s : Set (BridgePath 4)) := by
    intro p hp q hq he
    cases p
    cases q
    cases he
    rfl
  have hcard : (s.card : ℝ) ≤ ((allPaths n).card : ℝ) := by
    exact_mod_cast Finset.card_le_card_of_injOn _ hm hi
  exact hcard.trans (allPaths_card n)

lemma beta_lt_mu : beta < 2 * Real.cos (Real.pi / 8) := by
  have hs2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs2non : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hbr : beta ^ 2 - 2 < Real.sqrt 2 := by
    have hbpos : 0 < beta ^ 2 - 2 := by norm_num [beta]
    have hbsq : (beta ^ 2 - 2) ^ 2 < (2 : ℝ) := by norm_num [beta]
    nlinarith
  have hrnon : 0 ≤ Real.sqrt (2 + Real.sqrt 2) := Real.sqrt_nonneg _
  have hrsq : Real.sqrt (2 + Real.sqrt 2) ^ 2 = 2 + Real.sqrt 2 :=
    Real.sq_sqrt (by positivity)
  have hroot : beta < Real.sqrt (2 + Real.sqrt 2) := by
    have hbpos : 0 ≤ beta := le_trans (by norm_num) beta_ge_one
    nlinarith
  rw [Real.cos_pi_div_eight]
  linarith

theorem stripGrowthAtFour :
    ∃ C β : ℝ, 0 ≤ C ∧ 0 ≤ β ∧ β < 2 * Real.cos (Real.pi / 8) ∧
      ∀ (n : ℕ) (s : Finset (BridgePath 4)),
        (∀ p ∈ s, p.vertices.length = n) → (s.card : ℝ) ≤ C * β ^ n := by
  exact ⟨128, beta, by norm_num, le_trans (by norm_num) beta_ge_one,
    beta_lt_mu, path_card_real⟩

end WidthFour

/-- Fixed height four only; no all-height growth hypothesis is used. -/
theorem width_four_summability_diagnostic :
    Summable (weight (h := 4)) ∧ Summable (firstLengthWeight (h := 4)) := by
  obtain ⟨C, β, hC, hβ, hlt, hcount⟩ := WidthFour.stripGrowthAtFour
  have hL : Summable (firstLengthWeight (h := 4)) :=
    bridgeSummable_firstLengthWeight_of_mu_bound hC hβ hlt hcount
  exact ⟨bridgeSummable_weight_of_summable_firstLengthWeight hL,hL⟩

#check @WidthFour.mem_neighbors
#print axioms WidthFour.mem_neighbors
#check @WidthFour.edgeWeight_ge_one
#print axioms WidthFour.edgeWeight_ge_one
#check @WidthFour.edgeWeight_le_sixtyFour
#print axioms WidthFour.edgeWeight_le_sixtyFour
#check @WidthFour.potential_step
#print axioms WidthFour.potential_step
#check @WidthFour.continuations_card
#print axioms WidthFour.continuations_card
#check @WidthFour.mem_continuations
#print axioms WidthFour.mem_continuations
#check @WidthFour.allPaths_card
#print axioms WidthFour.allPaths_card
#check @WidthFour.path_mem_allPaths
#print axioms WidthFour.path_mem_allPaths
#check @WidthFour.path_card_real
#print axioms WidthFour.path_card_real
#check @WidthFour.beta_lt_mu
#print axioms WidthFour.beta_lt_mu
#check @WidthFour.stripGrowthAtFour
#print axioms WidthFour.stripGrowthAtFour
#check @width_four_summability_diagnostic
#print axioms width_four_summability_diagnostic
end PolynomialVacuumBridge.Corridor
end OAI
