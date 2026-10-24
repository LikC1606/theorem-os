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

namespace WidthFive

def inside : Vertex → Prop
  | .up _ j => 0 ≤ j ∧ j < 5
  | .down _ j => 0 ≤ j ∧ j < 5

lemma inside_iff (v : Vertex) : inside v ↔ 0 ≤ layer v ∧ layer v < 5 := by
  cases v <;> rfl

instance (v : Vertex) : Decidable (inside v) := by
  cases v <;> unfold inside <;> infer_instance

def rawNeighbors : Vertex → Finset Vertex
  | .up i j => {.down i (j-1), .down i j, .down (i-1) j}
  | .down i j => {.up i (j+1), .up i j, .up (i+1) j}

def neighbors (v : Vertex) : Finset Vertex := (rawNeighbors v).filter inside

lemma mem_neighbors {a b : Vertex} :
    b ∈ neighbors a ↔ adjacent a b ∧ inside b := by
  cases a <;> cases b <;>
    simp [neighbors, rawNeighbors, adjacent, inside, Vertex.up.injEq, Vertex.down.injEq] <;> omega

def shift (t : ℤ) : Vertex → Vertex
  | .up i j => .up (t+i) j
  | .down i j => .down (t+i) j

lemma shift_injective (t : ℤ) : Function.Injective (shift t) := by
  intro a b he
  cases a <;> cases b <;>
    simp [shift, Vertex.up.injEq, Vertex.down.injEq] at he ⊢ <;> tauto

@[simp] lemma inside_shift (t : ℤ) (v : Vertex) : inside (shift t v) ↔ inside v := by
  cases v <;> rfl

lemma neighbors_shift (t : ℤ) (b : Vertex) :
    neighbors (shift t b) = (neighbors b).image (shift t) := by
  have hr : rawNeighbors (shift t b) = (rawNeighbors b).image (shift t) := by
    cases b <;> simp [rawNeighbors, shift, add_sub_assoc, add_assoc]
  simp only [neighbors, hr, Finset.filter_image, inside_shift]

def last (w : List Vertex) : Vertex := w.getLastD (.up 0 0)

lemma last_eq_getLast {w : List Vertex} (hne : w ≠ []) :
    last w = w.getLast hne := by
  simp [last, List.getLast?_eq_some_getLast hne]

lemma last_shift (t : ℤ) {w : List Vertex} (hne : w ≠ []) :
    last (w.map (shift t)) = shift t (last w) := by
  simp [last, List.getLast?_map, List.getLast?_eq_some_getLast hne]

def horizontal : Vertex → ℤ
  | .up i _ => i
  | .down i _ => i

def origin (w : List Vertex) : ℤ := horizontal (last w)

def normalize (w : List Vertex) : List Vertex := w.map (shift (-origin w))

lemma normalize_shift (t : ℤ) {w : List Vertex} (hne : w ≠ []) :
    normalize (w.map (shift t)) = normalize w := by
  have ho : origin (w.map (shift t)) = t + origin w := by
    unfold origin
    rw [last_shift t hne]
    cases last w <;> rfl
  simp only [normalize, ho, List.map_map]
  apply List.map_congr_left
  intro v _
  cases v <;> simp [shift]

def candidates (w : List Vertex) : Finset Vertex :=
  (neighbors (last w)).filter (fun c => c ∉ w)

lemma candidates_shift (t : ℤ) {w : List Vertex} (hne : w ≠ []) :
    candidates (w.map (shift t)) = (candidates w).image (shift t) := by
  rw [candidates, last_shift t hne, neighbors_shift]
  ext v
  constructor
  · intro h
    obtain ⟨hin,hnot⟩ := Finset.mem_filter.mp h
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hin
    apply Finset.mem_image.mpr
    refine ⟨c, Finset.mem_filter.mpr ⟨hc, ?_⟩, rfl⟩
    intro hcw
    exact hnot (List.mem_map_of_mem hcw)
  · intro h
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hin,hnot⟩ := Finset.mem_filter.mp hc
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨c,hin,rfl⟩, ?_⟩
    intro hcw
    obtain ⟨d,hd,hde⟩ := List.mem_map.mp hcw
    exact hnot ((shift_injective t hde) ▸ hd)

def slide (w : List Vertex) (c : Vertex) : List Vertex :=
  (if w.length < 6 then w else w.tail) ++ [c]

lemma slide_ne_nil (w : List Vertex) (c : Vertex) : slide w c ≠ [] := by
  simp [slide]

lemma slide_shift (t : ℤ) (w : List Vertex) (c : Vertex) :
    slide (w.map (shift t)) (shift t c) = (slide w c).map (shift t) := by
  simp only [slide, List.length_map]
  split_ifs <;> simp [List.map_append]

def count (w : List Vertex) : ℕ → ℕ
  | 0 => 1
  | n+1 => ∑ c ∈ candidates w, count (slide w c) n

lemma count_shift (t : ℤ) (n : ℕ) (w : List Vertex) (hne : w ≠ []) :
    count (w.map (shift t)) n = count w n := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [count, candidates_shift t hne, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro c _
      rw [slide_shift]
      exact ih _ (slide_ne_nil w c)
    · intro c hc d hd he
      exact shift_injective t he


def table0 : List (List Vertex × ℕ) := [
  ([.up (0) 0], 2374603323719682490247505795183),
  ([.up (0) 0, .down (0) 0], 2192946169455126779743571601851),
  ([.up (1) 0, .down (0) 0], 2192946169455126779743571601851),
  ([.up (-1) 0, .down (-1) 0, .up (0) 0], 1196823800357469959127362198127),
  ([.up (0) 0, .down (0) 0, .up (0) 1], 2853547774626149203059014550491),
  ([.up (1) 0, .down (0) 0, .up (0) 0], 1196823800357469959127362198127),
  ([.up (1) 0, .down (0) 0, .up (0) 1], 2853547774626149203059014550491),
  ([.up (-1) 0, .down (-1) 0, .up (0) 0, .down (0) 0], 2210533559260247014508237979939),
  ([.up (0) 0, .down (0) 0, .up (0) 1, .down (0) 1], 2655101866512709734489499937378),
  ([.up (1) 0, .down (0) 0, .up (0) 1, .down (0) 1], 2615400873221787843560499937378),
  ([.up (1) 0, .down (1) 0, .up (1) 1, .down (0) 1], 2615400873221787843560499937378),
  ([.up (2) 0, .down (1) 0, .up (1) 0, .down (0) 0], 2210533559260247014508237979939)
]

def table1 : List (List Vertex × ℕ) := [
  ([.up (2) 0, .down (1) 0, .up (1) 1, .down (0) 1], 2655101866512709734489499937378),
  ([.up (-2) 0, .down (-2) 0, .up (-1) 0, .down (-1) 0, .up (0) 0], 1258124424490280717941286883036),
  ([.up (-1) 0, .down (-1) 0, .up (-1) 1, .down (-1) 1, .up (0) 1], 2030759268254691082659042093089),
  ([.up (-1) 0, .down (-1) 0, .up (0) 0, .down (0) 0, .up (0) 1], 2824731059463395517855428665910),
  ([.up (0) 0, .down (-1) 0, .up (-1) 1, .down (-1) 1, .up (0) 1], 1957431533646358350113179093089),
  ([.up (0) 0, .down (0) 0, .up (0) 1, .down (0) 1, .up (0) 2], 2873213879194283796943064291248),
  ([.up (1) 0, .down (0) 0, .up (0) 1, .down (0) 1, .up (0) 2], 2873213879194283796943064291248),
  ([.up (1) 0, .down (1) 0, .up (1) 1, .down (0) 1, .up (0) 1], 1957431533646358350113179093089),
  ([.up (1) 0, .down (1) 0, .up (1) 1, .down (0) 1, .up (0) 2], 2873213879194283796943064291248),
  ([.up (2) 0, .down (1) 0, .up (1) 0, .down (0) 0, .up (0) 0], 1258124424490280717941286883036),
  ([.up (2) 0, .down (1) 0, .up (1) 0, .down (0) 0, .up (0) 1], 2824731059463395517855428665910),
  ([.up (2) 0, .down (1) 0, .up (1) 1, .down (0) 1, .up (0) 1], 2030759268254691082659042093089)
]

def table2 : List (List Vertex × ℕ) := [
  ([.up (2) 0, .down (1) 0, .up (1) 1, .down (0) 1, .up (0) 2], 2873213879194283796943064291248),
  ([.up (-2) 0, .down (-2) 0, .up (-1) 0, .down (-1) 0, .up (0) 0, .down (0) 0], 2323755812033548486037556872967),
  ([.up (-2) 1, .down (-2) 0, .up (-1) 0, .down (-1) 0, .up (0) 0, .down (0) 0], 2323755812033548486037556872967),
  ([.up (-2) 1, .down (-2) 1, .up (-1) 1, .down (-1) 0, .up (0) 0, .down (0) 0], 2137778781428390588108556872967),
  ([.up (-2) 1, .down (-2) 1, .up (-1) 1, .down (-1) 1, .up (0) 1, .down (0) 0], 1267436670724753038704693872967),
  ([.up (-2) 1, .down (-2) 1, .up (-1) 1, .down (-1) 1, .up (0) 1, .down (0) 1], 2719015772532152021441419872967),
  ([.up (-2) 2, .down (-2) 1, .up (-1) 1, .down (-1) 0, .up (0) 0, .down (0) 0], 2137778781428390588108556872967),
  ([.up (-2) 2, .down (-2) 1, .up (-1) 1, .down (-1) 1, .up (0) 1, .down (0) 0], 1267436670724753038704693872967),
  ([.up (-2) 2, .down (-2) 1, .up (-1) 1, .down (-1) 1, .up (0) 1, .down (0) 1], 2719015772532152021441419872967),
  ([.up (-2) 2, .down (-2) 2, .up (-1) 2, .down (-1) 1, .up (0) 1, .down (0) 0], 1453413701329910936633693872967),
  ([.up (-2) 2, .down (-2) 2, .up (-1) 2, .down (-1) 1, .up (0) 1, .down (0) 1], 2529344741926994123512419872967),
  ([.up (-2) 2, .down (-2) 2, .up (-1) 2, .down (-1) 2, .up (0) 2, .down (0) 1], 2210507177606522109512419872967)
]

def table3 : List (List Vertex × ℕ) := [
  ([.up (-2) 2, .down (-2) 2, .up (-1) 2, .down (-1) 2, .up (0) 2, .down (0) 2], 2710195842315500035441419872967),
  ([.up (-2) 3, .down (-2) 2, .up (-1) 2, .down (-1) 1, .up (0) 1, .down (0) 0], 1453413701329910936633693872967),
  ([.up (-2) 3, .down (-2) 2, .up (-1) 2, .down (-1) 1, .up (0) 1, .down (0) 1], 2529344741926994123512419872967),
  ([.up (-2) 3, .down (-2) 2, .up (-1) 2, .down (-1) 2, .up (0) 2, .down (0) 1], 2210507177606522109512419872967),
  ([.up (-2) 3, .down (-2) 2, .up (-1) 2, .down (-1) 2, .up (0) 2, .down (0) 2], 2710195842315500035441419872967),
  ([.up (-2) 3, .down (-2) 3, .up (-1) 3, .down (-1) 2, .up (0) 2, .down (0) 1], 2400178208211680007441419872967),
  ([.up (-2) 3, .down (-2) 3, .up (-1) 3, .down (-1) 2, .up (0) 2, .down (0) 2], 2542735629710342137512419872967),
  ([.up (-2) 3, .down (-2) 3, .up (-1) 3, .down (-1) 3, .up (0) 3, .down (0) 2], 2725801690863466137512419872967),
  ([.up (-2) 3, .down (-2) 3, .up (-1) 3, .down (-1) 3, .up (0) 3, .down (0) 3], 2241191740168712225583419872967),
  ([.up (-2) 4, .down (-2) 3, .up (-1) 3, .down (-1) 2, .up (0) 2, .down (0) 1], 2400178208211680007441419872967),
  ([.up (-2) 4, .down (-2) 3, .up (-1) 3, .down (-1) 2, .up (0) 2, .down (0) 2], 2542735629710342137512419872967),
  ([.up (-2) 4, .down (-2) 3, .up (-1) 3, .down (-1) 3, .up (0) 3, .down (0) 2], 2725801690863466137512419872967)
]

def table4 : List (List Vertex × ℕ) := [
  ([.up (-2) 4, .down (-2) 3, .up (-1) 3, .down (-1) 3, .up (0) 3, .down (0) 3], 2241191740168712225583419872967),
  ([.up (-2) 4, .down (-2) 4, .up (-1) 4, .down (-1) 3, .up (0) 3, .down (0) 2], 2893261903468624035441419872967),
  ([.up (-2) 4, .down (-2) 4, .up (-1) 4, .down (-1) 3, .up (0) 3, .down (0) 3], 2124440210774835327654419872967),
  ([.up (-2) 4, .down (-2) 4, .up (-1) 4, .down (-1) 4, .up (0) 4, .down (0) 3], 2831243620824904137512419872967),
  ([.up (-2) 4, .down (-2) 4, .up (-1) 4, .down (-1) 4, .up (0) 4, .down (0) 4], 1389704663166353495692484911967),
  ([.up (-1) 0, .down (-1) 0, .up (-1) 1, .down (-1) 1, .up (0) 1, .down (0) 0], 1031796595934262408229830872967),
  ([.up (-1) 0, .down (-1) 0, .up (-1) 1, .down (-1) 1, .up (0) 1, .down (0) 1], 2719015772532152021441419872967),
  ([.up (-1) 0, .down (-1) 0, .up (0) 0, .down (0) 0, .up (0) 1, .down (0) 1], 2742680462955152021441419872967),
  ([.up (-1) 1, .down (-1) 0, .up (0) 0, .down (0) 0, .up (0) 1, .down (0) 1], 2742680462955152021441419872967),
  ([.up (-1) 1, .down (-1) 1, .up (-1) 2, .down (-1) 2, .up (0) 2, .down (0) 1], 1869208164924795472037556872967),
  ([.up (-1) 1, .down (-1) 1, .up (-1) 2, .down (-1) 2, .up (0) 2, .down (0) 2], 2710195842315500035441419872967),
  ([.up (-1) 1, .down (-1) 1, .up (0) 1, .down (0) 1, .up (0) 2, .down (0) 2], 2717889842315500035441419872967)
]

def table5 : List (List Vertex × ℕ) := [
  ([.up (-1) 2, .down (-1) 1, .up (-1) 1, .down (-1) 0, .up (0) 0, .down (0) 0], 1732068387900663950633693872967),
  ([.up (-1) 2, .down (-1) 1, .up (0) 1, .down (0) 1, .up (0) 2, .down (0) 2], 2717889842315500035441419872967),
  ([.up (-1) 2, .down (-1) 2, .up (-1) 3, .down (-1) 3, .up (0) 3, .down (0) 2], 2331479297335739500037556872967),
  ([.up (-1) 2, .down (-1) 2, .up (-1) 3, .down (-1) 3, .up (0) 3, .down (0) 3], 2241191740168712225583419872967),
  ([.up (-1) 2, .down (-1) 2, .up (0) 2, .down (0) 1, .up (0) 1, .down (0) 0], 1453413701329910936633693872967),
  ([.up (-1) 2, .down (-1) 2, .up (0) 2, .down (0) 2, .up (0) 3, .down (0) 3], 2239191740168712225583419872967),
  ([.up (-1) 3, .down (-1) 2, .up (-1) 2, .down (-1) 1, .up (0) 1, .down (0) 0], 1453413701329910936633693872967),
  ([.up (-1) 3, .down (-1) 2, .up (-1) 2, .down (-1) 1, .up (0) 1, .down (0) 1], 2168055984399267486037556872967),
  ([.up (-1) 3, .down (-1) 2, .up (0) 2, .down (0) 1, .up (0) 1, .down (0) 0], 1453413701329910936633693872967),
  ([.up (-1) 3, .down (-1) 2, .up (0) 2, .down (0) 2, .up (0) 3, .down (0) 3], 2239191740168712225583419872967),
  ([.up (-1) 3, .down (-1) 3, .up (-1) 4, .down (-1) 4, .up (0) 4, .down (0) 3], 2443744045297177500037556872967),
  ([.up (-1) 3, .down (-1) 3, .up (-1) 4, .down (-1) 4, .up (0) 4, .down (0) 4], 1389704663166353495692484911967)
]

def table6 : List (List Vertex × ℕ) := [
  ([.up (-1) 3, .down (-1) 3, .up (0) 3, .down (0) 2, .up (0) 2, .down (0) 1], 2400178208211680007441419872967),
  ([.up (-1) 3, .down (-1) 3, .up (0) 3, .down (0) 3, .up (0) 4, .down (0) 4], 1302548718063398488692484911967),
  ([.up (-1) 4, .down (-1) 3, .up (-1) 3, .down (-1) 2, .up (0) 2, .down (0) 1], 2400178208211680007441419872967),
  ([.up (-1) 4, .down (-1) 3, .up (-1) 3, .down (-1) 2, .up (0) 2, .down (0) 2], 2288558238605177500037556872967),
  ([.up (-1) 4, .down (-1) 3, .up (0) 3, .down (0) 2, .up (0) 2, .down (0) 1], 2400178208211680007441419872967),
  ([.up (-1) 4, .down (-1) 3, .up (0) 3, .down (0) 3, .up (0) 4, .down (0) 4], 1302548718063398488692484911967),
  ([.up (-1) 4, .down (-1) 4, .up (0) 4, .down (0) 3, .up (0) 3, .down (0) 2], 2893261903468624035441419872967),
  ([.up (0) 0, .down (-1) 0, .up (-1) 1, .down (-1) 1, .up (0) 1, .down (0) 0], 896360270112671851217621911967),
  ([.up (0) 0, .down (-1) 0, .up (-1) 1, .down (-1) 1, .up (0) 1, .down (0) 1], 2719015772532152021441419872967),
  ([.up (0) 0, .down (0) 0, .up (0) 1, .down (0) 1, .up (0) 2, .down (0) 2], 2717889842315500035441419872967),
  ([.up (0) 0, .down (0) 0, .up (1) 0, .down (1) 0, .up (1) 1, .down (0) 1], 2474597803873739500037556872967),
  ([.up (0) 1, .down (-1) 1, .up (-1) 1, .down (-1) 0, .up (0) 0, .down (0) 0], 936509671900952851217621911967)
]

def table7 : List (List Vertex × ℕ) := [
  ([.up (0) 1, .down (-1) 1, .up (-1) 2, .down (-1) 2, .up (0) 2, .down (0) 1], 1367742523553556386621484911967),
  ([.up (0) 1, .down (-1) 1, .up (-1) 2, .down (-1) 2, .up (0) 2, .down (0) 2], 2710195842315500035441419872967),
  ([.up (0) 1, .down (0) 0, .up (1) 0, .down (1) 0, .up (1) 1, .down (0) 1], 1682886087874028400621484911967),
  ([.up (0) 1, .down (0) 1, .up (0) 2, .down (0) 2, .up (0) 3, .down (0) 3], 2239191740168712225583419872967),
  ([.up (0) 1, .down (0) 1, .up (1) 1, .down (1) 0, .up (1) 0, .down (0) 0], 936509671900952851217621911967),
  ([.up (0) 1, .down (0) 1, .up (1) 1, .down (1) 1, .up (1) 2, .down (0) 2], 2247637179874615500037556872967),
  ([.up (0) 2, .down (-1) 2, .up (-1) 2, .down (-1) 1, .up (0) 1, .down (0) 0], 1453413701329910936633693872967),
  ([.up (0) 2, .down (-1) 2, .up (-1) 2, .down (-1) 1, .up (0) 1, .down (0) 1], 1367742523553556386621484911967),
  ([.up (0) 2, .down (-1) 2, .up (-1) 3, .down (-1) 3, .up (0) 3, .down (0) 2], 1604178962182028400621484911967),
  ([.up (0) 2, .down (-1) 2, .up (-1) 3, .down (-1) 3, .up (0) 3, .down (0) 3], 2241191740168712225583419872967),
  ([.up (0) 2, .down (0) 1, .up (1) 1, .down (1) 0, .up (1) 0, .down (0) 0], 1732068387900663950633693872967),
  ([.up (0) 2, .down (0) 1, .up (1) 1, .down (1) 1, .up (1) 2, .down (0) 2], 1447323719028904400621484911967)
]

def table8 : List (List Vertex × ℕ) := [
  ([.up (0) 2, .down (0) 2, .up (0) 3, .down (0) 3, .up (0) 4, .down (0) 4], 1302548718063398488692484911967),
  ([.up (0) 2, .down (0) 2, .up (1) 2, .down (1) 1, .up (1) 1, .down (0) 1], 1367742523553556386621484911967),
  ([.up (0) 2, .down (0) 2, .up (1) 2, .down (1) 2, .up (1) 3, .down (0) 3], 1666586316035827690179556872967),
  ([.up (0) 3, .down (-1) 3, .up (-1) 3, .down (-1) 2, .up (0) 2, .down (0) 1], 2400178208211680007441419872967),
  ([.up (0) 3, .down (-1) 3, .up (-1) 3, .down (-1) 2, .up (0) 2, .down (0) 2], 1602178962182028400621484911967),
  ([.up (0) 3, .down (-1) 3, .up (-1) 4, .down (-1) 4, .up (0) 4, .down (0) 3], 1608396948451466400621484911967),
  ([.up (0) 3, .down (-1) 3, .up (-1) 4, .down (-1) 4, .up (0) 4, .down (0) 4], 1389704663166353495692484911967),
  ([.up (0) 3, .down (0) 2, .up (0) 2, .down (0) 1, .up (0) 1, .down (0) 0], 1453413701329910936633693872967),
  ([.up (0) 3, .down (0) 2, .up (1) 2, .down (1) 1, .up (1) 1, .down (0) 1], 2168055984399267486037556872967),
  ([.up (0) 3, .down (0) 2, .up (1) 2, .down (1) 2, .up (1) 3, .down (0) 3], 980207039612678590763484911967),
  ([.up (0) 3, .down (0) 3, .up (1) 3, .down (1) 2, .up (1) 2, .down (0) 2], 1602178962182028400621484911967),
  ([.up (0) 3, .down (0) 3, .up (1) 3, .down (1) 3, .up (1) 4, .down (0) 4], 720378111930513953288621911967)
]

def table9 : List (List Vertex × ℕ) := [
  ([.up (0) 4, .down (-1) 4, .up (-1) 4, .down (-1) 3, .up (0) 3, .down (0) 2], 2893261903468624035441419872967),
  ([.up (0) 4, .down (-1) 4, .up (-1) 4, .down (-1) 3, .up (0) 3, .down (0) 3], 1598291539451466400621484911967),
  ([.up (0) 4, .down (0) 3, .up (0) 3, .down (0) 2, .up (0) 2, .down (0) 1], 2400178208211680007441419872967),
  ([.up (0) 4, .down (0) 3, .up (1) 3, .down (1) 2, .up (1) 2, .down (0) 2], 2288558238605177500037556872967),
  ([.up (0) 4, .down (0) 3, .up (1) 3, .down (1) 3, .up (1) 4, .down (0) 4], 250150893792477758801549950967),
  ([.up (0) 4, .down (0) 4, .up (1) 4, .down (1) 3, .up (1) 3, .down (0) 3], 1598291539451466400621484911967),
  ([.up (1) 0, .down (0) 0, .up (0) 1, .down (0) 1, .up (0) 2, .down (0) 2], 2717889842315500035441419872967),
  ([.up (1) 0, .down (1) 0, .up (1) 1, .down (0) 1, .up (0) 1, .down (0) 0], 896360270112671851217621911967),
  ([.up (1) 0, .down (1) 0, .up (1) 1, .down (0) 1, .up (0) 2, .down (0) 2], 2588936192556342137512419872967),
  ([.up (1) 0, .down (1) 0, .up (1) 1, .down (1) 1, .up (1) 2, .down (0) 2], 2588936192556342137512419872967),
  ([.up (1) 1, .down (0) 1, .up (0) 2, .down (0) 2, .up (0) 3, .down (0) 3], 2239191740168712225583419872967),
  ([.up (1) 1, .down (1) 0, .up (1) 0, .down (0) 0, .up (0) 1, .down (0) 1], 1682886087874028400621484911967)
]

def table10 : List (List Vertex × ℕ) := [
  ([.up (1) 1, .down (1) 1, .up (1) 2, .down (0) 2, .up (0) 2, .down (0) 1], 1367742523553556386621484911967),
  ([.up (1) 1, .down (1) 1, .up (1) 2, .down (0) 2, .up (0) 3, .down (0) 3], 2060908709563554327654419872967),
  ([.up (1) 1, .down (1) 1, .up (1) 2, .down (1) 2, .up (1) 3, .down (0) 3], 2060908709563554327654419872967),
  ([.up (1) 2, .down (0) 2, .up (0) 2, .down (0) 1, .up (0) 1, .down (0) 0], 1453413701329910936633693872967),
  ([.up (1) 2, .down (0) 2, .up (0) 3, .down (0) 3, .up (0) 4, .down (0) 4], 1302548718063398488692484911967),
  ([.up (1) 2, .down (1) 1, .up (1) 1, .down (0) 1, .up (0) 1, .down (0) 0], 1267436670724753038704693872967),
  ([.up (1) 2, .down (1) 1, .up (1) 1, .down (0) 1, .up (0) 2, .down (0) 2], 1447323719028904400621484911967),
  ([.up (1) 2, .down (1) 1, .up (1) 1, .down (1) 0, .up (1) 0, .down (0) 0], 2137778781428390588108556872967),
  ([.up (1) 2, .down (1) 2, .up (1) 3, .down (0) 3, .up (0) 3, .down (0) 2], 1604178962182028400621484911967),
  ([.up (1) 2, .down (1) 2, .up (1) 3, .down (0) 3, .up (0) 4, .down (0) 4], 1108877687458240590763484911967),
  ([.up (1) 2, .down (1) 2, .up (1) 3, .down (1) 3, .up (1) 4, .down (0) 4], 1108877687458240590763484911967),
  ([.up (1) 3, .down (0) 3, .up (0) 3, .down (0) 2, .up (0) 2, .down (0) 1], 2400178208211680007441419872967)
]

def table11 : List (List Vertex × ℕ) := [
  ([.up (1) 3, .down (1) 2, .up (1) 2, .down (0) 2, .up (0) 2, .down (0) 1], 2210507177606522109512419872967),
  ([.up (1) 3, .down (1) 2, .up (1) 2, .down (0) 2, .up (0) 3, .down (0) 3], 980207039612678590763484911967),
  ([.up (1) 3, .down (1) 2, .up (1) 2, .down (1) 1, .up (1) 1, .down (0) 1], 2529344741926994123512419872967),
  ([.up (1) 3, .down (1) 3, .up (1) 4, .down (0) 4, .up (0) 4, .down (0) 3], 1608396948451466400621484911967),
  ([.up (1) 4, .down (0) 4, .up (0) 4, .down (0) 3, .up (0) 3, .down (0) 2], 2893261903468624035441419872967),
  ([.up (1) 4, .down (1) 3, .up (1) 3, .down (0) 3, .up (0) 3, .down (0) 2], 2725801690863466137512419872967),
  ([.up (1) 4, .down (1) 3, .up (1) 3, .down (0) 3, .up (0) 4, .down (0) 4], 250150893792477758801549950967),
  ([.up (1) 4, .down (1) 3, .up (1) 3, .down (1) 2, .up (1) 2, .down (0) 2], 2542735629710342137512419872967),
  ([.up (2) 0, .down (1) 0, .up (1) 0, .down (0) 0, .up (0) 1, .down (0) 1], 2474597803873739500037556872967),
  ([.up (2) 0, .down (1) 0, .up (1) 1, .down (0) 1, .up (0) 1, .down (0) 0], 1031796595934262408229830872967),
  ([.up (2) 0, .down (1) 0, .up (1) 1, .down (0) 1, .up (0) 2, .down (0) 2], 2588936192556342137512419872967),
  ([.up (2) 0, .down (1) 0, .up (1) 1, .down (1) 1, .up (1) 2, .down (0) 2], 2588936192556342137512419872967)
]

def table12 : List (List Vertex × ℕ) := [
  ([.up (2) 0, .down (2) 0, .up (2) 1, .down (1) 1, .up (1) 1, .down (0) 1], 2719015772532152021441419872967),
  ([.up (2) 0, .down (2) 0, .up (2) 1, .down (1) 1, .up (1) 2, .down (0) 2], 2717889842315500035441419872967),
  ([.up (2) 1, .down (1) 1, .up (1) 1, .down (0) 1, .up (0) 1, .down (0) 0], 1267436670724753038704693872967),
  ([.up (2) 1, .down (1) 1, .up (1) 1, .down (0) 1, .up (0) 2, .down (0) 2], 2247637179874615500037556872967),
  ([.up (2) 1, .down (1) 1, .up (1) 1, .down (1) 0, .up (1) 0, .down (0) 0], 2137778781428390588108556872967),
  ([.up (2) 1, .down (1) 1, .up (1) 2, .down (0) 2, .up (0) 2, .down (0) 1], 1869208164924795472037556872967),
  ([.up (2) 1, .down (1) 1, .up (1) 2, .down (0) 2, .up (0) 3, .down (0) 3], 2060908709563554327654419872967),
  ([.up (2) 1, .down (1) 1, .up (1) 2, .down (1) 2, .up (1) 3, .down (0) 3], 2060908709563554327654419872967),
  ([.up (2) 1, .down (2) 0, .up (2) 0, .down (1) 0, .up (1) 0, .down (0) 0], 2323755812033548486037556872967),
  ([.up (2) 1, .down (2) 0, .up (2) 0, .down (1) 0, .up (1) 1, .down (0) 1], 2742680462955152021441419872967),
  ([.up (2) 1, .down (2) 1, .up (2) 2, .down (1) 2, .up (1) 2, .down (0) 2], 2710195842315500035441419872967),
  ([.up (2) 1, .down (2) 1, .up (2) 2, .down (1) 2, .up (1) 3, .down (0) 3], 2239191740168712225583419872967)
]

def table13 : List (List Vertex × ℕ) := [
  ([.up (2) 2, .down (1) 2, .up (1) 2, .down (0) 2, .up (0) 2, .down (0) 1], 2210507177606522109512419872967),
  ([.up (2) 2, .down (1) 2, .up (1) 2, .down (0) 2, .up (0) 3, .down (0) 3], 1666586316035827690179556872967),
  ([.up (2) 2, .down (1) 2, .up (1) 2, .down (1) 1, .up (1) 1, .down (0) 1], 2529344741926994123512419872967),
  ([.up (2) 2, .down (1) 2, .up (1) 3, .down (0) 3, .up (0) 3, .down (0) 2], 2331479297335739500037556872967),
  ([.up (2) 2, .down (1) 2, .up (1) 3, .down (0) 3, .up (0) 4, .down (0) 4], 1108877687458240590763484911967),
  ([.up (2) 2, .down (1) 2, .up (1) 3, .down (1) 3, .up (1) 4, .down (0) 4], 1108877687458240590763484911967),
  ([.up (2) 2, .down (2) 1, .up (2) 1, .down (1) 1, .up (1) 1, .down (0) 1], 2719015772532152021441419872967),
  ([.up (2) 2, .down (2) 1, .up (2) 1, .down (1) 1, .up (1) 2, .down (0) 2], 2717889842315500035441419872967),
  ([.up (2) 2, .down (2) 2, .up (2) 3, .down (1) 3, .up (1) 3, .down (0) 3], 2241191740168712225583419872967),
  ([.up (2) 2, .down (2) 2, .up (2) 3, .down (1) 3, .up (1) 4, .down (0) 4], 1302548718063398488692484911967),
  ([.up (2) 3, .down (1) 3, .up (1) 3, .down (0) 3, .up (0) 3, .down (0) 2], 2725801690863466137512419872967),
  ([.up (2) 3, .down (1) 3, .up (1) 3, .down (0) 3, .up (0) 4, .down (0) 4], 720378111930513953288621911967)
]

def table14 : List (List Vertex × ℕ) := [
  ([.up (2) 3, .down (1) 3, .up (1) 3, .down (1) 2, .up (1) 2, .down (0) 2], 2542735629710342137512419872967),
  ([.up (2) 3, .down (1) 3, .up (1) 4, .down (0) 4, .up (0) 4, .down (0) 3], 2443744045297177500037556872967),
  ([.up (2) 3, .down (2) 2, .up (2) 2, .down (1) 2, .up (1) 2, .down (0) 2], 2710195842315500035441419872967),
  ([.up (2) 3, .down (2) 2, .up (2) 2, .down (1) 2, .up (1) 3, .down (0) 3], 2239191740168712225583419872967),
  ([.up (2) 3, .down (2) 3, .up (2) 4, .down (1) 4, .up (1) 4, .down (0) 4], 1389704663166353495692484911967),
  ([.up (2) 4, .down (1) 4, .up (1) 4, .down (0) 4, .up (0) 4, .down (0) 3], 2831243620824904137512419872967),
  ([.up (2) 4, .down (1) 4, .up (1) 4, .down (1) 3, .up (1) 3, .down (0) 3], 2124440210774835327654419872967),
  ([.up (2) 4, .down (2) 3, .up (2) 3, .down (1) 3, .up (1) 3, .down (0) 3], 2241191740168712225583419872967),
  ([.up (2) 4, .down (2) 3, .up (2) 3, .down (1) 3, .up (1) 4, .down (0) 4], 1302548718063398488692484911967),
  ([.up (3) 0, .down (2) 0, .up (2) 0, .down (1) 0, .up (1) 0, .down (0) 0], 2323755812033548486037556872967),
  ([.up (3) 0, .down (2) 0, .up (2) 0, .down (1) 0, .up (1) 1, .down (0) 1], 2742680462955152021441419872967),
  ([.up (3) 0, .down (2) 0, .up (2) 1, .down (1) 1, .up (1) 1, .down (0) 1], 2719015772532152021441419872967)
]

def table15 : List (List Vertex × ℕ) := [
  ([.up (3) 0, .down (2) 0, .up (2) 1, .down (1) 1, .up (1) 2, .down (0) 2], 2717889842315500035441419872967),
  ([.up (3) 1, .down (2) 1, .up (2) 1, .down (1) 1, .up (1) 1, .down (0) 1], 2719015772532152021441419872967),
  ([.up (3) 1, .down (2) 1, .up (2) 1, .down (1) 1, .up (1) 2, .down (0) 2], 2717889842315500035441419872967),
  ([.up (3) 1, .down (2) 1, .up (2) 2, .down (1) 2, .up (1) 2, .down (0) 2], 2710195842315500035441419872967),
  ([.up (3) 1, .down (2) 1, .up (2) 2, .down (1) 2, .up (1) 3, .down (0) 3], 2239191740168712225583419872967),
  ([.up (3) 2, .down (2) 2, .up (2) 2, .down (1) 2, .up (1) 2, .down (0) 2], 2710195842315500035441419872967),
  ([.up (3) 2, .down (2) 2, .up (2) 2, .down (1) 2, .up (1) 3, .down (0) 3], 2239191740168712225583419872967),
  ([.up (3) 2, .down (2) 2, .up (2) 3, .down (1) 3, .up (1) 3, .down (0) 3], 2241191740168712225583419872967),
  ([.up (3) 2, .down (2) 2, .up (2) 3, .down (1) 3, .up (1) 4, .down (0) 4], 1302548718063398488692484911967),
  ([.up (3) 3, .down (2) 3, .up (2) 3, .down (1) 3, .up (1) 3, .down (0) 3], 2241191740168712225583419872967),
  ([.up (3) 3, .down (2) 3, .up (2) 3, .down (1) 3, .up (1) 4, .down (0) 4], 1302548718063398488692484911967),
  ([.up (3) 3, .down (2) 3, .up (2) 4, .down (1) 4, .up (1) 4, .down (0) 4], 1389704663166353495692484911967)
]

def table16 : List (List Vertex × ℕ) := [
  ([.up (3) 4, .down (2) 4, .up (2) 4, .down (1) 4, .up (1) 4, .down (0) 4], 1389704663166353495692484911967),
  ([.down (-3) 0, .up (-2) 0, .down (-2) 0, .up (-1) 0, .down (-1) 0, .up (0) 0], 1389704663166353495692484911967),
  ([.down (-3) 1, .up (-2) 1, .down (-2) 0, .up (-1) 0, .down (-1) 0, .up (0) 0], 1389704663166353495692484911967),
  ([.down (-3) 1, .up (-2) 1, .down (-2) 1, .up (-1) 1, .down (-1) 0, .up (0) 0], 1302548718063398488692484911967),
  ([.down (-3) 1, .up (-2) 1, .down (-2) 1, .up (-1) 1, .down (-1) 1, .up (0) 1], 2241191740168712225583419872967),
  ([.down (-3) 2, .up (-2) 2, .down (-2) 1, .up (-1) 1, .down (-1) 0, .up (0) 0], 1302548718063398488692484911967),
  ([.down (-3) 2, .up (-2) 2, .down (-2) 1, .up (-1) 1, .down (-1) 1, .up (0) 1], 2241191740168712225583419872967),
  ([.down (-3) 2, .up (-2) 2, .down (-2) 2, .up (-1) 2, .down (-1) 1, .up (0) 1], 2239191740168712225583419872967),
  ([.down (-3) 2, .up (-2) 2, .down (-2) 2, .up (-1) 2, .down (-1) 2, .up (0) 2], 2710195842315500035441419872967),
  ([.down (-3) 3, .up (-2) 3, .down (-2) 2, .up (-1) 2, .down (-1) 1, .up (0) 1], 2239191740168712225583419872967),
  ([.down (-3) 3, .up (-2) 3, .down (-2) 2, .up (-1) 2, .down (-1) 2, .up (0) 2], 2710195842315500035441419872967),
  ([.down (-3) 3, .up (-2) 3, .down (-2) 3, .up (-1) 3, .down (-1) 2, .up (0) 2], 2717889842315500035441419872967)
]

def table17 : List (List Vertex × ℕ) := [
  ([.down (-3) 3, .up (-2) 3, .down (-2) 3, .up (-1) 3, .down (-1) 3, .up (0) 3], 2719015772532152021441419872967),
  ([.down (-3) 4, .up (-2) 4, .down (-2) 3, .up (-1) 3, .down (-1) 2, .up (0) 2], 2717889842315500035441419872967),
  ([.down (-3) 4, .up (-2) 4, .down (-2) 3, .up (-1) 3, .down (-1) 3, .up (0) 3], 2719015772532152021441419872967),
  ([.down (-3) 4, .up (-2) 4, .down (-2) 4, .up (-1) 4, .down (-1) 3, .up (0) 3], 2742680462955152021441419872967),
  ([.down (-3) 4, .up (-2) 4, .down (-2) 4, .up (-1) 4, .down (-1) 4, .up (0) 4], 2323755812033548486037556872967),
  ([.down (-2) 0, .up (-2) 1, .down (-2) 1, .up (-1) 1, .down (-1) 0, .up (0) 0], 1302548718063398488692484911967),
  ([.down (-2) 0, .up (-2) 1, .down (-2) 1, .up (-1) 1, .down (-1) 1, .up (0) 1], 2241191740168712225583419872967),
  ([.down (-2) 0, .up (-1) 0, .down (-1) 0, .up (-1) 1, .down (-1) 1, .up (0) 1], 2124440210774835327654419872967),
  ([.down (-2) 0, .up (-1) 0, .down (-1) 0, .up (0) 0, .down (0) 0, .up (0) 1], 2831243620824904137512419872967),
  ([.down (-2) 1, .up (-2) 1, .down (-2) 0, .up (-1) 0, .down (-1) 0, .up (0) 0], 1389704663166353495692484911967),
  ([.down (-2) 1, .up (-2) 2, .down (-2) 2, .up (-1) 2, .down (-1) 1, .up (0) 1], 2239191740168712225583419872967),
  ([.down (-2) 1, .up (-2) 2, .down (-2) 2, .up (-1) 2, .down (-1) 2, .up (0) 2], 2710195842315500035441419872967)
]

def table18 : List (List Vertex × ℕ) := [
  ([.down (-2) 1, .up (-1) 1, .down (-1) 0, .up (0) 0, .down (0) 0, .up (0) 1], 2443744045297177500037556872967),
  ([.down (-2) 1, .up (-1) 1, .down (-1) 1, .up (-1) 2, .down (-1) 2, .up (0) 2], 2542735629710342137512419872967),
  ([.down (-2) 1, .up (-1) 1, .down (-1) 1, .up (0) 1, .down (0) 0, .up (0) 0], 720378111930513953288621911967),
  ([.down (-2) 1, .up (-1) 1, .down (-1) 1, .up (0) 1, .down (0) 1, .up (0) 2], 2725801690863466137512419872967),
  ([.down (-2) 2, .up (-2) 2, .down (-2) 1, .up (-1) 1, .down (-1) 0, .up (0) 0], 1302548718063398488692484911967),
  ([.down (-2) 2, .up (-2) 2, .down (-2) 1, .up (-1) 1, .down (-1) 1, .up (0) 1], 2241191740168712225583419872967),
  ([.down (-2) 2, .up (-2) 3, .down (-2) 3, .up (-1) 3, .down (-1) 2, .up (0) 2], 2717889842315500035441419872967),
  ([.down (-2) 2, .up (-2) 3, .down (-2) 3, .up (-1) 3, .down (-1) 3, .up (0) 3], 2719015772532152021441419872967),
  ([.down (-2) 2, .up (-1) 2, .down (-1) 1, .up (-1) 1, .down (-1) 0, .up (0) 0], 1108877687458240590763484911967),
  ([.down (-2) 2, .up (-1) 2, .down (-1) 1, .up (0) 1, .down (0) 0, .up (0) 0], 1108877687458240590763484911967),
  ([.down (-2) 2, .up (-1) 2, .down (-1) 1, .up (0) 1, .down (0) 1, .up (0) 2], 2331479297335739500037556872967),
  ([.down (-2) 2, .up (-1) 2, .down (-1) 2, .up (-1) 3, .down (-1) 3, .up (0) 3], 2529344741926994123512419872967)
]

def table19 : List (List Vertex × ℕ) := [
  ([.down (-2) 2, .up (-1) 2, .down (-1) 2, .up (0) 2, .down (0) 1, .up (0) 1], 1666586316035827690179556872967),
  ([.down (-2) 2, .up (-1) 2, .down (-1) 2, .up (0) 2, .down (0) 2, .up (0) 3], 2210507177606522109512419872967),
  ([.down (-2) 3, .up (-2) 3, .down (-2) 2, .up (-1) 2, .down (-1) 1, .up (0) 1], 2239191740168712225583419872967),
  ([.down (-2) 3, .up (-2) 3, .down (-2) 2, .up (-1) 2, .down (-1) 2, .up (0) 2], 2710195842315500035441419872967),
  ([.down (-2) 3, .up (-2) 4, .down (-2) 4, .up (-1) 4, .down (-1) 3, .up (0) 3], 2742680462955152021441419872967),
  ([.down (-2) 3, .up (-2) 4, .down (-2) 4, .up (-1) 4, .down (-1) 4, .up (0) 4], 2323755812033548486037556872967),
  ([.down (-2) 3, .up (-1) 3, .down (-1) 2, .up (-1) 2, .down (-1) 1, .up (0) 1], 2060908709563554327654419872967),
  ([.down (-2) 3, .up (-1) 3, .down (-1) 2, .up (0) 2, .down (0) 1, .up (0) 1], 2060908709563554327654419872967),
  ([.down (-2) 3, .up (-1) 3, .down (-1) 2, .up (0) 2, .down (0) 2, .up (0) 3], 1869208164924795472037556872967),
  ([.down (-2) 3, .up (-1) 3, .down (-1) 3, .up (-1) 4, .down (-1) 4, .up (0) 4], 2137778781428390588108556872967),
  ([.down (-2) 3, .up (-1) 3, .down (-1) 3, .up (0) 3, .down (0) 2, .up (0) 2], 2247637179874615500037556872967),
  ([.down (-2) 3, .up (-1) 3, .down (-1) 3, .up (0) 3, .down (0) 3, .up (0) 4], 1267436670724753038704693872967)
]

def table20 : List (List Vertex × ℕ) := [
  ([.down (-2) 4, .up (-2) 4, .down (-2) 3, .up (-1) 3, .down (-1) 2, .up (0) 2], 2717889842315500035441419872967),
  ([.down (-2) 4, .up (-2) 4, .down (-2) 3, .up (-1) 3, .down (-1) 3, .up (0) 3], 2719015772532152021441419872967),
  ([.down (-2) 4, .up (-1) 4, .down (-1) 3, .up (-1) 3, .down (-1) 2, .up (0) 2], 2588936192556342137512419872967),
  ([.down (-2) 4, .up (-1) 4, .down (-1) 3, .up (0) 3, .down (0) 2, .up (0) 2], 2588936192556342137512419872967),
  ([.down (-2) 4, .up (-1) 4, .down (-1) 3, .up (0) 3, .down (0) 3, .up (0) 4], 1031796595934262408229830872967),
  ([.down (-2) 4, .up (-1) 4, .down (-1) 4, .up (0) 4, .down (0) 3, .up (0) 3], 2474597803873739500037556872967),
  ([.down (-1) 0, .up (-1) 1, .down (-1) 1, .up (-1) 2, .down (-1) 2, .up (0) 2], 2542735629710342137512419872967),
  ([.down (-1) 0, .up (-1) 1, .down (-1) 1, .up (0) 1, .down (0) 0, .up (0) 0], 250150893792477758801549950967),
  ([.down (-1) 0, .up (-1) 1, .down (-1) 1, .up (0) 1, .down (0) 1, .up (0) 2], 2725801690863466137512419872967),
  ([.down (-1) 0, .up (0) 0, .down (0) 0, .up (0) 1, .down (0) 1, .up (0) 2], 2893261903468624035441419872967),
  ([.down (-1) 1, .up (-1) 1, .down (-1) 0, .up (0) 0, .down (0) 0, .up (0) 1], 1608396948451466400621484911967),
  ([.down (-1) 1, .up (-1) 2, .down (-1) 2, .up (-1) 3, .down (-1) 3, .up (0) 3], 2529344741926994123512419872967)
]

def table21 : List (List Vertex × ℕ) := [
  ([.down (-1) 1, .up (-1) 2, .down (-1) 2, .up (0) 2, .down (0) 1, .up (0) 1], 980207039612678590763484911967),
  ([.down (-1) 1, .up (-1) 2, .down (-1) 2, .up (0) 2, .down (0) 2, .up (0) 3], 2210507177606522109512419872967),
  ([.down (-1) 1, .up (0) 1, .down (0) 1, .up (0) 2, .down (0) 2, .up (0) 3], 2400178208211680007441419872967),
  ([.down (-1) 2, .up (-1) 2, .down (-1) 1, .up (-1) 1, .down (-1) 0, .up (0) 0], 1108877687458240590763484911967),
  ([.down (-1) 2, .up (-1) 2, .down (-1) 1, .up (0) 1, .down (0) 0, .up (0) 0], 1108877687458240590763484911967),
  ([.down (-1) 2, .up (-1) 2, .down (-1) 1, .up (0) 1, .down (0) 1, .up (0) 2], 1604178962182028400621484911967),
  ([.down (-1) 2, .up (-1) 3, .down (-1) 3, .up (-1) 4, .down (-1) 4, .up (0) 4], 2137778781428390588108556872967),
  ([.down (-1) 2, .up (-1) 3, .down (-1) 3, .up (0) 3, .down (0) 2, .up (0) 2], 1447323719028904400621484911967),
  ([.down (-1) 2, .up (-1) 3, .down (-1) 3, .up (0) 3, .down (0) 3, .up (0) 4], 1267436670724753038704693872967),
  ([.down (-1) 2, .up (0) 2, .down (0) 1, .up (0) 1, .down (0) 0, .up (0) 0], 1302548718063398488692484911967),
  ([.down (-1) 2, .up (0) 2, .down (0) 2, .up (0) 3, .down (0) 3, .up (0) 4], 1453413701329910936633693872967),
  ([.down (-1) 3, .up (-1) 3, .down (-1) 2, .up (-1) 2, .down (-1) 1, .up (0) 1], 2060908709563554327654419872967)
]

def table22 : List (List Vertex × ℕ) := [
  ([.down (-1) 3, .up (-1) 3, .down (-1) 2, .up (0) 2, .down (0) 1, .up (0) 1], 2060908709563554327654419872967),
  ([.down (-1) 3, .up (-1) 3, .down (-1) 2, .up (0) 2, .down (0) 2, .up (0) 3], 1367742523553556386621484911967),
  ([.down (-1) 3, .up (-1) 4, .down (-1) 4, .up (0) 4, .down (0) 3, .up (0) 3], 1682886087874028400621484911967),
  ([.down (-1) 3, .up (0) 3, .down (0) 2, .up (0) 2, .down (0) 1, .up (0) 1], 2239191740168712225583419872967),
  ([.down (-1) 4, .up (-1) 4, .down (-1) 3, .up (-1) 3, .down (-1) 2, .up (0) 2], 2588936192556342137512419872967),
  ([.down (-1) 4, .up (-1) 4, .down (-1) 3, .up (0) 3, .down (0) 2, .up (0) 2], 2588936192556342137512419872967),
  ([.down (-1) 4, .up (-1) 4, .down (-1) 3, .up (0) 3, .down (0) 3, .up (0) 4], 896360270112671851217621911967),
  ([.down (-1) 4, .up (0) 4, .down (0) 3, .up (0) 3, .down (0) 2, .up (0) 2], 2717889842315500035441419872967),
  ([.down (0) 0, .up (0) 0, .down (-1) 0, .up (-1) 1, .down (-1) 1, .up (0) 1], 1598291539451466400621484911967),
  ([.down (0) 0, .up (0) 1, .down (-1) 1, .up (-1) 1, .down (-1) 0, .up (0) 0], 250150893792477758801549950967),
  ([.down (0) 0, .up (0) 1, .down (-1) 1, .up (-1) 2, .down (-1) 2, .up (0) 2], 2288558238605177500037556872967),
  ([.down (0) 0, .up (0) 1, .down (0) 1, .up (0) 2, .down (0) 2, .up (0) 3], 2400178208211680007441419872967)
]

def table23 : List (List Vertex × ℕ) := [
  ([.down (0) 0, .up (1) 0, .down (1) 0, .up (1) 1, .down (0) 1, .up (0) 1], 1598291539451466400621484911967),
  ([.down (0) 0, .up (1) 0, .down (1) 0, .up (1) 1, .down (0) 1, .up (0) 2], 2893261903468624035441419872967),
  ([.down (0) 1, .up (0) 1, .down (-1) 1, .up (-1) 1, .down (-1) 0, .up (0) 0], 720378111930513953288621911967),
  ([.down (0) 1, .up (0) 1, .down (-1) 1, .up (-1) 2, .down (-1) 2, .up (0) 2], 1602178962182028400621484911967),
  ([.down (0) 1, .up (0) 2, .down (-1) 2, .up (-1) 2, .down (-1) 1, .up (0) 1], 980207039612678590763484911967),
  ([.down (0) 1, .up (0) 2, .down (-1) 2, .up (-1) 3, .down (-1) 3, .up (0) 3], 2168055984399267486037556872967),
  ([.down (0) 1, .up (0) 2, .down (0) 2, .up (0) 3, .down (0) 3, .up (0) 4], 1453413701329910936633693872967),
  ([.down (0) 1, .up (1) 1, .down (1) 0, .up (1) 0, .down (0) 0, .up (0) 0], 1389704663166353495692484911967),
  ([.down (0) 1, .up (1) 1, .down (1) 0, .up (1) 0, .down (0) 0, .up (0) 1], 1608396948451466400621484911967),
  ([.down (0) 1, .up (1) 1, .down (1) 1, .up (1) 2, .down (0) 2, .up (0) 2], 1602178962182028400621484911967),
  ([.down (0) 1, .up (1) 1, .down (1) 1, .up (1) 2, .down (0) 2, .up (0) 3], 2400178208211680007441419872967),
  ([.down (0) 2, .up (0) 2, .down (-1) 2, .up (-1) 2, .down (-1) 1, .up (0) 1], 1666586316035827690179556872967)
]

def table24 : List (List Vertex × ℕ) := [
  ([.down (0) 2, .up (0) 2, .down (-1) 2, .up (-1) 3, .down (-1) 3, .up (0) 3], 1367742523553556386621484911967),
  ([.down (0) 2, .up (0) 2, .down (0) 1, .up (0) 1, .down (0) 0, .up (0) 0], 1302548718063398488692484911967),
  ([.down (0) 2, .up (0) 3, .down (-1) 3, .up (-1) 3, .down (-1) 2, .up (0) 2], 1447323719028904400621484911967),
  ([.down (0) 2, .up (0) 3, .down (-1) 3, .up (-1) 4, .down (-1) 4, .up (0) 4], 1732068387900663950633693872967),
  ([.down (0) 2, .up (1) 2, .down (1) 1, .up (1) 1, .down (0) 1, .up (0) 1], 2241191740168712225583419872967),
  ([.down (0) 2, .up (1) 2, .down (1) 1, .up (1) 1, .down (0) 1, .up (0) 2], 1604178962182028400621484911967),
  ([.down (0) 2, .up (1) 2, .down (1) 2, .up (1) 3, .down (0) 3, .up (0) 3], 1367742523553556386621484911967),
  ([.down (0) 2, .up (1) 2, .down (1) 2, .up (1) 3, .down (0) 3, .up (0) 4], 1453413701329910936633693872967),
  ([.down (0) 3, .up (0) 3, .down (-1) 3, .up (-1) 3, .down (-1) 2, .up (0) 2], 2247637179874615500037556872967),
  ([.down (0) 3, .up (0) 3, .down (-1) 3, .up (-1) 4, .down (-1) 4, .up (0) 4], 936509671900952851217621911967),
  ([.down (0) 3, .up (0) 3, .down (0) 2, .up (0) 2, .down (0) 1, .up (0) 1], 2239191740168712225583419872967),
  ([.down (0) 3, .up (0) 4, .down (-1) 4, .up (-1) 4, .down (-1) 3, .up (0) 3], 1682886087874028400621484911967)
]

def table25 : List (List Vertex × ℕ) := [
  ([.down (0) 3, .up (1) 3, .down (1) 2, .up (1) 2, .down (0) 2, .up (0) 2], 2710195842315500035441419872967),
  ([.down (0) 3, .up (1) 3, .down (1) 2, .up (1) 2, .down (0) 2, .up (0) 3], 1367742523553556386621484911967),
  ([.down (0) 3, .up (1) 3, .down (1) 3, .up (1) 4, .down (0) 4, .up (0) 4], 936509671900952851217621911967),
  ([.down (0) 4, .up (0) 4, .down (-1) 4, .up (-1) 4, .down (-1) 3, .up (0) 3], 2474597803873739500037556872967),
  ([.down (0) 4, .up (0) 4, .down (0) 3, .up (0) 3, .down (0) 2, .up (0) 2], 2717889842315500035441419872967),
  ([.down (0) 4, .up (1) 4, .down (1) 3, .up (1) 3, .down (0) 3, .up (0) 3], 2719015772532152021441419872967),
  ([.down (0) 4, .up (1) 4, .down (1) 3, .up (1) 3, .down (0) 3, .up (0) 4], 896360270112671851217621911967),
  ([.down (1) 0, .up (1) 0, .down (0) 0, .up (0) 1, .down (0) 1, .up (0) 2], 2893261903468624035441419872967),
  ([.down (1) 0, .up (1) 1, .down (0) 1, .up (0) 1, .down (0) 0, .up (0) 0], 1302548718063398488692484911967),
  ([.down (1) 0, .up (1) 1, .down (0) 1, .up (0) 2, .down (0) 2, .up (0) 3], 2400178208211680007441419872967),
  ([.down (1) 0, .up (1) 1, .down (1) 1, .up (1) 2, .down (0) 2, .up (0) 2], 2288558238605177500037556872967),
  ([.down (1) 0, .up (1) 1, .down (1) 1, .up (1) 2, .down (0) 2, .up (0) 3], 2400178208211680007441419872967)
]

def table26 : List (List Vertex × ℕ) := [
  ([.down (1) 1, .up (1) 1, .down (0) 1, .up (0) 1, .down (0) 0, .up (0) 0], 1302548718063398488692484911967),
  ([.down (1) 1, .up (1) 1, .down (0) 1, .up (0) 2, .down (0) 2, .up (0) 3], 2400178208211680007441419872967),
  ([.down (1) 1, .up (1) 1, .down (1) 0, .up (1) 0, .down (0) 0, .up (0) 0], 1389704663166353495692484911967),
  ([.down (1) 1, .up (1) 1, .down (1) 0, .up (1) 0, .down (0) 0, .up (0) 1], 2443744045297177500037556872967),
  ([.down (1) 1, .up (1) 2, .down (0) 2, .up (0) 2, .down (0) 1, .up (0) 1], 2239191740168712225583419872967),
  ([.down (1) 1, .up (1) 2, .down (0) 2, .up (0) 3, .down (0) 3, .up (0) 4], 1453413701329910936633693872967),
  ([.down (1) 1, .up (1) 2, .down (1) 2, .up (1) 3, .down (0) 3, .up (0) 3], 2168055984399267486037556872967),
  ([.down (1) 1, .up (1) 2, .down (1) 2, .up (1) 3, .down (0) 3, .up (0) 4], 1453413701329910936633693872967),
  ([.down (1) 2, .up (1) 2, .down (0) 2, .up (0) 2, .down (0) 1, .up (0) 1], 2239191740168712225583419872967),
  ([.down (1) 2, .up (1) 2, .down (0) 2, .up (0) 3, .down (0) 3, .up (0) 4], 1453413701329910936633693872967),
  ([.down (1) 2, .up (1) 2, .down (1) 1, .up (1) 1, .down (0) 1, .up (0) 1], 2241191740168712225583419872967),
  ([.down (1) 2, .up (1) 2, .down (1) 1, .up (1) 1, .down (0) 1, .up (0) 2], 2331479297335739500037556872967)
]

def table27 : List (List Vertex × ℕ) := [
  ([.down (1) 2, .up (1) 3, .down (0) 3, .up (0) 3, .down (0) 2, .up (0) 2], 2717889842315500035441419872967),
  ([.down (1) 2, .up (1) 3, .down (1) 3, .up (1) 4, .down (0) 4, .up (0) 4], 1732068387900663950633693872967),
  ([.down (1) 3, .up (1) 3, .down (0) 3, .up (0) 3, .down (0) 2, .up (0) 2], 2717889842315500035441419872967),
  ([.down (1) 3, .up (1) 3, .down (1) 2, .up (1) 2, .down (0) 2, .up (0) 2], 2710195842315500035441419872967),
  ([.down (1) 3, .up (1) 3, .down (1) 2, .up (1) 2, .down (0) 2, .up (0) 3], 1869208164924795472037556872967),
  ([.down (1) 3, .up (1) 4, .down (0) 4, .up (0) 4, .down (0) 3, .up (0) 3], 2742680462955152021441419872967),
  ([.down (1) 4, .up (1) 4, .down (0) 4, .up (0) 4, .down (0) 3, .up (0) 3], 2742680462955152021441419872967),
  ([.down (1) 4, .up (1) 4, .down (1) 3, .up (1) 3, .down (0) 3, .up (0) 3], 2719015772532152021441419872967),
  ([.down (1) 4, .up (1) 4, .down (1) 3, .up (1) 3, .down (0) 3, .up (0) 4], 1031796595934262408229830872967),
  ([.down (2) 0, .up (2) 0, .down (1) 0, .up (1) 0, .down (0) 0, .up (0) 0], 1389704663166353495692484911967),
  ([.down (2) 0, .up (2) 0, .down (1) 0, .up (1) 0, .down (0) 0, .up (0) 1], 2831243620824904137512419872967),
  ([.down (2) 0, .up (2) 0, .down (1) 0, .up (1) 1, .down (0) 1, .up (0) 1], 2124440210774835327654419872967)
]

def table28 : List (List Vertex × ℕ) := [
  ([.down (2) 0, .up (2) 0, .down (1) 0, .up (1) 1, .down (0) 1, .up (0) 2], 2893261903468624035441419872967),
  ([.down (2) 0, .up (2) 1, .down (1) 1, .up (1) 1, .down (0) 1, .up (0) 1], 2241191740168712225583419872967),
  ([.down (2) 0, .up (2) 1, .down (1) 1, .up (1) 1, .down (0) 1, .up (0) 2], 2725801690863466137512419872967),
  ([.down (2) 0, .up (2) 1, .down (1) 1, .up (1) 2, .down (0) 2, .up (0) 2], 2542735629710342137512419872967),
  ([.down (2) 0, .up (2) 1, .down (1) 1, .up (1) 2, .down (0) 2, .up (0) 3], 2400178208211680007441419872967),
  ([.down (2) 1, .up (2) 1, .down (1) 1, .up (1) 1, .down (0) 1, .up (0) 1], 2241191740168712225583419872967),
  ([.down (2) 1, .up (2) 1, .down (1) 1, .up (1) 1, .down (0) 1, .up (0) 2], 2725801690863466137512419872967),
  ([.down (2) 1, .up (2) 1, .down (1) 1, .up (1) 2, .down (0) 2, .up (0) 2], 2542735629710342137512419872967),
  ([.down (2) 1, .up (2) 1, .down (1) 1, .up (1) 2, .down (0) 2, .up (0) 3], 2400178208211680007441419872967),
  ([.down (2) 1, .up (2) 2, .down (1) 2, .up (1) 2, .down (0) 2, .up (0) 2], 2710195842315500035441419872967),
  ([.down (2) 1, .up (2) 2, .down (1) 2, .up (1) 2, .down (0) 2, .up (0) 3], 2210507177606522109512419872967),
  ([.down (2) 1, .up (2) 2, .down (1) 2, .up (1) 3, .down (0) 3, .up (0) 3], 2529344741926994123512419872967)
]

def table29 : List (List Vertex × ℕ) := [
  ([.down (2) 1, .up (2) 2, .down (1) 2, .up (1) 3, .down (0) 3, .up (0) 4], 1453413701329910936633693872967),
  ([.down (2) 2, .up (2) 2, .down (1) 2, .up (1) 2, .down (0) 2, .up (0) 2], 2710195842315500035441419872967),
  ([.down (2) 2, .up (2) 2, .down (1) 2, .up (1) 2, .down (0) 2, .up (0) 3], 2210507177606522109512419872967),
  ([.down (2) 2, .up (2) 2, .down (1) 2, .up (1) 3, .down (0) 3, .up (0) 3], 2529344741926994123512419872967),
  ([.down (2) 2, .up (2) 2, .down (1) 2, .up (1) 3, .down (0) 3, .up (0) 4], 1453413701329910936633693872967),
  ([.down (2) 2, .up (2) 3, .down (1) 3, .up (1) 3, .down (0) 3, .up (0) 3], 2719015772532152021441419872967),
  ([.down (2) 2, .up (2) 3, .down (1) 3, .up (1) 3, .down (0) 3, .up (0) 4], 1267436670724753038704693872967),
  ([.down (2) 2, .up (2) 3, .down (1) 3, .up (1) 4, .down (0) 4, .up (0) 4], 2137778781428390588108556872967),
  ([.down (2) 3, .up (2) 3, .down (1) 3, .up (1) 3, .down (0) 3, .up (0) 3], 2719015772532152021441419872967),
  ([.down (2) 3, .up (2) 3, .down (1) 3, .up (1) 3, .down (0) 3, .up (0) 4], 1267436670724753038704693872967),
  ([.down (2) 3, .up (2) 3, .down (1) 3, .up (1) 4, .down (0) 4, .up (0) 4], 2137778781428390588108556872967),
  ([.down (2) 3, .up (2) 4, .down (1) 4, .up (1) 4, .down (0) 4, .up (0) 4], 2323755812033548486037556872967)
]

def table30 : List (List Vertex × ℕ) := [
  ([.down (2) 4, .up (2) 4, .down (1) 4, .up (1) 4, .down (0) 4, .up (0) 4], 2323755812033548486037556872967)
]

def table : List (List Vertex × ℕ) :=
  table0 ++ table1 ++ table2 ++ table3 ++ table4 ++ table5 ++ table6 ++ table7 ++ table8 ++ table9 ++ table10 ++ table11 ++ table12 ++ table13 ++ table14 ++ table15 ++ table16 ++ table17 ++ table18 ++ table19 ++ table20 ++ table21 ++ table22 ++ table23 ++ table24 ++ table25 ++ table26 ++ table27 ++ table28 ++ table29 ++ table30

def potential (w : List Vertex) : ℕ := (table.lookup w).getD 0

def states : List (List Vertex) := table.map Prod.fst

def rowOK (w : List Vertex) : Prop :=
  w ≠ [] ∧ 0 < potential w ∧
    (∀ c ∈ candidates w, normalize (slide w c) ∈ states) ∧
    1000 * (∑ c ∈ candidates w, potential (normalize (slide w c))) ≤ 1847 * potential w

instance (w : List Vertex) : Decidable (rowOK w) := by
  unfold rowOK
  infer_instance



lemma checked0 : ∀ w ∈ table0.map Prod.fst, rowOK w := by decide
lemma checked1 : ∀ w ∈ table1.map Prod.fst, rowOK w := by decide
lemma checked2 : ∀ w ∈ table2.map Prod.fst, rowOK w := by decide
lemma checked3 : ∀ w ∈ table3.map Prod.fst, rowOK w := by decide
lemma checked4 : ∀ w ∈ table4.map Prod.fst, rowOK w := by decide
lemma checked5 : ∀ w ∈ table5.map Prod.fst, rowOK w := by decide
lemma checked6 : ∀ w ∈ table6.map Prod.fst, rowOK w := by decide
lemma checked7 : ∀ w ∈ table7.map Prod.fst, rowOK w := by decide
lemma checked8 : ∀ w ∈ table8.map Prod.fst, rowOK w := by decide
lemma checked9 : ∀ w ∈ table9.map Prod.fst, rowOK w := by decide
lemma checked10 : ∀ w ∈ table10.map Prod.fst, rowOK w := by decide
lemma checked11 : ∀ w ∈ table11.map Prod.fst, rowOK w := by decide
lemma checked12 : ∀ w ∈ table12.map Prod.fst, rowOK w := by decide
lemma checked13 : ∀ w ∈ table13.map Prod.fst, rowOK w := by decide
lemma checked14 : ∀ w ∈ table14.map Prod.fst, rowOK w := by decide
lemma checked15 : ∀ w ∈ table15.map Prod.fst, rowOK w := by decide
lemma checked16 : ∀ w ∈ table16.map Prod.fst, rowOK w := by decide
lemma checked17 : ∀ w ∈ table17.map Prod.fst, rowOK w := by decide
lemma checked18 : ∀ w ∈ table18.map Prod.fst, rowOK w := by decide
lemma checked19 : ∀ w ∈ table19.map Prod.fst, rowOK w := by decide
lemma checked20 : ∀ w ∈ table20.map Prod.fst, rowOK w := by decide
lemma checked21 : ∀ w ∈ table21.map Prod.fst, rowOK w := by decide
lemma checked22 : ∀ w ∈ table22.map Prod.fst, rowOK w := by decide
lemma checked23 : ∀ w ∈ table23.map Prod.fst, rowOK w := by decide
lemma checked24 : ∀ w ∈ table24.map Prod.fst, rowOK w := by decide
lemma checked25 : ∀ w ∈ table25.map Prod.fst, rowOK w := by decide
lemma checked26 : ∀ w ∈ table26.map Prod.fst, rowOK w := by decide
lemma checked27 : ∀ w ∈ table27.map Prod.fst, rowOK w := by decide
lemma checked28 : ∀ w ∈ table28.map Prod.fst, rowOK w := by decide
lemma checked29 : ∀ w ∈ table29.map Prod.fst, rowOK w := by decide
lemma checked30 : ∀ w ∈ table30.map Prod.fst, rowOK w := by decide

lemma table_checked : ∀ w ∈ states, rowOK w := by
  simp only [states, table, List.map_append, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨checked0, checked1⟩, checked2⟩, checked3⟩, checked4⟩, checked5⟩, checked6⟩, checked7⟩, checked8⟩, checked9⟩, checked10⟩, checked11⟩, checked12⟩, checked13⟩, checked14⟩, checked15⟩, checked16⟩, checked17⟩, checked18⟩, checked19⟩, checked20⟩, checked21⟩, checked22⟩, checked23⟩, checked24⟩, checked25⟩, checked26⟩, checked27⟩, checked28⟩, checked29⟩, checked30⟩

lemma source_checked : normalize [Vertex.up 0 0] ∈ states := by decide

noncomputable def beta : ℝ := 1847 / 1000

lemma count_weighted (n : ℕ) (w : List Vertex) (hw : normalize w ∈ states) :
    (count w n : ℝ) ≤ (potential (normalize w) : ℝ) * beta ^ n := by
  induction n generalizing w with
  | zero =>
    have hp := (table_checked (normalize w) hw).2.1
    have hone : (1 : ℝ) ≤ (potential (normalize w) : ℝ) := by exact_mod_cast hp
    simpa only [count, Nat.cast_one, pow_zero, mul_one] using hone
  | succ n ih =>
    have cert := table_checked (normalize w) hw
    have hne : w ≠ [] := by
      intro he
      exact cert.1 (by simp [he, normalize])
    have heq : count (normalize w) (n+1) = count w (n+1) :=
      count_shift (-origin w) (n+1) w hne
    have hstep : (∑ c ∈ candidates (normalize w),
        (potential (normalize (slide (normalize w) c)) : ℝ)) ≤
          beta * (potential (normalize w) : ℝ) := by
      have hnat := cert.2.2.2
      have hreal : (1000 : ℝ) * (∑ c ∈ candidates (normalize w),
          (potential (normalize (slide (normalize w) c)) : ℝ)) ≤
            1847 * (potential (normalize w) : ℝ) := by
        exact_mod_cast hnat
      dsimp [beta]
      linarith
    calc (count w (n+1) : ℝ)
        = ∑ c ∈ candidates (normalize w), (count (slide (normalize w) c) n : ℝ) := by
          rw [← heq, count, Nat.cast_sum]
      _ ≤ ∑ c ∈ candidates (normalize w),
          (potential (normalize (slide (normalize w) c)) : ℝ) * beta ^ n := by
          apply Finset.sum_le_sum
          intro c hc
          exact ih _ (cert.2.2.1 c hc)
      _ = (∑ c ∈ candidates (normalize w),
          (potential (normalize (slide (normalize w) c)) : ℝ)) * beta ^ n := by
          rw [Finset.sum_mul]
      _ ≤ (beta * (potential (normalize w) : ℝ)) * beta ^ n :=
          mul_le_mul_of_nonneg_right hstep (pow_nonneg (by norm_num [beta]) n)
      _ = (potential (normalize w) : ℝ) * beta ^ (n+1) := by ring

def continuations (w : List Vertex) : ℕ → Finset (List Vertex)
  | 0 => {[]}
  | n+1 => (candidates w).biUnion fun c =>
      (continuations (slide w c) n).image fun l => c :: l

lemma continuations_card (n : ℕ) (w : List Vertex) :
    (continuations w n).card ≤ count w n := by
  induction n generalizing w with
  | zero => simp [continuations, count]
  | succ n ih =>
    calc (continuations w (n+1)).card
        ≤ ∑ c ∈ candidates w,
            ((continuations (slide w c) n).image fun l => c :: l).card := Finset.card_biUnion_le
      _ ≤ ∑ c ∈ candidates w, count (slide w c) n := by
          apply Finset.sum_le_sum
          intro c _
          exact Finset.card_image_le.trans (ih (slide w c))
      _ = count w (n+1) := rfl

lemma slide_append_eq (w : List Vertex) (c : Vertex) (l : List Vertex) (hne : w ≠ []) :
    slide w c ++ l = if w.length < 6 then w ++ c :: l else (w ++ c :: l).tail := by
  unfold slide
  split_ifs <;> simp [List.append_assoc, List.tail_append_of_ne_nil hne]

lemma mem_continuations {w l : List Vertex} (hne : w ≠ [])
    (hc : (w ++ l).IsChain adjacent) (hnd : (w ++ l).Nodup)
    (hin : ∀ v ∈ w ++ l, inside v) : l ∈ continuations w l.length := by
  induction l generalizing w with
  | nil => simp [continuations]
  | cons c l ih =>
    have hcin : inside c := hin c (by simp)
    have hcn : c ∉ w := by
      intro hcw
      exact ((List.nodup_append.mp hnd).2.2 c hcw c (by simp)) rfl
    have hrel : adjacent (last w) c := by
      have h := hc.rel_getLast_head_of_append hne (by simp)
      simpa only [last_eq_getLast hne, List.head_cons] using h
    have hnextc : (slide w c ++ l).IsChain adjacent := by
      rw [slide_append_eq w c l hne]
      split_ifs
      · exact hc
      · exact hc.tail
    have hnextnd : (slide w c ++ l).Nodup := by
      rw [slide_append_eq w c l hne]
      split_ifs
      · exact hnd
      · exact hnd.tail
    have hnextin : ∀ v ∈ slide w c ++ l, inside v := by
      intro v hv
      rw [slide_append_eq w c l hne] at hv
      split_ifs at hv
      · exact hin v hv
      · exact hin v (List.mem_of_mem_tail hv)
    apply Finset.mem_biUnion.mpr
    refine ⟨c, Finset.mem_filter.mpr ⟨mem_neighbors.mpr ⟨hrel,hcin⟩,hcn⟩, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨l, ih (slide_ne_nil w c) hnextc hnextnd hnextin, rfl⟩

def allPaths (n : ℕ) : Finset (List Vertex) :=
  (continuations [Vertex.up 0 0] (n-1)).image fun l => Vertex.up 0 0 :: l

lemma path_mem_allPaths (p : BridgePath 5) : p.vertices ∈ allPaths p.vertices.length := by
  have hsrc := p.source
  cases hv : p.vertices with
  | nil => simp [hv] at hsrc
  | cons a l =>
    have ha : a = .up 0 0 := by simpa [hv] using hsrc
    subst a
    have hc : ([Vertex.up 0 0] ++ l).IsChain adjacent := by
      simpa only [hv, List.singleton_append] using p.connected
    have hnd : ([Vertex.up 0 0] ++ l).Nodup := by
      simpa only [hv, List.singleton_append] using p.distinct
    have hin : ∀ v ∈ [Vertex.up 0 0] ++ l, inside v := by
      intro v h
      have hvp : v ∈ p.vertices := by simpa only [hv, List.singleton_append] using h
      exact (inside_iff v).mpr (p.inStrip v hvp)
    rw [allPaths]
    apply Finset.mem_image.mpr
    refine ⟨l, ?_, by simpa only [hv]⟩
    simpa only [hv, List.length_cons, Nat.add_sub_cancel] using
      mem_continuations (by simp : [Vertex.up 0 0] ≠ []) hc hnd hin

lemma path_card_real (n : ℕ) (s : Finset (BridgePath 5))
    (hlen : ∀ p ∈ s, p.vertices.length = n) :
    (s.card : ℝ) ≤ (potential (normalize [Vertex.up 0 0]) : ℝ) * beta ^ n := by
  classical
  have hm : Set.MapsTo (fun p : BridgePath 5 => p.vertices) (s : Set (BridgePath 5))
      (allPaths n : Set (List Vertex)) := by
    intro p hp
    change p.vertices ∈ allPaths n
    simpa only [hlen p hp] using path_mem_allPaths p
  have hi : Set.InjOn (fun p : BridgePath 5 => p.vertices) (s : Set (BridgePath 5)) := by
    intro p hp q hq he
    cases p
    cases q
    cases he
    rfl
  have hcard : (s.card : ℝ) ≤ ((allPaths n).card : ℝ) := by
    exact_mod_cast Finset.card_le_card_of_injOn _ hm hi
  have hcont : (allPaths n).card ≤ count [Vertex.up 0 0] (n-1) :=
    Finset.card_image_le.trans (continuations_card (n-1) [Vertex.up 0 0])
  calc (s.card : ℝ) ≤ ((allPaths n).card : ℝ) := hcard
    _ ≤ (count [Vertex.up 0 0] (n-1) : ℝ) := by exact_mod_cast hcont
    _ ≤ (potential (normalize [Vertex.up 0 0]) : ℝ) * beta ^ (n-1) :=
        count_weighted (n-1) _ source_checked
    _ ≤ (potential (normalize [Vertex.up 0 0]) : ℝ) * beta ^ n := by
        apply mul_le_mul_of_nonneg_left
        · exact pow_le_pow_right₀ (by norm_num [beta]) (by omega)
        · exact Nat.cast_nonneg _

lemma beta_lt_mu : beta < 2 * Real.cos (Real.pi / 8) := by
  have hsq2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have h2 : (1414/1000 : ℝ) < Real.sqrt 2 := by
    by_contra h
    have hle : Real.sqrt 2 ≤ (1414/1000 : ℝ) := le_of_not_gt h
    have hsqle := mul_le_mul hle hle (Real.sqrt_nonneg 2)
      (by norm_num : (0 : ℝ) ≤ 1414/1000)
    nlinarith
  have hroot : Real.sqrt (beta^2) < Real.sqrt (2 + Real.sqrt 2) :=
    Real.sqrt_lt_sqrt (sq_nonneg _) (by norm_num [beta] at *; linarith)
  rw [Real.sqrt_sq (by norm_num [beta])] at hroot
  rw [Real.cos_pi_div_eight]
  nlinarith

theorem stripGrowthAtFive :
    ∃ C β : ℝ, 0 ≤ C ∧ 0 ≤ β ∧ β < 2 * Real.cos (Real.pi / 8) ∧
      ∀ (n : ℕ) (s : Finset (BridgePath 5)),
        (∀ p ∈ s, p.vertices.length = n) → (s.card : ℝ) ≤ C * β ^ n := by
  exact ⟨(potential (normalize [Vertex.up 0 0]) : ℝ), beta,
    Nat.cast_nonneg _, by norm_num [beta], beta_lt_mu, path_card_real⟩

end WidthFive
/-- Unconditional height-five summability, using a checked six-vertex memory. -/
theorem width_five_summability_diagnostic :
    Summable (weight (h := 5)) ∧ Summable (firstLengthWeight (h := 5)) := by
  obtain ⟨C, β, hC, hβ, hlt, hcount⟩ := WidthFive.stripGrowthAtFive
  have hL : Summable (firstLengthWeight (h := 5)) :=
    bridgeSummable_firstLengthWeight_of_mu_bound hC hβ hlt hcount
  exact ⟨bridgeSummable_weight_of_summable_firstLengthWeight hL, hL⟩

#check @WidthFive.table_checked
#print axioms WidthFive.table_checked
#check @WidthFive.count_weighted
#print axioms WidthFive.count_weighted
#check @WidthFive.path_mem_allPaths
#print axioms WidthFive.path_mem_allPaths
#check @WidthFive.path_card_real
#print axioms WidthFive.path_card_real
#check @WidthFive.stripGrowthAtFive
#print axioms WidthFive.stripGrowthAtFive
#check @width_five_summability_diagnostic
#print axioms width_five_summability_diagnostic

end PolynomialVacuumBridge.Corridor
end OAI
