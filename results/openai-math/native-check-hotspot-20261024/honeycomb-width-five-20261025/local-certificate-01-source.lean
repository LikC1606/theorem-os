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

def inside (v : Vertex) : Prop := 0 ≤ layer v ∧ layer v < 5

instance (v : Vertex) : Decidable (inside v) := by
  unfold inside
  infer_instance

def neighbors : Vertex → Finset Vertex
  | .up i j => ({.down i (j-1), .down i j, .down (i-1) j} : Finset Vertex).filter inside
  | .down i j => ({.up i (j+1), .up i j, .up (i+1) j} : Finset Vertex).filter inside

lemma mem_neighbors {a b : Vertex} :
    b ∈ neighbors a ↔ adjacent a b ∧ inside b := by
  cases a <;> cases b <;>
    simp [neighbors, adjacent, inside, layer, Vertex.up.injEq, Vertex.down.injEq] <;> omega

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
  ext c
  constructor
  · intro h
    have hc := mem_neighbors.mp h
    cases b <;> cases c <;>
      simp only [shift, adjacent] at hc
    all_goals
      simp only [neighbors, Finset.mem_image, Finset.mem_filter, Finset.mem_insert,
        Finset.mem_singleton, Vertex.up.injEq, Vertex.down.injEq, shift]
      simp only [inside, layer] at hc ⊢
      grind
  · intro h
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp h
    have hc := mem_neighbors.mp hc
    apply mem_neighbors.mpr
    constructor
    · cases b <;> cases c <;> simp only [shift, adjacent] at hc ⊢ <;> omega
    · exact (inside_shift t c).mpr hc.2

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
  cases v <;> simp [Function.comp_def, shift] <;> congr 1 <;> omega

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


def table : List (List Vertex × ℕ) := [
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
  ([.up (2) 0, .down (1) 0, .up (1) 0, .down (0) 0], 2210533559260247014508237979939),
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
  ([.up (2) 0, .down (1) 0, .up (1) 1, .down (0) 1, .up (0) 1], 2030759268254691082659042093089),
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
  ([.up (-2) 2, .down (-2) 2, .up (-1) 2, .down (-1) 2, .up (0) 2, .down (0) 1], 2210507177606522109512419872967),
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
  ([.up (-2) 4, .down (-2) 3, .up (-1) 3, .down (-1) 3, .up (0) 3, .down (0) 2], 2725801690863466137512419872967),
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
  ([.up (-1) 1, .down (-1) 1, .up (0) 1, .down (0) 1, .up (0) 2, .down (0) 2], 2717889842315500035441419872967),
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
  ([.up (-1) 3, .down (-1) 3, .up (-1) 4, .down (-1) 4, .up (0) 4, .down (0) 4], 1389704663166353495692484911967),
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
  ([.up (0) 1, .down (-1) 1, .up (-1) 1, .down (-1) 0, .up (0) 0, .down (0) 0], 936509671900952851217621911967),
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
  ([.up (0) 2, .down (0) 1, .up (1) 1, .down (1) 1, .up (1) 2, .down (0) 2], 1447323719028904400621484911967),
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
  ([.up (0) 3, .down (0) 3, .up (1) 3, .down (1) 3, .up (1) 4, .down (0) 4], 720378111930513953288621911967),
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
  ([.up (1) 1, .down (1) 0, .up (1) 0, .down (0) 0, .up (0) 1, .down (0) 1], 1682886087874028400621484911967),
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
  ([.up (1) 3, .down (0) 3, .up (0) 3, .down (0) 2, .up (0) 2, .down (0) 1], 2400178208211680007441419872967),
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
  ([.up (2) 0, .down (1) 0, .up (1) 1, .down (1) 1, .up (1) 2, .down (0) 2], 2588936192556342137512419872967),
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
  ([.up (2) 1, .down (2) 1, .up (2) 2, .down (1) 2, .up (1) 3, .down (0) 3], 2239191740168712225583419872967),
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
  ([.up (2) 3, .down (1) 3, .up (1) 3, .down (0) 3, .up (0) 4, .down (0) 4], 720378111930513953288621911967),
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
  ([.up (3) 0, .down (2) 0, .up (2) 1, .down (1) 1, .up (1) 1, .down (0) 1], 2719015772532152021441419872967),
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
  ([.up (3) 3, .down (2) 3, .up (2) 4, .down (1) 4, .up (1) 4, .down (0) 4], 1389704663166353495692484911967),
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
  ([.down (-3) 3, .up (-2) 3, .down (-2) 3, .up (-1) 3, .down (-1) 2, .up (0) 2], 2717889842315500035441419872967),
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
  ([.down (-2) 1, .up (-2) 2, .down (-2) 2, .up (-1) 2, .down (-1) 2, .up (0) 2], 2710195842315500035441419872967),
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
  ([.down (-2) 2, .up (-1) 2, .down (-1) 2, .up (-1) 3, .down (-1) 3, .up (0) 3], 2529344741926994123512419872967),
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
  ([.down (-2) 3, .up (-1) 3, .down (-1) 3, .up (0) 3, .down (0) 3, .up (0) 4], 1267436670724753038704693872967),
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
  ([.down (-1) 1, .up (-1) 2, .down (-1) 2, .up (-1) 3, .down (-1) 3, .up (0) 3], 2529344741926994123512419872967),
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
  ([.down (-1) 3, .up (-1) 3, .down (-1) 2, .up (-1) 2, .down (-1) 1, .up (0) 1], 2060908709563554327654419872967),
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
  ([.down (0) 0, .up (0) 1, .down (0) 1, .up (0) 2, .down (0) 2, .up (0) 3], 2400178208211680007441419872967),
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
  ([.down (0) 2, .up (0) 2, .down (-1) 2, .up (-1) 2, .down (-1) 1, .up (0) 1], 1666586316035827690179556872967),
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
  ([.down (0) 3, .up (0) 4, .down (-1) 4, .up (-1) 4, .down (-1) 3, .up (0) 3], 1682886087874028400621484911967),
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
  ([.down (1) 0, .up (1) 1, .down (1) 1, .up (1) 2, .down (0) 2, .up (0) 3], 2400178208211680007441419872967),
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
  ([.down (1) 2, .up (1) 2, .down (1) 1, .up (1) 1, .down (0) 1, .up (0) 2], 2331479297335739500037556872967),
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
  ([.down (2) 0, .up (2) 0, .down (1) 0, .up (1) 1, .down (0) 1, .up (0) 1], 2124440210774835327654419872967),
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
  ([.down (2) 1, .up (2) 2, .down (1) 2, .up (1) 3, .down (0) 3, .up (0) 3], 2529344741926994123512419872967),
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
  ([.down (2) 3, .up (2) 4, .down (1) 4, .up (1) 4, .down (0) 4, .up (0) 4], 2323755812033548486037556872967),
  ([.down (2) 4, .up (2) 4, .down (1) 4, .up (1) 4, .down (0) 4, .up (0) 4], 2323755812033548486037556872967)
]

def potential (w : List Vertex) : ℕ := (table.lookup w).getD 0

def states : List (List Vertex) := table.map Prod.fst

def rowOK (w : List Vertex) : Prop :=
  w ≠ [] ∧ 0 < potential w ∧
    (∀ c ∈ candidates w, normalize (slide w c) ∈ states) ∧
    1000 * (∑ c ∈ candidates w, potential (normalize (slide w c))) ≤ 1847 * potential w

instance (w : List Vertex) : Decidable (rowOK w) := by
  unfold rowOK
  infer_instance

lemma table_checked : ∀ w ∈ states, rowOK w := by decide

lemma source_checked : normalize [Vertex.up 0 0] ∈ states := by decide


end WidthFive

#check @WidthFive.table_checked
#print axioms WidthFive.table_checked

end PolynomialVacuumBridge.Corridor
end OAI
