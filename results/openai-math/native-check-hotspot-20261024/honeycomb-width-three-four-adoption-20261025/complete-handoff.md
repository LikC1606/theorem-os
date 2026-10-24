# Height 3

Prove and deliver the exact unconditional fixed-height-three pair of summabilities as a typed auxiliary lemma. A complete insertion-ready proof increment is included below and has passed an independent local Lean 4.34.1 kernel check; normal host typed verification and canonical integration are still required. The proof enumerates the six width-three vertex kinds, proves the translation invariance of non-backtracking continuation counts, and kernel-checks the at-most-20 count for five steps after each possible incoming edge using ordinary decide. A block induction bounds all continuation counts by 16*20^(n/5); a finite vertex-list enumerator contains every canonical BridgePath 3 and yields the cardinality bound 32*20^(n/5) <= 32*(11/6)^n. Pure rational arithmetic proves 20 <= (11/6)^5, and the exact cosine/square-root identity proves 11/6 < 2*cos(pi/8). Use the already integrated unconditional counting-to-summability helpers from sums_reduction. The task has no strip_growth_below_mu antecedent and does not invoke the original finite_bridge_sums proof. Insert the following complete WidthThree.lean.inc increment once inside namespace OAI.PolynomialVacuumBridge.Corridor in generated/problem/Submission.lean, after bridgeSummable_firstLengthWeight_of_mu_bound and bridgeSummable_weight_of_summable_firstLengthWeight. The increment opens and closes nested namespace WidthThree and then proves width_three_summability_diagnostic in the outer namespace. Check for declaration-name collisions and reuse exact compatible helpers if a previous delivery has inserted them. Preserve all existing declarations, all current tasks, the original theorem and its unresolved higher-width frontier. Do not replace Submission.lean with the standalone WidthThree.lean validation harness. The finite enumeration is proved directly from frozen definitions; it imports no Python count or external certificate as an axiom. Ordinary decide reduces a finite proposition in the kernel. The source has no placeholder, native_decide, additional axiom or weakened conclusion. Height three alone is proved; this auxiliary task does not resolve all heights.

Local evidence: source SHA256 e0dd3d9678d060cd719c52092bed9a15244b6fdd357956779a9fa38a6f0fdf63, increment SHA256 375739ea3473e164e586091370a0bac3c03aab5a52a17e6a3cc46a3b7460cfc7, Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, sealed environment 2d808da67c8ab8ad74458d8a53ecc2ee8da9c63a825e0429439ebf56a9a78c87, actual exit 0 in 10.050331623060629 seconds, one thread/core, 32 GiB, maxHeartbeats=0, no wall/CPU/invocation cap. All six printed key declarations, including the exact target, depend only on [propext, Classical.choice, Quot.sound]. This package does not itself grant native host task acceptance or OpenAI-hosted certification.

```lean
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
```


# Height 4

Prove the exact unconditional height-four weight and first-length-weight summability lemma and deliver it via the ordinary typed proof protocol. The complete increment below has passed local Lean 4.34.1 kernel checking. Native host verification and canonical integration remain required. Preserve the original all-height target and every existing declaration; do not infer an all-width result.

The proof uses the canonical geometry at h=4. It enumerates the eight vertex kinds and all 22 incoming-edge cases, and proves a one-step potential inequality with beta=1847/1000 and positive integer weights between 29 and 64. It then inductively bounds continuation counts by edgeWeight*beta^n, covers every canonical BridgePath 4 by the enumerator using the actual connectedness, Nodup, source, terminal and strip fields, and derives the finite-family count bound card <=128*beta^n. It proves beta<2*cos(pi/8) by exact rational/root inequalities, then uses the already integrated unconditional counting-to-summability helpers. No growth hypothesis, unresolved original theorem, additional axiom, native_decide or publisher solution is used. There is no 14-step enumeration.

Insert the entire WidthFour.lean.inc once inside namespace OAI.PolynomialVacuumBridge.Corridor after the existing bridgeSummable_firstLengthWeight_of_mu_bound and bridgeSummable_weight_of_summable_firstLengthWeight helpers from sums_reduction. The increment opens/closes WidthFour and declares width_four_summability_diagnostic in the outer namespace. Reuse identical names if a prior delivery has already integrated them. The standalone WidthFour.lean validation harness must not replace Submission.lean. The exact theorem/type/proofPath in the task must be delivered; an advisory report is not a formal proof delivery.

Local evidence: actual Lean exit 0 in 11.999551268992946 seconds. Source SHA256 a8462a1922c107fde21cde91cb10c505f57860c5d926b3bb30df2869cd804e91, increment SHA256 db6e35bfe5eba4bfae490a63997874ce18953292e266c8351410097cbdae41b0. Fixed Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, one CPU/thread, 32 GiB, maxHeartbeats=0 and no wall/CPU/call cap. All 12 printed key declarations including the exact target use only propext, Classical.choice and Quot.sound. A single unnecessarySimpa style warning remains; no proof error or stderr. No unchanged-source rerun was performed during archival. This evidence is local; native task acceptance and OpenAI-hosted certification are not claimed.

Complete independently checked Lean increment:
```lean
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
```
