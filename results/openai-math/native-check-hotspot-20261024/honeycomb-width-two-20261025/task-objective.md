Prove the existing exact fixed-width-two summability diagnostic and deliver it through the ordinary assignment proof protocol. A complete unconditional proof increment is included below and has passed an independent local Lean 4.34.1 kernel check; normal host typed verification and canonical integration are still required. This is the same pending task and same conclusion, not a new or conditional task. Preserve its current theoremName, type, dependencies, and all other tasks; no all-width strip-growth hypothesis is assumed. The proof explicitly enumerates neighbors of the four width-two vertex kinds, proves at most three non-backtracking two-step extensions after any incoming edge, recursively bounds continuation counts by 2*3^(n/2), injects each canonical BridgePath 2 vertex list into the finite enumerator, and derives the count bound 4*3^(n/2) <= 4*(sqrt 3)^n. It proves sqrt 3 < 2*cos(pi/8) and uses the existing canonical unconditional counting-to-summability helpers from integrated sums_reduction. Insert the following entire WidthTwo.lean.inc increment once inside namespace OAI.PolynomialVacuumBridge.Corridor in generated/problem/Submission.lean, after bridgeSummable_firstLengthWeight_of_mu_bound and bridgeSummable_weight_of_summable_firstLengthWeight. The increment itself opens and closes the nested WidthTwo namespace and then proves width_two_summability_diagnostic in the outer namespace. Check for declaration-name collisions and reuse exact compatible existing helpers if a prior delivery has already inserted them. Preserve all existing declarations, including finite_bridge_sums and all-width tasks. Do not replace Submission.lean with the standalone WidthTwo.lean validation harness. The complete proof and finite enumeration use no placeholder, imported solution, extra axiom or native_decide. Widths h>=3 remain outside this fixed-width diagnostic.

Local evidence: source SHA256 97a34151766af41dc81716bb199f5565d87b2e505f5be38f0a289c5b657c7027, increment SHA256 6946d27d61a5056762c4fd4e3b1cbc8e9ea7da84d78fef68aa008fa6ff99e1ef, Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, sealed environment 2d808da67c8ab8ad74458d8a53ecc2ee8da9c63a825e0429439ebf56a9a78c87, actual Lean exit 0 in 21.30641626403667 seconds, one thread/core, 32 GiB, maxHeartbeats=0, no wall/CPU/call cap. All six printed key declarations, including the exact target, depend only on [propext, Classical.choice, Quot.sound]. This evidence does not itself constitute native host task acceptance or OpenAI-hosted certification.

```lean
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
  rcases Finset.mem_image.mp hd with ⟨d,hdmem,rfl⟩
  have hcin : inside c := ((mem_neighbors hb).1 (Finset.mem_erase.mp hc).2).2
  have hdin := (mem_neighbors hcin).1 (Finset.mem_erase.mp hdmem).2
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
    simpa [continuations] using
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

noncomputable def allPaths (n : ℕ) : Finset (List Vertex) :=
  (neighbors (.up 0 0)).biUnion fun b =>
    (continuations (.up 0 0) b (n-2)).image fun l => (.up 0 0) :: b :: l

lemma allPaths_card (n : ℕ) : (allPaths n).card ≤ 4 * 3 ^ (n/2) := by
  classical
  have hs : inside (.up 0 0) := by simp [inside,layer]
  calc (allPaths n).card
      ≤ ∑ b ∈ neighbors (.up 0 0),
          ((continuations (.up 0 0) b (n-2)).image fun l => (.up 0 0) :: b :: l).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ neighbors (.up 0 0), 2 * 3 ^ ((n-2)/2) := by
        apply Finset.sum_le_sum
        intro b hb
        obtain ⟨hadj,hbin⟩ := (mem_neighbors hs).1 hb
        exact Finset.card_image_le.trans (continuations_card (n-2) _ _ hs hbin hadj)
    _ = 4 * 3 ^ ((n-2)/2) := by simp [neighbors]; ring
    _ ≤ 4 * 3 ^ (n/2) := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_right (by omega) (by omega)

lemma path_mem_allPaths (p : BridgePath 2) : p.vertices ∈ allPaths p.vertices.length := by
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

lemma path_card (n : ℕ) (s : Finset (BridgePath 2))
    (hlen : ∀ p ∈ s, p.vertices.length = n) : s.card ≤ 4 * 3 ^ (n/2) := by
  classical
  have hm : Set.MapsTo (fun p : BridgePath 2 => p.vertices) (s : Set (BridgePath 2))
      (allPaths n : Set (List Vertex)) := by
    intro p hp
    change p.vertices ∈ allPaths n
    simpa only [hlen p hp] using path_mem_allPaths p
  have hi : Set.InjOn (fun p : BridgePath 2 => p.vertices) (s : Set (BridgePath 2)) := by
    intro p hp q hq he
    cases p
    cases q
    cases he
    rfl
  exact (Finset.card_le_card_of_injOn _ hm hi).trans (allPaths_card n)

lemma sqrt_three_lt_mu : Real.sqrt 3 < 2 * Real.cos (Real.pi / 8) := by
  have hsq2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have h2 : (1 : ℝ) < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hroot : Real.sqrt 3 < Real.sqrt (2 + Real.sqrt 2) :=
    Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  rw [Real.cos_pi_div_eight]
  nlinarith

lemma path_card_real (n : ℕ) (s : Finset (BridgePath 2))
    (hlen : ∀ p ∈ s, p.vertices.length = n) :
    (s.card : ℝ) ≤ 4 * Real.sqrt 3 ^ n := by
  have hcard : (s.card : ℝ) ≤ 4 * (3 : ℝ) ^ (n/2) := by
    exact_mod_cast path_card n s hlen
  have hge : (1 : ℝ) ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  calc (s.card : ℝ) ≤ 4 * (3 : ℝ) ^ (n/2) := hcard
    _ = 4 * Real.sqrt 3 ^ (2*(n/2)) := by
        rw [pow_mul,Real.sq_sqrt (by norm_num)]
    _ ≤ 4 * Real.sqrt 3 ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hge (by omega)) (by norm_num)

theorem stripGrowthAtTwo :
    ∃ C β : ℝ, 0 ≤ C ∧ 0 ≤ β ∧ β < 2 * Real.cos (Real.pi / 8) ∧
      ∀ (n : ℕ) (s : Finset (BridgePath 2)),
        (∀ p ∈ s, p.vertices.length = n) → (s.card : ℝ) ≤ C * β ^ n := by
  exact ⟨4, Real.sqrt 3, by norm_num, Real.sqrt_nonneg 3,
    sqrt_three_lt_mu, path_card_real⟩

end WidthTwo

/-- Unconditional fixed-width-two diagnostic. This does not prove all widths. -/
theorem width_two_summability_diagnostic :
    Summable (weight (h := 2)) ∧ Summable (firstLengthWeight (h := 2)) := by
  obtain ⟨C, β, hC, hβ, hlt, hcount⟩ := WidthTwo.stripGrowthAtTwo
  have hL : Summable (firstLengthWeight (h := 2)) :=
    bridgeSummable_firstLengthWeight_of_mu_bound hC hβ hlt hcount
  exact ⟨bridgeSummable_weight_of_summable_firstLengthWeight hL,hL⟩
```
