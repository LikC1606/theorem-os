
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
