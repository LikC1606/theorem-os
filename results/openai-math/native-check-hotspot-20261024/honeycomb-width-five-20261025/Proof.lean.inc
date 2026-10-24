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
