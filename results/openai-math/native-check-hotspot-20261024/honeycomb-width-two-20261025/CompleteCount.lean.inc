
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
      simpa only [hv,List.length_cons,Nat.add_sub_cancel] using mem_continuations hc hnd hin

lemma path_card (n : ℕ) (s : Finset (BridgePath 2))
    (hlen : ∀ p ∈ s, p.vertices.length = n) : s.card ≤ 4 * 3 ^ (n/2) := by
  classical
  have hm : Set.MapsTo (fun p : BridgePath 2 => p.vertices) (s : Set (BridgePath 2))
      (allPaths n : Set (List Vertex)) := by
    intro p hp
    simpa only [hlen p hp] using path_mem_allPaths p
  have hi : Set.InjOn (fun p : BridgePath 2 => p.vertices) (s : Set (BridgePath 2)) := by
    intro p hp q hq he
    cases p
    cases q
    cases he
    rfl
  exact (Finset.card_le_card_of_injOn _ hm hi).trans (allPaths_card n)
