
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
