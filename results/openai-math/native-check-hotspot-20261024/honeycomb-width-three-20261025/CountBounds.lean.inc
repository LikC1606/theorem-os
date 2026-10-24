
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
