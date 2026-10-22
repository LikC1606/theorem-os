import ChallengePrelude

namespace OAI.SnakyConditional.OrdinaryStrategy

variable {α : Type*} [DecidableEq α] [Infinite α]

noncomputable def freshCell (M B : Finset α) : α :=
  Classical.choose (Finset.exists_notMem (M ∪ B))

lemma freshCell_legal (M B : Finset α) :
    freshCell M B ∉ M ∧ freshCell M B ∉ B := by
  have h := Classical.choose_spec (Finset.exists_notMem (M ∪ B))
  simpa only [freshCell, Finset.mem_union, not_or] using h

def Winning (G : Finset α → Prop) : ℕ → Finset α → Finset α → Prop
  | 0, M, _ => G M
  | n + 1, M, B => ∃ a : α, a ∉ M ∧ a ∉ B ∧
      ∀ b : α, b ∉ insert a M → b ∉ B → Winning G n (insert a M) (insert b B)

noncomputable def winningPolicy (G : Finset α → Prop) : Policy α := by
  classical
  exact fun n M B => if h : ∃ a : α, a ∉ M ∧ a ∉ B ∧
      ∀ b : α, b ∉ insert a M → b ∉ B → Winning G (n - 1) (insert a M) (insert b B)
    then Classical.choose h else freshCell M B

lemma winningPolicy_legal (G : Finset α → Prop) (n : ℕ) (M B : Finset α) :
    winningPolicy G n M B ∉ M ∧ winningPolicy G n M B ∉ B := by
  classical
  unfold winningPolicy
  split_ifs with h
  · exact ⟨(Classical.choose_spec h).1, (Classical.choose_spec h).2.1⟩
  · exact freshCell_legal M B

lemma winningPolicy_step (G : Finset α → Prop) (n : ℕ) (M B : Finset α)
    (h : Winning G (n + 1) M B) (b : α)
    (hbM : b ∉ insert (winningPolicy G (n + 1) M B) M) (hbB : b ∉ B) :
    Winning G n (insert (winningPolicy G (n + 1) M B) M) (insert b B) := by
  classical
  simp only [Winning] at h
  have hs : winningPolicy G (n + 1) M B = Classical.choose h := by
    simp only [winningPolicy, Nat.add_sub_cancel, dif_pos h]
  rw [hs] at hbM ⊢
  exact (Classical.choose_spec h).2.2 b hbM hbB

lemma playState_card_maker (σ : Policy α)
    (hσ : ∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B)
    (N : ℕ) (β : ℕ → α) (k : ℕ) :
    (playState σ N β ∅ ∅ k).1.card = k := by
  induction k with
  | zero => simp [playState]
  | succ k ih =>
      simp only [playState, Finset.card_insert_of_notMem (hσ _ _ _).1, ih]

lemma playState_legal_before_final (σ : Policy α)
    (hσ : ∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B)
    (N : ℕ) (β : ℕ → α) (hβ : LegalRepliesBeforeFinal σ N β ∅ ∅) :
    ∀ k, k < N →
      Disjoint (playState σ N β ∅ ∅ k).1 (playState σ N β ∅ ∅ k).2 ∧
      (playState σ N β ∅ ∅ k).2.card = k := by
  intro k
  induction k with
  | zero => intro hk; simp [playState]
  | succ k ih =>
      intro hk
      obtain ⟨hd, hc⟩ := ih (by omega)
      obtain ⟨hbM, hbB⟩ := hβ k hk
      simp only [playState]
      constructor
      · apply Finset.disjoint_insert_right.mpr
        refine ⟨hbM, ?_⟩
        exact Finset.disjoint_insert_left.mpr ⟨(hσ _ _ _).2, hd⟩
      · exact (Finset.card_insert_of_notMem hbB).trans (congrArg (· + 1) hc)

lemma playState_final_disjoint (σ : Policy α)
    (hσ : ∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B)
    (N : ℕ) (hN : 0 < N) (β : ℕ → α)
    (hβ : LegalRepliesBeforeFinal σ N β ∅ ∅) :
    Disjoint (playState σ N β ∅ ∅ N).1 (playState σ N β ∅ ∅ (N - 1)).2 := by
  cases N with
  | zero => omega
  | succ n =>
      have hd := (playState_legal_before_final σ hσ (n + 1) β hβ n (by omega)).1
      simp only [Nat.succ_sub_one, playState]
      exact Finset.disjoint_insert_left.mpr ⟨(hσ _ _ _).2, hd⟩

lemma winningPolicy_play_invariant (G : Finset α → Prop) (N : ℕ)
    (hwin : Winning G N ∅ ∅) (β : ℕ → α)
    (hβ : LegalRepliesBeforeFinal (winningPolicy G) N β ∅ ∅) :
    ∀ k, k < N → Winning G (N - k)
      (playState (winningPolicy G) N β ∅ ∅ k).1
      (playState (winningPolicy G) N β ∅ ∅ k).2 := by
  intro k
  induction k with
  | zero => intro hk; simpa only [Nat.sub_zero, playState] using hwin
  | succ k ih =>
      intro hk
      have hw := ih (by omega)
      obtain ⟨hbM, hbB⟩ := hβ k hk
      have hsub : N - k = (N - (k + 1)) + 1 := by omega
      rw [hsub] at hw
      have hs := winningPolicy_step G (N - (k + 1)) _ _ hw (β k)
      simp only [makerAt, hsub] at hbM
      have hh := hs hbM hbB
      simpa only [playState, hsub] using hh

lemma winningPolicy_wins (G : Finset α → Prop) (N : ℕ) (hN : 0 < N)
    (hwin : Winning G N ∅ ∅) (β : ℕ → α)
    (hβ : LegalRepliesBeforeFinal (winningPolicy G) N β ∅ ∅) :
    G (playState (winningPolicy G) N β ∅ ∅ N).1 := by
  cases N with
  | zero => omega
  | succ n =>
      have hw := winningPolicy_play_invariant G (n + 1) hwin β hβ n (by omega)
      have hsub : n + 1 - n = 1 := by omega
      rw [hsub] at hw
      let M := (playState (winningPolicy G) (n + 1) β ∅ ∅ n).1
      let B := (playState (winningPolicy G) (n + 1) β ∅ ∅ n).2
      let a := winningPolicy G 1 M B
      let b := freshCell (insert a M) B
      have hb := freshCell_legal (insert a M) B
      have hh := winningPolicy_step G 0 M B hw b hb.1 hb.2
      change G (insert a M) at hh
      simpa only [playState, hsub] using hh

theorem ordinary_policy_of_winning (G : Finset α → Prop) (N : ℕ) (hN : 0 < N)
    (hwin : Winning G N ∅ ∅) :
    ∃ σ : Policy α,
      (∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) ∧
      ∀ β : ℕ → α, LegalRepliesBeforeFinal σ N β ∅ ∅ →
        G (playState σ N β ∅ ∅ N).1 ∧
        (playState σ N β ∅ ∅ N).1.card = N ∧
        Disjoint (playState σ N β ∅ ∅ N).1 (playState σ N β ∅ ∅ (N - 1)).2 ∧
        ∀ k, k < N →
          Disjoint (playState σ N β ∅ ∅ k).1 (playState σ N β ∅ ∅ k).2 ∧
          (playState σ N β ∅ ∅ k).2.card = k := by
  refine ⟨winningPolicy G, winningPolicy_legal G, ?_⟩
  intro β hβ
  exact ⟨winningPolicy_wins G N hN hwin β hβ,
    playState_card_maker _ (winningPolicy_legal G) N β N,
    playState_final_disjoint _ (winningPolicy_legal G) N hN β hβ,
    playState_legal_before_final _ (winningPolicy_legal G) N β hβ⟩

end OAI.SnakyConditional.OrdinaryStrategy
