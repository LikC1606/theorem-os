import Mathlib

namespace OAI.SnakyConditional

abbrev Cell := ℤ × ℤ
def snaky : Finset Cell := {(0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1)}
def orient (r : Fin 8) (p : Cell) : Cell :=
  match r.val with
  | 0 => (p.1, p.2)
  | 1 => (p.2, p.1)
  | 2 => (p.1, -p.2)
  | 3 => (-p.2, p.1)
  | 4 => (-p.1, p.2)
  | 5 => (p.2, -p.1)
  | 6 => (-p.1, -p.2)
  | _ => (-p.2, -p.1)
def placement (r : Fin 8) (t p : Cell) : Cell := orient r p + t
def HasSnaky (M : Finset Cell) : Prop :=
  ∃ (r : Fin 8) (t : Cell), snaky.image (placement r t) ⊆ M

namespace OrdinaryStrategy

variable {α : Type*} [DecidableEq α]

abbrev Policy (α : Type*) := ℕ → Finset α → Finset α → α
def playState (σ : Policy α) (N : ℕ) (β : ℕ → α) (M₀ B₀ : Finset α) :
    ℕ → Finset α × Finset α
  | 0 => (M₀, B₀)
  | k + 1 =>
      let state := playState σ N β M₀ B₀ k
      (insert (σ (N - k) state.1 state.2) state.1, insert (β k) state.2)
def makerAt (σ : Policy α) (N : ℕ) (β : ℕ → α) (M₀ B₀ : Finset α) (k : ℕ) : α :=
  let state := playState σ N β M₀ B₀ k
  σ (N - k) state.1 state.2
def LegalRepliesBeforeFinal (σ : Policy α) (N : ℕ) (β : ℕ → α)
    (M₀ B₀ : Finset α) : Prop :=
  ∀ k, k + 1 < N →
    β k ∉ insert (makerAt σ N β M₀ B₀ k) (playState σ N β M₀ B₀ k).1 ∧
    β k ∉ (playState σ N β M₀ B₀ k).2
end OrdinaryStrategy

open OrdinaryStrategy

def qhb (t : Lean.Syntax) : Lean.Elab.Tactic.TacticM Unit := Lean.withOptions (fun o => Lean.maxHeartbeats.set o 0) (withTheReader Lean.Core.Context (fun c => { c with maxHeartbeats := 0 }) (Lean.Elab.Tactic.evalTactic t))
noncomputable def freshCell {α : Type*} [DecidableEq α] [Infinite α] (M B : Finset α) : α := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (Classical.choose (Finset.exists_notMem (M ∪ B)))
def freshCell_legal {α : Type*} [DecidableEq α] [Infinite α] (M B : Finset α) :
    freshCell M B ∉ M ∧ freshCell M B ∉ B := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          have h := Classical.choose_spec (Finset.exists_notMem (M ∪ B))
          simpa only [freshCell,Finset.mem_union,not_or] using h)
def Winning {α : Type*} [DecidableEq α] [Infinite α] (G : Finset α → Prop) : ℕ → Finset α → Finset α → Prop
  | 0,M,_ => G M
  | n + 1,M,B => ∃ a : α,a ∉ M ∧ a ∉ B ∧
      ∀ b : α,b ∉ insert a M → b ∉ B → Winning G n (insert a M) (insert b B)
noncomputable def winningPolicy {α : Type*} [DecidableEq α] [Infinite α] (G : Finset α → Prop) : Policy α := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          classical
          exact fun n M B => if h : ∃ a : α,a ∉ M ∧ a ∉ B ∧
              ∀ b : α,b ∉ insert a M → b ∉ B → Winning G (n - 1) (insert a M) (insert b B)
            then Classical.choose h else freshCell M B)
def winningPolicy_legal {α : Type*} [DecidableEq α] [Infinite α] (G : Finset α → Prop) (n : ℕ) (M B : Finset α) :
    winningPolicy G n M B ∉ M ∧ winningPolicy G n M B ∉ B := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          classical
          unfold winningPolicy
          split_ifs with h
          · exact ⟨(Classical.choose_spec h).1,(Classical.choose_spec h).2.1⟩
          · exact freshCell_legal M B)
def winningPolicy_step {α : Type*} [DecidableEq α] [Infinite α] (G : Finset α → Prop) (n : ℕ) (M B : Finset α)
    (h : Winning G (n + 1) M B) (b : α)
    (hbM : b ∉ insert (winningPolicy G (n + 1) M B) M) (hbB : b ∉ B) :
    Winning G n (insert (winningPolicy G (n + 1) M B) M) (insert b B) := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          classical
          simp only [Winning] at h
          have hs : winningPolicy G (n + 1) M B = Classical.choose h := by
            simp only [winningPolicy,Nat.add_sub_cancel,dif_pos h]
          rw [hs] at hbM ⊢
          exact (Classical.choose_spec h).2.2 b hbM hbB)
def playState_card_maker {α : Type*} [DecidableEq α] [Infinite α] (σ : Policy α)
    (hσ : ∀ r M B,σ r M B ∉ M ∧ σ r M B ∉ B)
    (N : ℕ) (β : ℕ → α) (k : ℕ) :
    (playState σ N β ∅ ∅ k).1.card = k := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          induction k with
          | zero => simp [playState]
          | succ k ih =>
              simp only [playState,Finset.card_insert_of_notMem (hσ _ _ _).1,ih])
def playState_legal_before_final {α : Type*} [DecidableEq α] [Infinite α] (σ : Policy α)
    (hσ : ∀ r M B,σ r M B ∉ M ∧ σ r M B ∉ B)
    (N : ℕ) (β : ℕ → α) (hβ : LegalRepliesBeforeFinal σ N β ∅ ∅) :
    ∀ k,k < N →
      Disjoint (playState σ N β ∅ ∅ k).1 (playState σ N β ∅ ∅ k).2 ∧
      (playState σ N β ∅ ∅ k).2.card = k := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          intro k
          induction k with
          | zero => intro hk; simp [playState]
          | succ k ih =>
              intro hk
              obtain ⟨hd,hc⟩ := ih (by omega)
              obtain ⟨hbM,hbB⟩ := hβ k hk
              simp only [playState]
              constructor
              · apply Finset.disjoint_insert_right.mpr
                refine ⟨hbM,?_⟩
                exact Finset.disjoint_insert_left.mpr ⟨(hσ _ _ _).2,hd⟩
              · exact (Finset.card_insert_of_notMem hbB).trans (congrArg (· + 1) hc))
def playState_final_disjoint {α : Type*} [DecidableEq α] [Infinite α] (σ : Policy α)
    (hσ : ∀ r M B,σ r M B ∉ M ∧ σ r M B ∉ B)
    (N : ℕ) (hN : 0 < N) (β : ℕ → α)
    (hβ : LegalRepliesBeforeFinal σ N β ∅ ∅) :
    Disjoint (playState σ N β ∅ ∅ N).1 (playState σ N β ∅ ∅ (N - 1)).2 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          cases N with
          | zero => omega
          | succ n =>
              have hd := (playState_legal_before_final σ hσ (n + 1) β hβ n (by omega)).1
              simp only [Nat.succ_sub_one,playState]
              exact Finset.disjoint_insert_left.mpr ⟨(hσ _ _ _).2,hd⟩)
def winningPolicy_play_invariant {α : Type*} [DecidableEq α] [Infinite α] (G : Finset α → Prop) (N : ℕ)
    (hwin : Winning G N ∅ ∅) (β : ℕ → α)
    (hβ : LegalRepliesBeforeFinal (winningPolicy G) N β ∅ ∅) :
    ∀ k,k < N → Winning G (N - k)
      (playState (winningPolicy G) N β ∅ ∅ k).1
      (playState (winningPolicy G) N β ∅ ∅ k).2 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          intro k
          induction k with
          | zero => intro hk; simpa only [Nat.sub_zero,playState] using hwin
          | succ k ih =>
              intro hk
              have hw := ih (by omega)
              obtain ⟨hbM,hbB⟩ := hβ k hk
              have hsub : N - k = (N - (k + 1)) + 1 := by omega
              rw [hsub] at hw
              have hs := winningPolicy_step G (N - (k + 1)) _ _ hw (β k)
              simp only [makerAt,hsub] at hbM
              have hh := hs hbM hbB
              simpa only [playState,hsub] using hh)
def winningPolicy_wins {α : Type*} [DecidableEq α] [Infinite α] (G : Finset α → Prop) (N : ℕ) (hN : 0 < N)
    (hwin : Winning G N ∅ ∅) (β : ℕ → α)
    (hβ : LegalRepliesBeforeFinal (winningPolicy G) N β ∅ ∅) :
    G (playState (winningPolicy G) N β ∅ ∅ N).1 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
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
              simpa only [playState,hsub] using hh)
def ordinary_policy_of_winning {α : Type*} [DecidableEq α] [Infinite α] (G : Finset α → Prop) (N : ℕ) (hN : 0 < N)
    (hwin : Winning G N ∅ ∅) :
    ∃ σ : Policy α,
      (∀ r M B,σ r M B ∉ M ∧ σ r M B ∉ B) ∧
      ∀ β : ℕ → α,LegalRepliesBeforeFinal σ N β ∅ ∅ →
        G (playState σ N β ∅ ∅ N).1 ∧
        (playState σ N β ∅ ∅ N).1.card = N ∧
        Disjoint (playState σ N β ∅ ∅ N).1 (playState σ N β ∅ ∅ (N - 1)).2 ∧
        ∀ k,k < N →
          Disjoint (playState σ N β ∅ ∅ k).1 (playState σ N β ∅ ∅ k).2 ∧
          (playState σ N β ∅ ∅ k).2.card = k := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          refine ⟨winningPolicy G,winningPolicy_legal G,?_⟩
          intro β hβ
          exact ⟨winningPolicy_wins G N hN hwin β hβ,
            playState_card_maker _ (winningPolicy_legal G) N β N,
            playState_final_disjoint _ (winningPolicy_legal G) N hN β hβ,
            playState_legal_before_final _ (winningPolicy_legal G) N β hβ⟩)
def winning_of_goal {α : Type*} [DecidableEq α] [Infinite α] (G : Finset α → Prop)
    (hG : ∀ {M M'},M ⊆ M' → G M → G M')
    (n : ℕ) (M B : Finset α) (h : G M) : Winning G n M B := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          induction n generalizing M B with
          | zero => exact h
          | succ n ih =>
              let a := freshCell M B
              have ha := freshCell_legal M B
              refine ⟨a,ha.1,ha.2,?_⟩
              intro b hbM hbB
              exact ih (insert a M) (insert b B) (hG (Finset.subset_insert _ _) h))
def winning_mono_time {α : Type*} [DecidableEq α] [Infinite α] (G : Finset α → Prop)
    (hG : ∀ {M M'},M ⊆ M' → G M → G M')
    {n m : ℕ} (hnm : n ≤ m) (M B : Finset α) (h : Winning G n M B) :
    Winning G m M B := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          induction n generalizing m M B with
          | zero => exact winning_of_goal G hG m M B h
          | succ n ih =>
              cases m with
              | zero => omega
              | succ m =>
                  obtain ⟨a,haM,haB,hs⟩ := h
                  refine ⟨a,haM,haB,?_⟩
                  intro b hbM hbB
                  exact ih (by omega) _ _ (hs b hbM hbB))
def Threat {α : Type*} [DecidableEq α] [Infinite α] (G : Finset α → Prop) (A H : Finset α) (n : ℕ) : Prop := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (∀ M B,A ⊆ M → Disjoint H B → Winning G n M B)
def threat_leaf {α : Type*} [DecidableEq α] [Infinite α] (G : Finset α → Prop)
    (hG : ∀ {M M'},M ⊆ M' → G M → G M')
    (p : α) (S : Finset α) (hS : G S) : Threat G (S.erase p) S 1 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          intro M B hA hB
          by_cases hpM : p ∈ M
          · apply winning_of_goal G hG 1 M B
            apply hG ?_ hS
            intro x hx
            by_cases hxp : x = p
            · simpa [hxp] using hpM
            · exact hA (Finset.mem_erase.mpr ⟨hxp,hx⟩)
          · by_cases hpS : p ∈ S
            · have hpB : p ∉ B := fun h => Finset.disjoint_left.mp hB hpS h
              refine ⟨p,hpM,hpB,?_⟩
              intro b hbM hbB
              change G (insert p M)
              apply hG ?_ hS
              intro x hx
              by_cases hxp : x = p
              · simp [hxp]
              · exact Finset.mem_insert_of_mem (hA (Finset.mem_erase.mpr ⟨hxp,hx⟩))
            · apply winning_of_goal G hG 1 M B
              apply hG ?_ hS
              intro x hx
              exact hA (Finset.mem_erase.mpr ⟨fun h => hpS (h ▸ hx),hx⟩))
def winning_map {α : Type*} [DecidableEq α] [Infinite α] (G : Finset α → Prop) (e : α ≃ α)
    (hG : ∀ M,G M → G (M.image e))
    (n : ℕ) (M B : Finset α) (hw : Winning G n M B) :
    Winning G n (M.image e) (B.image e) := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          induction n generalizing M B with
          | zero => exact hG M hw
          | succ n ih =>
              obtain ⟨a,haM,haB,hs⟩ := hw
              refine ⟨e a,?_,?_,?_⟩
              · simpa using haM
              · simpa using haB
              · intro b hbM hbB
                have hbM' : e.symm b ∉ insert a M := by
                  intro h
                  apply hbM
                  simpa only [Finset.image_insert,Equiv.apply_symm_apply] using
                    (Finset.mem_image_of_mem e h)
                have hbB' : e.symm b ∉ B := by
                  intro h
                  apply hbB
                  simpa only [Equiv.apply_symm_apply] using (Finset.mem_image_of_mem e h)
                simpa only [Finset.image_insert,Equiv.apply_symm_apply] using
                  (ih (insert a M) (insert (e.symm b) B) (hs _ hbM' hbB')))
def threat_map {α : Type*} [DecidableEq α] [Infinite α] (G : Finset α → Prop) (e : α ≃ α)
    (hG : ∀ M,G M → G (M.image e))
    (A H : Finset α) (n : ℕ) (hw : Threat G A H n) :
    Threat G (A.image e) (H.image e) n := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          intro M B hAM hHB
          have hA : A ⊆ M.image e.symm := by
            intro a ha
            have h := hAM (Finset.mem_image_of_mem e ha)
            simpa only [Equiv.symm_apply_apply] using Finset.mem_image_of_mem e.symm h
          have hB : Disjoint H (B.image e.symm) := by
            apply Finset.disjoint_left.mpr
            intro a ha hab
            obtain ⟨b,hb,hab⟩ := Finset.mem_image.mp hab
            apply Finset.disjoint_left.mp hHB (Finset.mem_image_of_mem e ha)
            simpa [← hab] using hb
          have hh := winning_map G e hG n _ _ (hw _ _ hA hB)
          simpa only [Finset.image_image,Function.comp_def,Equiv.apply_symm_apply,
            Finset.image_id'] using hh)
abbrev ThreatData (α : Type*) := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (Finset α × Finset α × ℕ)
def ThreatData.threatDataA {α : Type*} (x : ThreatData α) : Finset α := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (x.1)
def ThreatData.threatDataH {α : Type*} (x : ThreatData α) : Finset α := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (x.2.1)
def ThreatData.threatDataHeight {α : Type*} (x : ThreatData α) : ℕ := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (x.2.2)
def threat_fork {α : Type*} [DecidableEq α] (G : Finset α → Prop) [Infinite α] (hG : ∀ {M M'},M ⊆ M' → G M → G M')
    (p : α) (ds : List (ThreatData α)) (hne : ds ≠ []) (n : ℕ)
    (hs : ∀ d ∈ ds,Threat G d.threatDataA d.threatDataH d.threatDataHeight)
    (hh : ∀ d ∈ ds,d.threatDataHeight ≤ n)
    (A H : Finset α)
    (hA : ∀ d ∈ ds,d.threatDataA ⊆ insert p A)
    (hH : ∀ d ∈ ds,d.threatDataH ⊆ H) (hpH : p ∈ H)
    (hcommon : ∀ b,(∀ d ∈ ds,b ∈ d.threatDataH) → b ∈ insert p A) :
    Threat G A H (n + 1) := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          intro M B hAM hHB
          have hMA : insert p A ⊆ insert p M := Finset.insert_subset_insert p hAM
          by_cases hpM : p ∈ M
          · obtain ⟨d,hd⟩ := List.exists_mem_of_ne_nil ds hne
            have hdA : d.threatDataA ⊆ M := by
              intro x hx
              rcases Finset.mem_insert.mp (hA d hd hx) with he | ha
              · simpa [he] using hpM
              · exact hAM ha
            have hdB : Disjoint d.threatDataH B := hHB.mono_left (hH d hd)
            exact winning_mono_time G hG (by have := hh d hd; omega) M B (hs d hd M B hdA hdB)
          · have hpB : p ∉ B := fun h => Finset.disjoint_left.mp hHB hpH h
            refine ⟨p,hpM,hpB,?_⟩
            intro b hbM hbB
            have hex : ∃ d ∈ ds,b ∉ d.threatDataH := by
              by_contra hx
              push_neg at hx
              have hb := hcommon b hx
              exact hbM (hMA hb)
            obtain ⟨d,hd,hbd⟩ := hex
            have hdB : Disjoint d.threatDataH (insert b B) :=
              Finset.disjoint_insert_right.mpr ⟨hbd,hHB.mono_left (hH d hd)⟩
            exact winning_mono_time G hG (hh d hd) _ _
              (hs d hd (insert p M) (insert b B) (fun x hx => hMA (hA d hd hx)) hdB))
theorem generic_bridge_probe (hwin : Winning HasSnaky 35 ∅ ∅) :
    ∃ σ : Policy Cell,
      (∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) ∧
      ∀ β : ℕ → Cell, LegalRepliesBeforeFinal σ 35 β ∅ ∅ →
        HasSnaky (playState σ 35 β ∅ ∅ 35).1 ∧
        (playState σ 35 β ∅ ∅ 35).1.card = 35 ∧
        Disjoint (playState σ 35 β ∅ ∅ 35).1 (playState σ 35 β ∅ ∅ 34).2 ∧
        ∀ k, k < 35 →
          Disjoint (playState σ 35 β ∅ ∅ k).1 (playState σ 35 β ∅ ∅ k).2 ∧
          (playState σ 35 β ∅ ∅ k).2.card = k := by
  exact ordinary_policy_of_winning HasSnaky 35 (by omega) hwin

#print axioms generic_bridge_probe
end OAI.SnakyConditional
