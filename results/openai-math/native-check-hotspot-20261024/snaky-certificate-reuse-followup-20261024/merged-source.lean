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
abbrev qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (ℤ × ℤ)
def qorigin : qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ((0,0))
def qsnaky : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)})
def qorient (r : Fin 8) (p : qCell) : qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (match r.val with
  | 0 => (p.1,p.2)
  | 1 => (p.2,p.1)
  | 2 => (p.1,-p.2)
  | 3 => (-p.2,p.1)
  | 4 => (-p.1,p.2)
  | 5 => (p.2,-p.1)
  | 6 => (-p.1,-p.2)
  | _ => (-p.2,-p.1))
def qplacement (r : Fin 8) (t p : qCell) : qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (qorient r p + t)
def qbasePoint (i : Fin 6) : qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (![(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)] i)
def qbaseEnvelope (i : Fin 6) : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (qsnaky.image (qplacement 0 (-qbasePoint i)))
def qbaseRequired (i : Fin 6) : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ((qbaseEnvelope i).erase qorigin)
abbrev qT := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (ℕ × Fin 8 × Fin 10 × Fin 10)
def qT.child (x : qT) : ℕ := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (x.1)
def qT.rotation (x : qT) : Fin 8 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (x.2.1)
def qT.xDigit (x : qT) : Fin 10 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (x.2.2.1)
def qT.yDigit (x : qT) : Fin 10 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (x.2.2.2)
def qT.shift (t : qT) : qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (((t.xDigit.val : ℤ) - 4,(t.yDigit.val : ℤ) - 4))
abbrev qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (ℕ × List qT)
def qE.index (x : qE) : ℕ := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (x.1)
def qE.terms (x : qE) : List qT := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (x.2)
def qemptyEntry : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨0,[]⟩)
def qv6 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨6,[⟨0,0,0,3⟩]⟩)
def qv7 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨7,[⟨4,0,3,4⟩,⟨6,0,5,4⟩]⟩)
def qv8 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨8,[⟨0,4,8,3⟩,⟨6,4,3,4⟩]⟩)
def qv9 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨9,[⟨0,4,5,4⟩,⟨6,4,0,5⟩]⟩)
def qv10 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨10,[⟨2,0,2,3⟩,⟨2,6,2,4⟩]⟩)
def qv11 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨11,[⟨6,4,2,5⟩,⟨6,6,2,3⟩]⟩)
def qv12 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨12,[⟨0,6,5,4⟩,⟨0,0,0,3⟩]⟩)
def qv13 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨13,[⟨6,6,0,3⟩,⟨6,4,0,5⟩]⟩)
def qv14 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨14,[⟨0,6,5,4⟩,⟨3,6,1,4⟩]⟩)
def qv15 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨15,[⟨0,6,6,4⟩,⟨3,6,2,4⟩]⟩)
def qv16 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨16,[⟨3,6,3,4⟩,⟨0,6,7,4⟩]⟩)
def qv17 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨17,[⟨0,6,5,4⟩,⟨3,0,3,3⟩]⟩)
def qv18 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨18,[⟨3,6,2,4⟩,⟨3,0,4,3⟩]⟩)
def qv19 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨19,[⟨6,4,1,5⟩,⟨6,0,6,5⟩]⟩)
def qv20 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨20,[⟨6,4,0,5⟩,⟨6,0,5,5⟩]⟩)
def qv21 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨21,[⟨4,6,2,3⟩,⟨6,0,6,5⟩]⟩)
def qv22 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨22,[⟨0,6,7,5⟩,⟨3,0,5,4⟩]⟩)
def qv23 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨23,[⟨0,6,6,4⟩,⟨0,0,1,3⟩]⟩)
def qv24 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨24,[⟨0,0,0,3⟩,⟨17,0,5,4⟩]⟩)
def qv25 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨25,[⟨0,0,0,3⟩,⟨14,0,5,4⟩]⟩)
def qv26 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨26,[⟨0,4,6,4⟩,⟨6,0,6,5⟩]⟩)
def qv27 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨27,[⟨0,6,5,4⟩,⟨6,4,0,5⟩]⟩)
def qv28 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨28,[⟨6,1,4,5⟩,⟨0,6,6,4⟩]⟩)
def qv29 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨29,[⟨1,4,7,3⟩,⟨6,3,4,5⟩]⟩)
def qv30 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨30,[⟨0,0,1,3⟩,⟨14,0,6,4⟩]⟩)
def qv31 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨31,[⟨0,0,1,4⟩,⟨17,0,6,5⟩]⟩)
def qv32 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨32,[⟨0,4,8,3⟩,⟨6,3,4,5⟩]⟩)
def qv33 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨33,[⟨0,0,2,4⟩,⟨17,0,7,5⟩]⟩)
def qv34 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨34,[⟨6,1,4,5⟩,⟨1,6,5,4⟩]⟩)
def qv35 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨35,[⟨0,0,2,4⟩,⟨14,0,7,5⟩]⟩)
def qv36 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨36,[⟨0,0,3,4⟩,⟨17,0,8,5⟩]⟩)
def qv37 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨37,[⟨6,3,4,5⟩,⟨2,4,6,3⟩]⟩)
def qv38 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨38,[⟨3,0,3,3⟩,⟨16,0,2,4⟩]⟩)
def qv39 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨39,[⟨0,0,1,3⟩,⟨17,0,6,4⟩]⟩)
def qv40 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨40,[⟨3,0,4,3⟩,⟨16,0,3,4⟩]⟩)
def qv41 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨41,[⟨6,3,3,5⟩,⟨1,4,6,3⟩]⟩)
def qv42 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨42,[⟨0,6,6,4⟩,⟨6,4,1,5⟩]⟩)
def qv43 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨43,[⟨2,4,5,3⟩,⟨6,3,3,5⟩]⟩)
def qv44 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨44,[⟨4,4,1,5⟩,⟨7,0,4,5⟩]⟩)
def qv45 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨45,[⟨6,4,0,5⟩,⟨7,0,4,5⟩]⟩)
def qv46 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨46,[⟨6,6,0,3⟩,⟨7,0,4,5⟩]⟩)
def qv47 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨47,[⟨6,3,3,5⟩,⟨6,2,7,3⟩]⟩)
def qv48 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨48,[⟨6,3,4,5⟩,⟨6,2,8,3⟩]⟩)
def qv49 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨49,[⟨4,7,3,1⟩,⟨7,1,5,4⟩]⟩)
def qv50 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨50,[⟨6,3,3,5⟩,⟨7,1,5,4⟩]⟩)
def qv51 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨51,[⟨10,2,5,3⟩,⟨10,0,5,4⟩,⟨26,2,3,4⟩,⟨26,0,3,3⟩]⟩)
def qv52 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨52,[⟨0,0,0,3⟩,⟨0,4,7,3⟩]⟩)
def qv53 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨53,[⟨6,4,3,4⟩,⟨3,1,4,5⟩]⟩)
def qv54 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨54,[⟨22,0,2,3⟩,⟨3,6,1,4⟩]⟩)
def qv55 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨55,[⟨7,4,0,5⟩,⟨7,0,4,5⟩]⟩)
def qv56 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨56,[⟨7,4,0,5⟩,⟨7,6,0,3⟩]⟩)
def qv57 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨57,[⟨0,6,5,4⟩,⟨7,0,4,5⟩]⟩)
def qv58 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨58,[⟨0,4,5,4⟩,⟨7,0,4,5⟩]⟩)
def qv59 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨59,[⟨0,6,5,4⟩,⟨7,4,0,5⟩]⟩)
def qv60 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨60,[⟨6,6,1,3⟩,⟨49,1,6,4⟩]⟩)
def qv61 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨61,[⟨6,0,5,4⟩,⟨14,1,4,5⟩]⟩)
def qv62 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨62,[⟨6,6,0,3⟩,⟨53,0,1,5⟩]⟩)
def qv63 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨63,[⟨4,3,4,3⟩,⟨50,0,5,4⟩]⟩)
def qv64 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨64,[⟨6,6,3,4⟩,⟨49,1,8,5⟩]⟩)
def qv65 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨65,[⟨6,6,0,3⟩,⟨49,1,5,4⟩]⟩)
def qv66 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨66,[⟨6,3,4,5⟩,⟨53,5,6,4⟩]⟩)
def qv67 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨67,[⟨6,1,4,5⟩,⟨9,2,5,4⟩]⟩)
def qv68 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨68,[⟨6,4,0,5⟩,⟨44,0,5,4⟩]⟩)
def qv69 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨69,[⟨6,3,4,5⟩,⟨34,0,6,5⟩]⟩)
def qv70 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨70,[⟨4,3,4,3⟩,⟨41,0,5,4⟩]⟩)
def qv71 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨71,[⟨6,1,4,5⟩,⟨23,2,4,3⟩]⟩)
def qv72 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨72,[⟨0,5,3,8⟩,⟨8,6,5,4⟩]⟩)
def qv73 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨73,[⟨4,3,3,4⟩,⟨50,0,4,5⟩]⟩)
def qv74 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨74,[⟨2,7,4,3⟩,⟨53,0,3,3⟩]⟩)
def qv75 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨75,[⟨0,0,1,3⟩,⟨9,0,7,3⟩]⟩)
def qv76 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨76,[⟨0,7,5,7⟩,⟨14,0,7,5⟩]⟩)
def qv77 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨77,[⟨0,5,3,7⟩,⟨12,0,5,4⟩]⟩)
def qv78 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨78,[⟨6,4,3,4⟩,⟨52,0,5,4⟩]⟩)
def qv79 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨79,[⟨6,1,5,5⟩,⟨48,0,3,4⟩]⟩)
def qv80 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨80,[⟨0,6,6,4⟩,⟨13,4,2,4⟩]⟩)
def qv81 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨81,[⟨4,3,4,3⟩,⟨43,0,5,4⟩]⟩)
def qv82 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨82,[⟨6,1,4,5⟩,⟨36,0,1,3⟩]⟩)
def qv83 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨83,[⟨0,7,5,7⟩,⟨67,2,6,3⟩]⟩)
def qv84 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨84,[⟨6,3,4,5⟩,⟨67,0,6,4⟩]⟩)
def qv85 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨85,[⟨9,0,6,3⟩,⟨8,4,5,4⟩]⟩)
def qv86 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨86,[⟨0,6,5,4⟩,⟨67,3,1,5⟩]⟩)
def qv87 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨87,[⟨0,5,3,7⟩,⟨24,2,5,3⟩]⟩)
def qv88 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨88,[⟨0,6,6,4⟩,⟨67,3,2,5⟩]⟩)
def qv89 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨89,[⟨8,3,3,1⟩,⟨7,1,5,4⟩]⟩)
def qv90 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨90,[⟨31,0,3,3⟩,⟨54,6,0,3⟩,⟨54,0,5,4⟩,⟨31,6,2,4⟩]⟩)
def qv91 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨91,[⟨6,3,4,5⟩,⟨74,5,7,3⟩]⟩)
def qv92 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨92,[⟨6,1,4,5⟩,⟨33,0,2,3⟩]⟩)
def qv93 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨93,[⟨4,3,4,3⟩,⟨47,0,5,4⟩]⟩)
def qv94 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨94,[⟨6,1,4,5⟩,⟨27,3,3,6⟩]⟩)
def qv95 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨95,[⟨0,5,3,7⟩,⟨29,0,2,5⟩]⟩)
def qv96 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨96,[⟨6,1,5,5⟩,⟨70,0,3,5⟩]⟩)
def qv97 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨97,[⟨6,6,0,3⟩,⟨44,0,5,4⟩]⟩)
def qv98 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨98,[⟨6,6,2,3⟩,⟨44,0,7,4⟩]⟩)
def qv99 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨99,[⟨2,1,3,2⟩,⟨24,0,5,4⟩]⟩)
def qv100 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨100,[⟨0,6,5,4⟩,⟨48,0,1,4⟩]⟩)
def qv101 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨101,[⟨0,7,4,6⟩,⟨24,0,5,4⟩]⟩)
def qv102 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨102,[⟨6,3,4,5⟩,⟨25,2,6,3⟩]⟩)
def qv103 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨103,[⟨6,3,4,5⟩,⟨71,0,6,4⟩]⟩)
def qv104 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨104,[⟨6,0,5,4⟩,⟨75,0,3,4⟩]⟩)
def qv105 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨105,[⟨6,5,4,3⟩,⟨77,0,4,5⟩]⟩)
def qv106 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨106,[⟨6,1,4,5⟩,⟨36,6,5,4⟩]⟩)
def qv107 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨107,[⟨6,6,0,3⟩,⟨63,1,5,3⟩]⟩)
def qv108 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨108,[⟨4,6,1,3⟩,⟨63,1,5,3⟩]⟩)
def qv109 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨109,[⟨4,6,1,3⟩,⟨55,0,5,4⟩]⟩)
def qv110 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨110,[⟨6,6,1,3⟩,⟨63,1,6,3⟩]⟩)
def qv111 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨111,[⟨6,7,4,3⟩,⟨83,0,4,5⟩]⟩)
def qv112 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨112,[⟨4,1,5,4⟩,⟨93,0,3,5⟩]⟩)
def qv113 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨113,[⟨1,6,6,4⟩,⟨36,6,7,5⟩]⟩)
def qv114 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨114,[⟨6,0,6,5⟩,⟨67,3,2,5⟩]⟩)
def qv115 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨115,[⟨6,2,7,3⟩,⟨70,7,2,5⟩]⟩)
def qv116 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨116,[⟨0,7,4,6⟩,⟨24,2,5,4⟩]⟩)
def qv117 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨117,[⟨6,1,4,5⟩,⟨100,0,5,4⟩]⟩)
def qv118 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨118,[⟨4,7,3,1⟩,⟨61,1,5,4⟩]⟩)
def qv119 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨119,[⟨6,6,1,3⟩,⟨55,0,6,4⟩]⟩)
def qv120 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨120,[⟨4,0,4,5⟩,⟨58,2,5,4⟩]⟩)
def qv121 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨121,[⟨9,3,4,5⟩,⟨7,1,5,4⟩]⟩)
def qv122 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨122,[⟨6,6,3,3⟩,⟨105,1,4,5⟩]⟩)
def qv123 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨123,[⟨6,6,1,3⟩,⟨64,2,2,5⟩]⟩)
def qv124 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨124,[⟨6,1,4,5⟩,⟨31,2,5,4⟩]⟩)
def qv125 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨125,[⟨3,0,4,3⟩,⟨31,2,4,5⟩]⟩)
def qv126 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨126,[⟨6,3,4,5⟩,⟨46,1,5,7⟩]⟩)
def qv127 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨127,[⟨7,0,4,5⟩,⟨44,2,5,4⟩]⟩)
def qv128 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨128,[⟨9,6,1,5⟩,⟨57,0,6,5⟩]⟩)
def qv129 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨129,[⟨6,4,2,5⟩,⟨58,1,3,6⟩]⟩)
def qv130 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨130,[⟨6,1,4,5⟩,⟨60,0,5,4⟩]⟩)
def qv131 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨131,[⟨45,3,4,5⟩,⟨7,1,5,4⟩]⟩)
def qv132 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨132,[⟨6,3,4,5⟩,⟨89,0,5,6⟩]⟩)
def qv133 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨133,[⟨6,7,3,1⟩,⟨92,0,5,5⟩]⟩)
def qv134 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨134,[⟨6,7,3,0⟩,⟨82,0,5,4⟩]⟩)
def qv135 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨135,[⟨7,0,4,5⟩,⟨75,4,2,5⟩,⟨44,0,5,4⟩]⟩)
def qv136 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨136,[⟨6,3,3,7⟩,⟨102,2,3,3⟩]⟩)
def qv137 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨137,[⟨4,1,4,3⟩,⟨96,0,3,4⟩]⟩)
def qv138 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨138,[⟨27,0,5,4⟩,⟨10,1,4,7⟩]⟩)
def qv139 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨139,[⟨28,1,4,5⟩,⟨27,0,5,4⟩]⟩)
def qv140 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨140,[⟨6,7,3,2⟩,⟨82,0,5,6⟩]⟩)
def qv141 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨141,[⟨7,0,4,5⟩,⟨78,2,1,3⟩]⟩)
def qv142 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨142,[⟨72,4,2,3⟩,⟨32,1,4,3⟩,⟨55,2,5,4⟩]⟩)
def qv143 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨143,[⟨6,6,3,4⟩,⟨108,0,8,5⟩]⟩)
def qv144 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨144,[⟨7,0,4,5⟩,⟨104,4,1,5⟩,⟨55,0,5,4⟩]⟩)
def qv145 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨145,[⟨0,5,4,5⟩,⟨91,0,3,4⟩]⟩)
def qv146 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨146,[⟨36,6,5,4⟩,⟨24,1,4,5⟩]⟩)
def qv147 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨147,[⟨53,0,1,5⟩,⟨44,2,5,4⟩]⟩)
def qv148 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨148,[⟨7,1,5,4⟩,⟨46,1,4,5⟩,⟨94,0,5,3⟩,⟨97,1,4,5⟩]⟩)
def qv149 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨149,[⟨16,1,4,3⟩,⟨24,2,5,4⟩]⟩)
def qv150 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨150,[⟨4,6,1,3⟩,⟨126,5,2,5⟩]⟩)
def qv151 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨151,[⟨2,1,4,3⟩,⟨101,2,6,3⟩]⟩)
def qv152 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨152,[⟨6,3,4,5⟩,⟨73,1,7,4⟩]⟩)
def qv153 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨153,[⟨59,4,0,4⟩,⟨27,0,5,4⟩]⟩)
def qv154 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨154,[⟨7,6,4,3⟩,⟨104,0,7,5⟩]⟩)
def qv155 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨155,[⟨7,1,5,4⟩,⟨55,3,4,5⟩]⟩)
def qv156 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨156,[⟨11,0,2,4⟩,⟨98,2,2,4⟩,⟨33,0,2,3⟩]⟩)
def qv157 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨157,[⟨6,3,4,5⟩,⟨57,1,5,6⟩]⟩)
def qv158 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨158,[⟨66,0,3,4⟩,⟨45,1,4,5⟩,⟨46,3,4,5⟩]⟩)
def qv159 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨159,[⟨45,3,4,5⟩,⟨65,1,4,5⟩,⟨7,3,3,4⟩]⟩)
def qv160 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨160,[⟨63,1,8,3⟩,⟨32,3,4,3⟩]⟩)
def qv161 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨161,[⟨15,1,4,5⟩,⟨86,0,5,4⟩]⟩)
def qv162 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨162,[⟨7,3,3,4⟩,⟨127,1,4,5⟩,⟨63,0,3,5⟩,⟨157,0,3,3⟩]⟩)
def qv163 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨163,[⟨44,2,5,4⟩,⟨49,1,5,4⟩,⟨56,4,0,4⟩]⟩)
def qv164 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨164,[⟨6,1,4,5⟩,⟨110,0,5,4⟩]⟩)
def qv165 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨165,[⟨0,7,5,8⟩,⟨107,0,7,5⟩]⟩)
def qv166 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨166,[⟨2,7,4,5⟩,⟨107,0,6,4⟩]⟩)
def qv167 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨167,[⟨57,0,5,4⟩,⟨57,4,0,4⟩]⟩)
def qv168 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨168,[⟨6,1,5,5⟩,⟨152,0,3,4⟩]⟩)
def qv169 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨169,[⟨28,3,4,5⟩,⟨63,1,8,3⟩]⟩)
def qv170 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨170,[⟨4,6,1,3⟩,⟨127,2,5,4⟩]⟩)
def qv171 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨171,[⟨6,0,5,4⟩,⟨91,0,0,5⟩]⟩)
def qv172 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨172,[⟨63,1,5,3⟩,⟨55,6,0,4⟩,⟨64,0,1,3⟩]⟩)
def qv173 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨173,[⟨63,1,5,3⟩,⟨64,6,4,5⟩,⟨55,6,0,4⟩]⟩)
def qv174 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨174,[⟨58,3,4,5⟩,⟨57,1,4,5⟩,⟨84,0,3,4⟩]⟩)
def qv175 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨175,[⟨141,0,5,4⟩,⟨7,2,4,3⟩,⟨63,1,5,3⟩]⟩)
def qv176 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨176,[⟨63,1,5,3⟩,⟨64,6,4,5⟩,⟨55,2,5,4⟩]⟩)
def qv177 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨177,[⟨6,1,4,5⟩,⟨136,3,5,4⟩]⟩)
def qv178 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨178,[⟨37,0,3,4⟩,⟨68,1,4,5⟩,⟨46,3,4,5⟩]⟩)
def qv179 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨179,[⟨6,6,0,3⟩,⟨148,5,5,4⟩]⟩)
def qv180 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨180,[⟨7,3,3,4⟩,⟨63,0,3,5⟩,⟨155,0,4,5⟩,⟨132,0,3,3⟩]⟩)
def qv181 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨181,[⟨24,3,4,5⟩,⟨87,2,6,4⟩,⟨90,0,7,5⟩]⟩)
def qv182 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨182,[⟨12,2,7,3⟩,⟨139,0,7,4⟩]⟩)
def qv183 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨183,[⟨64,2,1,5⟩,⟨63,3,0,3⟩,⟨55,2,5,4⟩]⟩)
def qv184 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨184,[⟨34,3,4,2⟩,⟨35,2,5,4⟩]⟩)
def qv185 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨185,[⟨44,3,4,5⟩,⟨49,0,4,5⟩,⟨84,0,3,4⟩]⟩)
def qv186 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨186,[⟨7,6,0,3⟩,⟨141,2,5,4⟩]⟩)
def qv187 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨187,[⟨6,4,3,4⟩,⟨108,3,4,5⟩]⟩)
def qv188 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨188,[⟨6,3,4,5⟩,⟨112,5,7,4⟩]⟩)
def qv189 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨189,[⟨12,0,5,4⟩,⟨86,4,1,4⟩]⟩)
def qv190 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨190,[⟨46,0,5,4⟩,⟨85,2,3,3⟩,⟨111,3,4,3⟩]⟩)
def qv191 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨191,[⟨6,4,3,4⟩,⟨145,0,4,5⟩]⟩)
def qv192 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨192,[⟨64,1,3,1⟩,⟨103,0,3,4⟩,⟨55,3,4,5⟩]⟩)
def qv193 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨193,[⟨6,6,2,3⟩,⟨162,1,7,4⟩]⟩)
def qv194 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨194,[⟨0,0,0,3⟩,⟨146,4,2,5⟩]⟩)
def qv195 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨195,[⟨6,6,0,3⟩,⟨162,1,5,4⟩]⟩)
def qv196 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨196,[⟨6,3,4,5⟩,⟨187,5,6,4⟩]⟩)
def qv197 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨197,[⟨63,3,0,3⟩,⟨63,1,5,3⟩]⟩)
def qv198 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨198,[⟨7,4,0,5⟩,⟨131,1,5,4⟩]⟩)
def qv199 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨199,[⟨55,1,4,5⟩,⟨64,3,5,1⟩,⟨84,0,3,4⟩]⟩)
def qv200 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨200,[⟨103,0,3,4⟩,⟨64,3,5,1⟩,⟨55,1,4,5⟩]⟩)
def qv201 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨201,[⟨45,3,5,7⟩,⟨82,0,6,5⟩]⟩)
def qv202 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨202,[⟨150,0,5,4⟩,⟨7,0,4,5⟩,⟨108,0,5,4⟩]⟩)
def qv203 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨203,[⟨18,6,1,3⟩,⟨107,0,5,4⟩,⟨163,0,5,4⟩]⟩)
def qv204 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨204,[⟨2,5,4,2⟩,⟨166,2,5,3⟩]⟩)
def qv205 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨205,[⟨4,1,4,3⟩,⟨168,0,3,4⟩]⟩)
def qv206 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨206,[⟨28,3,4,5⟩,⟨135,2,8,4⟩]⟩)
def qv207 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨207,[⟨28,3,4,5⟩,⟨127,0,8,4⟩]⟩)
def qv208 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨208,[⟨7,4,0,5⟩,⟨127,0,5,4⟩]⟩)
def qv209 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨209,[⟨25,0,5,4⟩,⟨81,5,5,7⟩]⟩)
def qv210 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨210,[⟨58,2,5,4⟩,⟨57,0,5,4⟩,⟨117,1,4,5⟩]⟩)
def qv211 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨211,[⟨49,5,5,4⟩,⟨6,6,0,3⟩]⟩)
def qv212 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨212,[⟨6,0,5,4⟩,⟨188,0,0,5⟩]⟩)
def qv213 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨213,[⟨6,0,7,5⟩,⟨191,0,3,5⟩]⟩)
def qv214 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨214,[⟨7,3,3,4⟩,⟨108,3,4,5⟩,⟨95,0,5,2⟩]⟩)
def qv215 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨215,[⟨107,1,4,6⟩,⟨24,0,5,4⟩]⟩)
def qv216 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨216,[⟨7,6,0,3⟩,⟨155,5,5,4⟩]⟩)
def qv217 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨217,[⟨111,1,1,3⟩,⟨55,4,0,4⟩,⟨64,0,1,3⟩]⟩)
def qv218 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨218,[⟨0,5,3,7⟩,⟨182,0,2,4⟩]⟩)
def qv219 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨219,[⟨0,5,3,7⟩,⟨179,2,6,4⟩]⟩)
def qv220 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨220,[⟨56,4,0,4⟩,⟨63,1,5,3⟩,⟨144,2,5,4⟩,⟨154,6,5,4⟩,⟨155,1,5,4⟩]⟩)
def qv221 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨221,[⟨6,6,0,3⟩,⟨180,5,5,4⟩]⟩)
def qv222 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨222,[⟨6,1,4,5⟩,⟨158,5,5,4⟩]⟩)
def qv223 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨223,[⟨63,1,5,3⟩,⟨135,2,5,4⟩,⟨128,0,3,3⟩,⟨111,3,4,3⟩,⟨127,0,5,4⟩]⟩)
def qv224 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨224,[⟨6,1,4,5⟩,⟨212,0,6,3⟩]⟩)
def qv225 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨225,[⟨111,7,7,5⟩,⟨61,4,4,5⟩]⟩)
def qv226 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨226,[⟨10,6,0,3⟩,⟨203,0,5,4⟩,⟨33,0,2,3⟩,⟨193,0,2,4⟩]⟩)
def qv227 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨227,[⟨6,1,5,5⟩,⟨212,0,7,3⟩]⟩)
def qv228 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨228,[⟨82,0,6,5⟩,⟨68,3,5,7⟩]⟩)
def qv229 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨229,[⟨171,0,7,3⟩,⟨45,1,4,5⟩,⟨46,3,4,5⟩]⟩)
def qv230 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨230,[⟨10,6,3,4⟩,⟨193,0,5,5⟩,⟨203,0,8,5⟩,⟨33,0,5,4⟩]⟩)
def qv231 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨231,[⟨6,3,4,5⟩,⟨222,0,6,4⟩]⟩)
def qv232 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨232,[⟨24,2,5,4⟩,⟨107,1,4,6⟩]⟩)
def qv233 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨233,[⟨32,3,3,1⟩,⟨133,0,6,4⟩]⟩)
def qv234 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨234,[⟨180,4,4,5⟩,⟨37,0,3,4⟩,⟨129,0,5,3⟩,⟨63,0,3,5⟩]⟩)
def qv235 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨235,[⟨7,3,3,4⟩,⟨110,0,6,4⟩,⟨70,0,3,5⟩]⟩)
def qv236 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨236,[⟨38,1,4,5⟩,⟨122,7,3,4⟩,⟨181,0,2,3⟩,⟨30,1,4,3⟩]⟩)
def qv237 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨237,[⟨6,3,4,5⟩,⟨172,0,7,4⟩]⟩)
def qv238 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨238,[⟨6,3,4,5⟩,⟨178,5,7,4⟩]⟩)
def qv239 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨239,[⟨0,4,7,3⟩,⟨174,4,3,5⟩]⟩)
def qv240 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨240,[⟨6,1,4,5⟩,⟨237,0,2,4⟩]⟩)
def qv241 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨241,[⟨131,1,5,4⟩,⟨159,1,5,4⟩,⟨61,0,4,5⟩]⟩)
def qv242 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨242,[⟨6,1,4,5⟩,⟨190,0,5,4⟩]⟩)
def qv243 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨243,[⟨6,0,5,4⟩,⟨233,0,2,5⟩]⟩)
def qv244 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨244,[⟨99,4,2,5⟩,⟨99,0,4,5⟩,⟨11,7,3,3⟩,⟨173,2,5,4⟩]⟩)
def qv245 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨245,[⟨64,0,1,3⟩,⟨175,4,0,4⟩,⟨143,6,4,5⟩,⟨186,6,0,4⟩]⟩)
def qv246 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨246,[⟨64,6,4,5⟩,⟨175,2,5,4⟩,⟨186,0,5,4⟩,⟨143,0,1,3⟩]⟩)
def qv247 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨247,[⟨6,4,3,4⟩,⟨229,0,4,5⟩]⟩)
def qv248 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨248,[⟨186,0,7,4⟩,⟨143,0,3,3⟩,⟨175,2,7,4⟩,⟨64,6,6,5⟩]⟩)
def qv249 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨249,[⟨0,7,4,5⟩,⟨225,1,4,1⟩]⟩)
def qv250 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨250,[⟨6,1,4,5⟩,⟨238,0,2,4⟩]⟩)
def qv251 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨251,[⟨6,2,5,4⟩,⟨239,4,3,6⟩]⟩)
def qv252 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨252,[⟨111,3,4,3⟩,⟨154,6,5,4⟩,⟨144,2,5,4⟩,⟨63,1,5,3⟩,⟨155,1,5,4⟩]⟩)
def qv253 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨253,[⟨29,3,3,0⟩,⟨177,1,6,2⟩]⟩)
def qv254 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨254,[⟨96,7,4,5⟩,⟨108,0,8,5⟩]⟩)
def qv255 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨255,[⟨69,0,3,3⟩,⟨205,0,5,5⟩,⟨7,3,3,4⟩]⟩)
def qv256 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨256,[⟨0,5,4,5⟩,⟨231,0,3,4⟩]⟩)
def qv257 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨257,[⟨4,1,5,4⟩,⟨235,0,4,5⟩]⟩)
def qv258 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨258,[⟨6,4,3,4⟩,⟨227,0,4,5⟩]⟩)
def qv259 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨259,[⟨6,4,3,4⟩,⟨231,1,7,2⟩]⟩)
def qv260 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨260,[⟨0,5,4,6⟩,⟨231,0,3,5⟩]⟩)
def qv261 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨261,[⟨6,3,4,5⟩,⟨242,0,6,4⟩]⟩)
def qv262 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨262,[⟨0,7,5,7⟩,⟨213,0,3,4⟩]⟩)
def qv263 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨263,[⟨144,6,0,4⟩,⟨143,0,1,3⟩,⟨175,0,5,4⟩,⟨55,6,0,4⟩]⟩)
def qv264 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨264,[⟨6,4,3,4⟩,⟨250,1,7,4⟩]⟩)
def qv265 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨265,[⟨6,6,3,4⟩,⟨247,0,4,6⟩]⟩)
def qv266 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨266,[⟨6,3,3,5⟩,⟨242,0,5,4⟩]⟩)
def qv267 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨267,[⟨175,4,1,4⟩,⟨144,2,6,4⟩,⟨55,2,6,4⟩,⟨143,4,5,3⟩]⟩)
def qv268 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨268,[⟨6,0,5,4⟩,⟨251,0,4,2⟩]⟩)
def qv269 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨269,[⟨28,3,3,6⟩,⟨202,0,7,5⟩]⟩)
def qv270 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨270,[⟨63,0,3,7⟩,⟨6,7,3,2⟩]⟩)
def qv271 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨271,[⟨107,2,7,3⟩,⟨107,3,4,6⟩]⟩)
def qv272 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨272,[⟨1,1,3,1⟩,⟨249,0,4,5⟩]⟩)
def qv273 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨273,[⟨6,1,4,5⟩,⟨223,0,5,4⟩]⟩)
def qv274 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨274,[⟨6,7,3,1⟩,⟨240,0,5,5⟩]⟩)
def qv275 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨275,[⟨63,1,5,3⟩,⟨198,4,0,4⟩,⟨44,2,5,4⟩]⟩)
def qv276 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨276,[⟨7,3,3,4⟩,⟨177,0,5,4⟩,⟨63,0,3,5⟩]⟩)
def qv277 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨277,[⟨14,3,4,5⟩,⟨204,2,3,0⟩,⟨33,1,3,2⟩]⟩)
def qv278 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨278,[⟨63,3,3,3⟩,⟨162,1,8,4⟩]⟩)
def qv279 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨279,[⟨6,3,4,5⟩,⟨234,5,7,4⟩]⟩)
def qv280 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨280,[⟨184,0,1,5⟩,⟨116,2,4,3⟩]⟩)
def qv281 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨281,[⟨36,4,5,4⟩,⟨163,2,5,4⟩,⟨189,0,4,5⟩]⟩)
def qv282 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨282,[⟨56,0,5,4⟩,⟨64,0,1,3⟩,⟨55,0,5,4⟩,⟨265,0,1,3⟩]⟩)
def qv283 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨283,[⟨64,0,1,3⟩,⟨196,1,4,3⟩,⟨55,2,5,4⟩]⟩)
def qv284 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨284,[⟨45,1,4,5⟩,⟨224,0,5,4⟩,⟨46,3,4,5⟩]⟩)
def qv285 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨285,[⟨6,3,4,5⟩,⟨273,0,6,4⟩]⟩)
def qv286 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨286,[⟨6,7,3,0⟩,⟨261,0,3,4⟩]⟩)
def qv287 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨287,[⟨64,0,1,3⟩,⟨55,0,5,4⟩,⟨56,0,5,4⟩,⟨264,4,4,5⟩]⟩)
def qv288 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨288,[⟨130,1,4,2⟩,⟨96,0,1,4⟩]⟩)
def qv289 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨289,[⟨6,1,4,5⟩,⟨279,0,2,4⟩]⟩)
def qv290 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨290,[⟨67,2,5,2⟩,⟨231,4,5,5⟩]⟩)
def qv291 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨291,[⟨89,3,3,4⟩,⟨202,0,8,4⟩,⟨55,4,3,4⟩]⟩)
def qv292 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨292,[⟨39,0,3,4⟩,⟨219,3,3,4⟩,⟨79,1,4,3⟩]⟩)
def qv293 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨293,[⟨2,7,4,3⟩,⟨280,0,5,4⟩]⟩)
def qv294 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨294,[⟨63,1,5,3⟩,⟨196,3,1,3⟩]⟩)
def qv295 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨295,[⟨63,1,5,3⟩,⟨64,2,1,5⟩,⟨55,0,5,4⟩,⟨265,4,4,3⟩]⟩)
def qv296 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨296,[⟨107,1,4,5⟩,⟨209,3,3,4⟩,⟨65,1,4,5⟩]⟩)
def qv297 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨297,[⟨6,4,3,4⟩,⟨289,1,7,4⟩]⟩)
def qv298 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨298,[⟨24,2,7,3⟩,⟨24,6,3,3⟩,⟨107,4,3,4⟩,⟨195,0,7,4⟩]⟩)
def qv299 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨299,[⟨6,4,3,4⟩,⟨284,0,4,5⟩]⟩)
def qv300 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨300,[⟨64,3,5,1⟩,⟨240,2,5,1⟩,⟨55,3,4,5⟩]⟩)
def qv301 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨301,[⟨59,0,5,4⟩,⟨57,0,5,4⟩,⟨258,4,4,5⟩]⟩)
def qv302 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨302,[⟨125,0,5,3⟩,⟨162,4,3,6⟩]⟩)
def qv303 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨303,[⟨49,4,4,5⟩,⟨44,1,4,5⟩,⟨63,0,3,5⟩,⟨261,0,3,4⟩]⟩)
def qv304 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨304,[⟨55,4,3,4⟩,⟨202,0,8,4⟩,⟨131,3,3,4⟩]⟩)
def qv305 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨305,[⟨6,1,4,5⟩,⟨278,0,1,4⟩]⟩)
def qv306 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨306,[⟨4,1,4,3⟩,⟨288,0,6,4⟩]⟩)
def qv307 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨307,[⟨0,7,4,6⟩,⟨273,0,5,5⟩]⟩)
def qv308 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨308,[⟨6,6,3,4⟩,⟨299,0,4,6⟩]⟩)
def qv309 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨309,[⟨28,6,3,4⟩,⟨268,1,5,7⟩]⟩)
def qv310 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨310,[⟨6,1,4,5⟩,⟨281,0,5,3⟩]⟩)
def qv311 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨311,[⟨6,3,3,5⟩,⟨278,0,2,4⟩]⟩)
def qv312 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨312,[⟨9,2,5,4⟩,⟨272,0,4,5⟩]⟩)
def qv313 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨313,[⟨162,4,4,5⟩,⟨148,5,6,3⟩]⟩)
def qv314 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨314,[⟨6,3,4,5⟩,⟨305,0,6,4⟩]⟩)
def qv315 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨315,[⟨6,0,5,4⟩,⟨296,0,4,5⟩]⟩)
def qv316 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨316,[⟨6,6,3,4⟩,⟨306,0,5,8⟩]⟩)
def qv317 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨317,[⟨263,2,6,4⟩,⟨26,3,4,3⟩,⟨99,0,5,5⟩]⟩)
def qv318 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨318,[⟨64,3,5,1⟩,⟨63,0,3,5⟩,⟨261,0,3,4⟩,⟨55,1,4,5⟩]⟩)
def qv319 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨319,[⟨39,2,3,4⟩,⟨109,4,0,5⟩,⟨266,1,4,5⟩,⟨122,4,4,5⟩]⟩)
def qv320 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨320,[⟨19,1,4,3⟩,⟨267,2,6,4⟩,⟨115,7,4,3⟩]⟩)
def qv321 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨321,[⟨165,1,3,4⟩,⟨97,0,7,5⟩,⟨223,3,4,7⟩]⟩)
def qv322 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨322,[⟨96,0,1,4⟩,⟨205,1,5,2⟩]⟩)
def qv323 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨323,[⟨165,6,4,5⟩,⟨278,0,1,4⟩,⟨25,1,4,5⟩]⟩)
def qv324 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨324,[⟨6,3,4,5⟩,⟨298,0,3,4⟩]⟩)
def qv325 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨325,[⟨25,0,6,5⟩,⟨313,1,6,4⟩,⟨24,2,6,3⟩]⟩)
def qv326 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨326,[⟨63,1,5,3⟩,⟨255,7,0,4⟩]⟩)
def qv327 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨327,[⟨24,2,6,3⟩,⟨195,4,2,4⟩,⟨195,0,6,4⟩,⟨24,6,2,3⟩]⟩)
def qv328 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨328,[⟨49,0,4,5⟩,⟨44,3,4,5⟩,⟨285,0,3,4⟩]⟩)
def qv329 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨329,[⟨0,7,4,6⟩,⟨305,0,5,5⟩]⟩)
def qv330 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨330,[⟨63,1,5,3⟩,⟨268,0,4,5⟩,⟨144,0,5,4⟩,⟨154,4,5,4⟩,⟨155,5,5,4⟩]⟩)
def qv331 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨331,[⟨113,0,1,4⟩,⟨15,0,3,4⟩,⟨298,4,4,5⟩,⟨90,2,5,4⟩]⟩)
def qv332 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨332,[⟨67,4,3,4⟩,⟨289,2,5,1⟩]⟩)
def qv333 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨333,[⟨317,0,5,4⟩,⟨1,5,4,3⟩]⟩)
def qv334 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨334,[⟨67,6,3,2⟩,⟨289,0,5,5⟩]⟩)
def qv335 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨335,[⟨196,3,1,3⟩,⟨162,1,5,4⟩]⟩)
def qv336 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨336,[⟨25,6,2,3⟩,⟨199,3,2,4⟩,⟨65,0,6,4⟩,⟨304,0,2,4⟩]⟩)
def qv337 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨337,[⟨107,3,3,7⟩,⟨230,2,1,5⟩]⟩)
def qv338 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨338,[⟨241,0,6,4⟩,⟨275,4,2,4⟩,⟨107,4,2,4⟩]⟩)
def qv339 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨339,[⟨4,1,4,3⟩,⟨322,0,6,4⟩]⟩)
def qv340 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨340,[⟨25,3,3,6⟩,⟨300,4,4,6⟩,⟨24,3,3,6⟩]⟩)
def qv341 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨341,[⟨162,5,5,4⟩,⟨259,4,4,5⟩,⟨208,2,5,4⟩,⟨143,0,1,3⟩]⟩)
def qv342 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨342,[⟨210,0,5,2⟩,⟨88,1,4,3⟩,⟨260,4,4,3⟩,⟨290,0,4,3⟩]⟩)
def qv343 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨343,[⟨0,5,4,5⟩,⟨250,0,5,4⟩]⟩)
def qv344 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨344,[⟨7,1,5,4⟩,⟨108,3,4,5⟩,⟨262,4,5,2⟩]⟩)
def qv345 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨345,[⟨6,0,5,5⟩,⟨320,4,4,7⟩]⟩)
def qv346 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨346,[⟨60,1,4,3⟩,⟨255,0,1,4⟩,⟨276,0,1,4⟩]⟩)
def qv347 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨347,[⟨6,6,3,4⟩,⟨339,0,5,8⟩]⟩)
def qv348 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨348,[⟨312,1,5,5⟩,⟨114,4,3,4⟩,⟨139,3,4,5⟩]⟩)
def qv349 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨349,[⟨14,1,4,5⟩,⟨17,1,4,5⟩,⟨332,0,3,4⟩]⟩)
def qv350 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨350,[⟨24,4,2,5⟩,⟨107,2,6,4⟩,⟨271,4,5,5⟩,⟨215,0,5,5⟩]⟩)
def qv351 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨351,[⟨163,0,5,4⟩,⟨287,4,1,4⟩,⟨25,4,1,5⟩]⟩)
def qv352 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨352,[⟨214,0,4,5⟩,⟨91,0,3,4⟩,⟨63,0,3,5⟩,⟨344,0,4,5⟩,⟨180,4,4,5⟩]⟩)
def qv353 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨353,[⟨6,4,0,5⟩,⟨347,0,1,3⟩]⟩)
def qv354 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨354,[⟨138,2,5,4⟩,⟨114,5,4,3⟩,⟨312,0,5,5⟩,⟨182,2,2,4⟩]⟩)
def qv355 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨355,[⟨12,2,7,3⟩,⟨167,0,7,4⟩,⟨342,0,6,6⟩]⟩)
def qv356 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨356,[⟨24,2,6,3⟩,⟨24,6,2,3⟩,⟨211,4,2,4⟩,⟨179,0,6,4⟩]⟩)
def qv357 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨357,[⟨82,6,2,3⟩,⟨283,0,5,6⟩]⟩)
def qv358 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨358,[⟨6,0,5,4⟩,⟨346,0,4,6⟩]⟩)
def qv359 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨359,[⟨134,0,4,6⟩,⟨24,7,3,2⟩,⟨323,0,5,5⟩]⟩)
def qv360 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨360,[⟨155,4,4,5⟩,⟨7,3,3,4⟩,⟨337,0,5,2⟩,⟨228,4,5,2⟩]⟩)
def qv361 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨361,[⟨6,4,3,4⟩,⟨352,0,4,5⟩]⟩)
def qv362 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨362,[⟨4,0,3,4⟩,⟨345,0,4,3⟩]⟩)
def qv363 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨363,[⟨137,1,4,2⟩,⟨248,0,2,4⟩]⟩)
def qv364 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨364,[⟨63,0,3,5⟩,⟨314,2,3,1⟩]⟩)
def qv365 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨365,[⟨6,1,4,5⟩,⟨354,0,4,3⟩]⟩)
def qv366 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨366,[⟨6,3,4,5⟩,⟨357,0,6,2⟩]⟩)
def qv367 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨367,[⟨6,2,5,4⟩,⟨361,4,4,6⟩]⟩)
def qv368 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨368,[⟨6,1,4,5⟩,⟨366,0,2,4⟩]⟩)
def qv369 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨369,[⟨6,0,5,4⟩,⟨367,4,1,2⟩]⟩)
def qv370 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨370,[⟨199,3,1,4⟩,⟨286,1,5,4⟩,⟨24,6,1,3⟩,⟨319,0,5,3⟩]⟩)
def qv371 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨371,[⟨267,6,2,4⟩,⟨137,1,4,2⟩]⟩)
def qv372 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨372,[⟨40,1,4,3⟩,⟨333,0,2,4⟩,⟨120,1,3,3⟩,⟨161,0,4,2⟩]⟩)
def qv373 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨373,[⟨156,2,7,4⟩,⟨226,4,3,5⟩,⟨80,0,5,4⟩,⟨327,0,5,5⟩,⟨156,6,3,4⟩]⟩)
def qv374 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨374,[⟨65,4,3,4⟩,⟨335,0,7,4⟩,⟨24,2,7,3⟩,⟨163,4,3,4⟩]⟩)
def qv375 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨375,[⟨24,3,3,6⟩,⟨327,6,3,3⟩]⟩)
def qv376 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨376,[⟨162,1,5,4⟩,⟨285,3,1,3⟩]⟩)
def qv377 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨377,[⟨29,3,3,0⟩,⟨362,0,7,2⟩]⟩)
def qv378 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨378,[⟨295,0,5,4⟩,⟨176,4,1,4⟩,⟨183,4,1,4⟩,⟨172,6,1,4⟩,⟨294,4,1,4⟩]⟩)
def qv379 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨379,[⟨63,0,3,5⟩,⟨64,1,3,1⟩,⟨55,3,4,5⟩,⟨368,0,5,4⟩]⟩)
def qv380 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨380,[⟨101,4,2,5⟩,⟨271,0,2,5⟩,⟨223,0,5,4⟩,⟨192,3,1,4⟩]⟩)
def qv381 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨381,[⟨211,6,3,4⟩,⟨24,0,7,5⟩,⟨163,4,3,4⟩,⟨341,0,7,4⟩]⟩)
def qv382 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨382,[⟨124,1,5,3⟩,⟨2,7,4,3⟩]⟩)
def qv383 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨383,[⟨192,3,2,4⟩,⟨271,0,3,5⟩,⟨197,0,6,4⟩,⟨172,0,6,4⟩,⟨215,4,3,5⟩]⟩)
def qv384 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨384,[⟨173,2,6,4⟩,⟨282,4,2,4⟩,⟨220,2,6,4⟩,⟨246,2,6,4⟩,⟨263,2,6,4⟩,⟨183,6,2,4⟩,⟨295,0,6,4⟩]⟩)
def qv385 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨385,[⟨63,1,5,3⟩,⟨64,2,1,5⟩,⟨55,0,5,4⟩,⟨369,4,1,5⟩]⟩)
def qv386 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨386,[⟨217,4,1,4⟩,⟨172,0,5,4⟩,⟨173,4,1,4⟩,⟨217,0,5,4⟩,⟨294,0,5,4⟩,⟨294,4,1,4⟩]⟩)
def qv387 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨387,[⟨14,1,4,6⟩,⟨370,0,5,4⟩]⟩)
def qv388 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨388,[⟨6,3,4,5⟩,⟨374,0,3,4⟩]⟩)
def qv389 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨389,[⟨197,5,4,1⟩,⟨215,7,3,2⟩,⟨271,3,3,2⟩,⟨236,0,5,5⟩,⟨192,6,4,1⟩]⟩)
def qv390 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨390,[⟨372,2,5,0⟩,⟨167,5,4,1⟩,⟨12,7,3,1⟩]⟩)
def qv391 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨391,[⟨6,5,5,1⟩,⟨388,0,3,5⟩]⟩)
def qv392 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨392,[⟨24,7,3,1⟩,⟨107,1,4,5⟩,⟨236,0,5,5⟩,⟨364,2,4,1⟩]⟩)
def qv393 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨393,[⟨107,3,4,5⟩,⟨348,0,6,3⟩,⟨65,3,4,5⟩,⟨303,0,4,5⟩]⟩)
def qv394 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨394,[⟨226,4,1,4⟩,⟨226,0,5,4⟩,⟨327,4,3,4⟩,⟨327,6,3,3⟩,⟨226,6,1,3⟩,⟨226,2,5,3⟩]⟩)
def qv395 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨395,[⟨211,4,2,4⟩,⟨376,0,6,4⟩,⟨24,2,6,3⟩,⟨236,3,2,5⟩]⟩)
def qv396 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨396,[⟨107,3,4,5⟩,⟨365,1,7,3⟩,⟨303,0,4,5⟩,⟨65,3,4,5⟩]⟩)
def qv397 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨397,[⟨24,3,4,5⟩,⟨374,0,3,4⟩,⟨65,5,5,1⟩]⟩)
def qv398 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨398,[⟨257,0,1,3⟩,⟨363,0,5,4⟩,⟨130,1,4,2⟩,⟨177,1,4,2⟩]⟩)
def qv399 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨399,[⟨192,6,4,1⟩,⟨271,3,3,2⟩,⟨173,1,4,5⟩,⟨319,1,3,5⟩,⟨215,7,3,2⟩]⟩)
def qv400 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨400,[⟨283,4,2,4⟩,⟨252,4,2,4⟩,⟨176,4,2,4⟩,⟨197,0,6,4⟩,⟨283,0,6,4⟩,⟨245,4,2,4⟩]⟩)
def qv401 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨401,[⟨24,7,3,2⟩,⟨286,0,4,6⟩,⟨364,2,4,2⟩,⟨319,1,3,6⟩]⟩)
def qv402 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨402,[⟨29,3,3,0⟩,⟨384,0,5,4⟩]⟩)
def qv403 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨403,[⟨202,1,4,5⟩,⟨180,0,4,5⟩,⟨314,4,5,4⟩,⟨63,0,3,5⟩,⟨388,0,3,4⟩]⟩)
def qv404 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨404,[⟨82,6,2,3⟩,⟨388,4,4,6⟩]⟩)
def qv405 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨405,[⟨391,0,4,3⟩,⟨301,0,5,2⟩,⟨42,1,4,3⟩]⟩)
def qv406 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨406,[⟨295,1,4,5⟩,⟨172,7,4,1⟩,⟨245,3,4,5⟩,⟨197,5,4,1⟩,⟨236,0,5,5⟩,⟨176,3,4,5⟩,⟨364,2,4,1⟩]⟩)
def qv407 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨407,[⟨285,0,3,7⟩,⟨314,6,5,4⟩]⟩)
def qv408 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨408,[⟨357,0,5,2⟩,⟨229,7,2,4⟩,⟨223,4,2,4⟩,⟨223,0,6,4⟩]⟩)
def qv409 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨409,[⟨136,6,4,3⟩,⟨384,0,5,4⟩,⟨133,4,4,3⟩,⟨110,3,4,3⟩]⟩)
def qv410 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨410,[⟨0,4,5,4⟩,⟨405,0,3,7⟩]⟩)
def qv411 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨411,[⟨252,0,7,4⟩,⟨263,0,7,4⟩,⟨300,3,3,4⟩,⟨379,1,7,4⟩,⟨173,0,7,4⟩,⟨246,0,7,4⟩]⟩)
def qv412 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨412,[⟨0,0,0,3⟩,⟨403,4,3,6⟩]⟩)
def qv413 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨413,[⟨3,7,4,3⟩,⟨403,0,4,7⟩]⟩)
def qv414 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨414,[⟨374,0,2,5⟩,⟨199,2,4,2⟩,⟨185,2,4,2⟩]⟩)
def qv415 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨415,[⟨177,1,4,2⟩,⟨164,1,4,2⟩,⟨205,1,5,2⟩,⟨384,0,3,4⟩,⟨371,0,5,4⟩]⟩)
def qv416 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨416,[⟨176,2,5,4⟩,⟨385,4,1,4⟩,⟨197,4,1,4⟩,⟨295,0,5,4⟩,⟨245,2,5,4⟩,⟨220,2,5,4⟩]⟩)
def qv417 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨417,[⟨409,0,2,4⟩,⟨11,1,4,2⟩,⟨270,4,4,2⟩]⟩)
def qv418 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨418,[⟨68,4,1,3⟩,⟨62,6,1,3⟩,⟨147,6,1,3⟩,⟨413,0,4,2⟩]⟩)
def qv419 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨419,[⟨243,0,4,2⟩,⟨164,1,4,2⟩,⟨402,0,2,4⟩,⟨253,0,2,4⟩,⟨377,0,2,4⟩]⟩)
def qv420 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨420,[⟨29,3,3,0⟩,⟨415,0,6,4⟩]⟩)
def qv421 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨421,[⟨24,6,2,3⟩,⟨397,1,5,3⟩,⟨25,6,2,3⟩,⟨241,4,2,4⟩]⟩)
def qv422 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨422,[⟨45,1,3,7⟩,⟨106,6,2,3⟩,⟨419,1,6,6⟩]⟩)
def qv423 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨423,[⟨378,4,2,4⟩,⟨386,0,5,4⟩,⟨226,3,3,5⟩,⟨386,4,2,4⟩,⟨378,0,5,4⟩]⟩)
def qv424 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨424,[⟨55,1,4,5⟩,⟨394,0,6,4⟩,⟨216,3,4,5⟩]⟩)
def qv425 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨425,[⟨386,0,5,4⟩,⟨226,1,4,5⟩,⟨378,4,2,4⟩,⟨378,0,5,4⟩,⟨386,4,2,4⟩]⟩)
def qv426 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨426,[⟨300,6,4,1⟩,⟨252,1,4,5⟩,⟨397,0,3,4⟩,⟨291,1,4,1⟩,⟨328,0,4,5⟩,⟨319,1,3,5⟩]⟩)
def qv427 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨427,[⟨45,1,3,7⟩,⟨106,6,2,3⟩,⟨420,1,6,4⟩]⟩)
def qv428 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨428,[⟨26,3,4,3⟩,⟨416,0,5,4⟩,⟨244,0,5,4⟩,⟨329,0,4,3⟩]⟩)
def qv429 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨429,[⟨128,0,6,3⟩,⟨28,3,4,5⟩]⟩)
def qv430 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨430,[⟨277,7,1,3⟩,⟨338,4,3,4⟩,⟨336,1,4,3⟩,⟨375,2,4,3⟩,⟨277,6,3,1⟩]⟩)
def qv431 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨431,[⟨73,4,3,3⟩,⟨302,1,5,2⟩,⟨415,0,6,4⟩,⟨398,0,6,4⟩]⟩)
def qv432 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨432,[⟨42,3,4,3⟩,⟨428,0,5,4⟩,⟨274,0,4,3⟩]⟩)
def qv433 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨433,[⟨63,0,3,5⟩,⟨7,3,3,4⟩,⟨427,0,5,2⟩,⟨422,0,5,2⟩]⟩)
def qv434 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨434,[⟨418,0,4,5⟩,⟨263,2,5,4⟩,⟨295,0,5,4⟩,⟨176,2,5,4⟩,⟨116,0,4,3⟩]⟩)
def qv435 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨435,[⟨6,4,3,4⟩,⟨431,0,5,6⟩]⟩)
def qv436 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨436,[⟨51,1,5,4⟩,⟨60,3,4,3⟩,⟨274,4,4,3⟩,⟨428,0,5,4⟩]⟩)
def qv437 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨437,[⟨55,7,4,0⟩,⟨427,0,5,2⟩,⟨63,0,3,5⟩,⟨422,0,5,2⟩]⟩)
def qv438 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨438,[⟨0,0,1,3⟩,⟨432,0,4,6⟩]⟩)
def qv439 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨439,[⟨176,2,5,4⟩,⟨295,0,5,4⟩,⟨263,2,5,4⟩,⟨418,0,4,5⟩,⟨149,0,4,3⟩]⟩)
def qv440 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨440,[⟨6,6,1,3⟩,⟨435,0,2,5⟩]⟩)
def qv441 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨441,[⟨6,6,3,4⟩,⟨435,0,4,6⟩]⟩)
def qv442 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨442,[⟨63,0,3,5⟩,⟨7,1,5,4⟩,⟨433,0,4,5⟩,⟨201,0,3,2⟩]⟩)
def qv443 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨443,[⟨6,0,5,4⟩,⟨438,0,3,4⟩]⟩)
def qv444 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨444,[⟨194,0,5,3⟩,⟨160,3,4,1⟩,⟨142,7,4,1⟩,⟨236,0,5,5⟩,⟨353,4,1,2⟩,⟨412,0,5,3⟩]⟩)
def qv445 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨445,[⟨9,4,3,4⟩,⟨432,0,5,7⟩]⟩)
def qv446 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨446,[⟨4,6,4,3⟩,⟨438,0,6,5⟩]⟩)
def qv447 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨447,[⟨0,0,0,3⟩,⟨436,4,4,6⟩]⟩)
def qv448 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨448,[⟨9,4,1,3⟩,⟨436,0,3,6⟩]⟩)
def qv449 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨449,[⟨26,3,4,3⟩,⟨244,0,5,4⟩,⟨439,0,5,4⟩,⟨307,0,4,3⟩]⟩)
def qv450 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨450,[⟨6,1,5,5⟩,⟨440,0,6,4⟩]⟩)
def qv451 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨451,[⟨1,5,4,3⟩,⟨449,0,5,4⟩]⟩)
def qv452 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨452,[⟨24,1,5,7⟩,⟨451,0,3,8⟩,⟨25,3,3,7⟩]⟩)
def qv453 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨453,[⟨359,0,4,3⟩,⟨226,7,3,1⟩,⟨386,4,2,4⟩,⟨389,1,5,4⟩,⟨414,4,3,3⟩]⟩)
def qv454 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨454,[⟨58,0,6,3⟩,⟨436,0,3,6⟩]⟩)
def qv455 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨455,[⟨20,2,4,5⟩,⟨118,3,0,5⟩,⟨39,2,3,4⟩]⟩)
def qv456 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨456,[⟨308,4,4,3⟩,⟨64,2,1,5⟩,⟨63,1,5,3⟩,⟨55,0,5,4⟩]⟩)
def qv457 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨457,[⟨28,7,3,2⟩,⟨454,0,5,4⟩]⟩)
def qv458 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨458,[⟨130,1,4,2⟩,⟨177,1,4,2⟩,⟨450,0,1,4⟩]⟩)
def qv459 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨459,[⟨97,2,7,3⟩,⟨448,0,5,4⟩,⟨65,2,7,3⟩]⟩)
def qv460 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨460,[⟨183,6,1,4⟩,⟨173,2,5,4⟩,⟨295,0,5,4⟩,⟨282,4,1,4⟩,⟨246,2,5,4⟩,⟨263,2,5,4⟩,⟨220,2,5,4⟩]⟩)
def qv461 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨461,[⟨4,1,4,3⟩,⟨458,0,6,4⟩]⟩)
def qv462 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨462,[⟨452,0,3,2⟩,⟨86,0,5,4⟩,⟨328,1,5,4⟩]⟩)
def qv463 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨463,[⟨170,0,6,3⟩,⟨76,1,3,2⟩,⟨447,0,5,4⟩]⟩)
def qv464 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨464,[⟨63,0,3,5⟩,⟨224,0,5,4⟩,⟨315,0,7,3⟩,⟨306,0,5,5⟩,⟨358,0,7,3⟩,⟨461,0,5,5⟩]⟩)
def qv465 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨465,[⟨55,3,4,5⟩,⟨285,0,3,4⟩,⟨64,1,3,1⟩]⟩)
def qv466 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨466,[⟨395,4,3,4⟩,⟨360,4,2,6⟩,⟨417,1,5,4⟩,⟨325,4,3,4⟩,⟨324,4,3,5⟩]⟩)
def qv467 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨467,[⟨64,7,5,7⟩,⟨314,6,5,4⟩,⟨443,1,5,7⟩]⟩)
def qv468 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨468,[⟨6,6,3,4⟩,⟨464,0,4,7⟩]⟩)
def qv469 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨469,[⟨55,5,4,3⟩,⟨443,1,5,7⟩,⟨314,6,5,4⟩]⟩)
def qv470 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨470,[⟨6,4,3,4⟩,⟨468,0,4,2⟩]⟩)
def qv471 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨471,[⟨6,5,4,3⟩,⟨466,0,5,6⟩]⟩)
def qv472 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨472,[⟨6,5,5,0⟩,⟨466,0,6,3⟩]⟩)
def qv473 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨473,[⟨121,5,5,4⟩,⟨436,0,3,7⟩,⟨445,4,5,4⟩]⟩)
def qv474 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨474,[⟨463,0,6,5⟩,⟨70,0,3,5⟩,⟨83,1,5,3⟩]⟩)
def qv475 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨475,[⟨63,1,5,3⟩,⟨261,1,4,3⟩,⟨457,0,2,5⟩,⟨269,2,2,5⟩]⟩)
def qv476 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨476,[⟨0,0,1,3⟩,⟨473,0,5,3⟩]⟩)
def qv477 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨477,[⟨55,1,4,5⟩,⟨154,7,4,5⟩,⟨154,3,4,0⟩,⟨471,2,5,4⟩]⟩)
def qv478 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨478,[⟨25,3,4,5⟩,⟨165,2,4,5⟩,⟨190,0,7,4⟩]⟩)
def qv479 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨479,[⟨55,0,5,4⟩,⟨443,0,4,5⟩,⟨443,4,1,5⟩]⟩)
def qv480 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨480,[⟨108,1,4,5⟩,⟨4,1,5,4⟩]⟩)
def qv481 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨481,[⟨303,1,5,4⟩,⟨429,2,1,4⟩,⟨309,1,1,4⟩,⟨206,2,1,4⟩,⟨169,2,1,4⟩,⟨207,2,1,4⟩]⟩)
def qv482 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨482,[⟨6,1,4,5⟩,⟨218,2,4,3⟩]⟩)
def qv483 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨483,[⟨173,1,4,5⟩,⟨292,7,3,1⟩,⟨319,1,3,5⟩,⟨192,6,4,1⟩,⟨475,1,4,5⟩]⟩)
def qv484 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨484,[⟨25,4,1,5⟩,⟨107,2,5,4⟩,⟨349,3,1,5⟩,⟨163,2,5,4⟩]⟩)
def qv485 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨485,[⟨484,0,5,4⟩,⟨2,3,4,3⟩]⟩)
def qv486 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨486,[⟨2,5,4,2⟩,⟨485,0,5,3⟩]⟩)
def qv487 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨487,[⟨2,3,4,3⟩,⟨481,0,5,4⟩]⟩)
def qv488 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨488,[⟨0,6,6,4⟩,⟨247,0,2,5⟩]⟩)
def qv489 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨489,[⟨356,1,3,3⟩,⟨197,4,1,4⟩,⟨172,6,1,4⟩]⟩)
def qv490 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨490,[⟨64,1,3,1⟩,⟨471,0,5,1⟩,⟨470,1,5,1⟩,⟨111,0,3,1⟩]⟩)
def qv491 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨491,[⟨6,3,3,5⟩,⟨273,0,5,4⟩]⟩)
def qv492 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨492,[⟨62,4,3,4⟩,⟨107,4,3,4⟩,⟨487,0,6,6⟩]⟩)
def qv493 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨493,[⟨225,0,1,4⟩,⟨455,0,5,3⟩,⟨236,1,5,5⟩,⟨221,0,5,4⟩]⟩)
def qv494 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨494,[⟨297,4,4,5⟩,⟨268,4,1,5⟩,⟨162,5,5,4⟩]⟩)
def qv495 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨495,[⟨25,6,1,3⟩,⟨167,4,1,4⟩,⟨456,4,1,4⟩]⟩)
def qv496 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨496,[⟨25,0,7,5⟩,⟨107,6,3,4⟩,⟨163,6,3,4⟩,⟨494,0,7,4⟩]⟩)
def qv497 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨497,[⟨36,2,3,4⟩,⟨167,0,7,4⟩,⟨410,0,7,3⟩]⟩)
def qv498 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨498,[⟨14,1,4,6⟩,⟨298,2,2,4⟩]⟩)
def qv499 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨499,[⟨493,0,5,4⟩,⟨25,1,4,5⟩,⟨478,0,2,4⟩]⟩)
def qv500 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨500,[⟨1,5,3,6⟩,⟨351,0,5,4⟩]⟩)
def qv501 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨501,[⟨6,4,0,5⟩,⟨316,0,1,3⟩]⟩)
def qv502 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨502,[⟨215,6,2,3⟩,⟨232,0,4,3⟩,⟨192,7,1,4⟩,⟨173,0,5,4⟩,⟨271,2,2,3⟩]⟩)
def qv503 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨503,[⟨63,0,3,5⟩,⟨55,7,4,0⟩,⟨420,1,7,2⟩,⟨419,1,7,4⟩]⟩)
def qv504 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨504,[⟨381,0,3,4⟩,⟨310,4,4,5⟩,⟨159,0,5,6⟩,⟨351,4,3,4⟩,⟨496,0,3,4⟩]⟩)
def qv505 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨505,[⟨173,1,4,5⟩,⟨499,0,5,4⟩,⟨183,1,4,5⟩,⟨282,1,4,5⟩]⟩)
def qv506 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨506,[⟨99,0,4,5⟩,⟨200,7,1,4⟩,⟨318,5,5,4⟩,⟨173,0,5,4⟩]⟩)
def qv507 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨507,[⟨151,0,2,4⟩,⟨33,3,4,3⟩,⟨481,0,5,4⟩]⟩)
def qv508 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨508,[⟨6,0,5,4⟩,⟨393,0,1,5⟩]⟩)
def qv509 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨509,[⟨252,0,6,4⟩,⟨241,4,2,4⟩,⟨455,0,6,3⟩,⟨68,2,6,4⟩]⟩)
def qv510 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨510,[⟨6,4,3,4⟩,⟨508,0,7,4⟩]⟩)
def qv511 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨511,[⟨15,1,4,5⟩,⟨331,0,5,3⟩,⟨380,4,2,4⟩]⟩)
def qv512 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨512,[⟨62,0,5,4⟩,⟨107,0,5,4⟩,⟨507,0,4,6⟩]⟩)
def qv513 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨513,[⟨6,4,3,4⟩,⟨396,0,4,5⟩]⟩)
def qv514 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨514,[⟨57,0,5,4⟩,⟨443,4,1,5⟩,⟨510,0,1,5⟩]⟩)
def qv515 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨515,[⟨2,6,2,4⟩,⟨512,1,1,5⟩]⟩)
def qv516 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨516,[⟨329,0,4,3⟩,⟨244,4,2,4⟩,⟨10,1,4,5⟩,⟨506,4,2,4⟩]⟩)
def qv517 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨517,[⟨496,0,2,3⟩,⟨140,0,4,2⟩,⟨193,1,4,2⟩]⟩)
def qv518 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨518,[⟨9,6,3,4⟩,⟨514,0,7,4⟩]⟩)
def qv519 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨519,[⟨498,0,4,3⟩,⟨311,4,3,4⟩,⟨38,1,4,5⟩,⟨408,0,3,4⟩]⟩)
def qv520 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨520,[⟨254,0,2,3⟩,⟨200,5,6,4⟩,⟨271,6,5,3⟩,⟨215,2,5,3⟩,⟨252,4,2,4⟩]⟩)
def qv521 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨521,[⟨492,4,5,1⟩,⟨2,7,4,2⟩]⟩)
def qv522 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨522,[⟨176,3,4,6⟩,⟨338,2,3,3⟩,⟨252,1,4,6⟩]⟩)
def qv523 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨523,[⟨303,1,5,4⟩,⟨25,4,1,5⟩,⟨107,2,5,4⟩,⟨511,4,1,6⟩]⟩)
def qv524 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨524,[⟨504,4,5,3⟩,⟨504,0,3,3⟩,⟨180,0,4,5⟩,⟨180,4,4,5⟩,⟨261,0,3,4⟩]⟩)
def qv525 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨525,[⟨303,1,5,4⟩,⟨25,4,1,5⟩,⟨430,0,4,6⟩,⟨107,2,5,4⟩]⟩)
def qv526 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨526,[⟨359,0,4,3⟩,⟨416,4,2,4⟩,⟨327,5,4,3⟩,⟨489,0,5,4⟩,⟨399,3,2,4⟩]⟩)
def qv527 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨527,[⟨387,4,4,3⟩,⟨38,3,4,5⟩,⟨491,0,5,4⟩,⟨519,0,6,4⟩]⟩)
def qv528 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨528,[⟨414,1,3,5⟩,⟨386,1,4,6⟩,⟨502,5,4,3⟩,⟨226,4,1,5⟩,⟨359,5,3,4⟩]⟩)
def qv529 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨529,[⟨55,4,3,4⟩,⟨441,0,4,3⟩,⟨63,3,3,3⟩,⟨64,6,7,5⟩]⟩)
def qv530 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨530,[⟨456,7,4,2⟩,⟨336,0,5,5⟩,⟨283,7,4,2⟩,⟨271,5,5,5⟩]⟩)
def qv531 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨531,[⟨425,0,5,4⟩,⟨336,3,4,3⟩,⟨340,6,4,3⟩,⟨394,1,5,4⟩,⟨423,0,5,4⟩,⟨526,0,5,4⟩,⟨401,4,4,3⟩,⟨453,0,5,4⟩]⟩)
def qv532 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨532,[⟨504,4,5,3⟩,⟨6,7,3,0⟩]⟩)
def qv533 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨533,[⟨318,4,4,5⟩,⟨319,7,5,1⟩,⟨407,4,4,1⟩,⟨173,3,4,5⟩,⟨217,1,4,5⟩]⟩)
def qv534 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨534,[⟨434,0,4,6⟩,⟨12,6,1,3⟩]⟩)
def qv535 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨535,[⟨444,0,4,5⟩,⟨426,0,4,5⟩,⟨25,0,5,4⟩,⟨321,4,4,2⟩]⟩)
def qv536 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨536,[⟨307,0,4,3⟩,⟨244,0,5,4⟩,⟨26,3,4,3⟩,⟨534,0,5,2⟩]⟩)
def qv537 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨537,[⟨373,2,2,4⟩,⟨271,3,3,3⟩,⟨176,1,4,6⟩,⟨330,1,4,6⟩]⟩)
def qv538 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨538,[⟨63,3,3,3⟩,⟨470,0,4,5⟩,⟨64,6,7,5⟩,⟨55,4,3,4⟩]⟩)
def qv539 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨539,[⟨51,1,5,4⟩,⟨488,3,4,3⟩,⟨428,0,5,4⟩,⟨516,0,5,4⟩]⟩)
def qv540 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨540,[⟨334,0,4,3⟩,⟨51,1,5,4⟩,⟨88,3,4,3⟩,⟨536,0,5,4⟩]⟩)
def qv541 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨541,[⟨236,0,5,5⟩,⟨142,7,4,1⟩,⟨160,3,4,1⟩,⟨194,0,5,3⟩,⟨501,4,1,2⟩,⟨412,0,5,3⟩]⟩)
def qv542 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨542,[⟨6,5,5,0⟩,⟨442,0,4,5⟩]⟩)
def qv543 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨543,[⟨493,3,2,6⟩,⟨107,2,5,4⟩,⟨318,5,5,4⟩]⟩)
def qv544 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨544,[⟨263,2,7,4⟩,⟨9,6,3,4⟩,⟨451,1,8,3⟩]⟩)
def qv545 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨545,[⟨256,0,4,5⟩,⟨448,0,5,4⟩,⟨153,0,6,3⟩,⟨343,0,4,5⟩]⟩)
def qv546 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨546,[⟨64,0,4,3⟩,⟨482,7,4,3⟩,⟨443,0,7,5⟩,⟨64,6,7,5⟩]⟩)
def qv547 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨547,[⟨443,0,7,5⟩,⟨510,4,7,5⟩,⟨131,3,3,4⟩]⟩)
def qv548 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨548,[⟨426,0,4,5⟩,⟨541,0,4,5⟩,⟨25,0,5,4⟩,⟨321,4,4,2⟩]⟩)
def qv549 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨549,[⟨385,0,6,4⟩,⟨385,4,2,4⟩,⟨330,0,6,4⟩,⟨252,6,2,4⟩,⟨326,0,6,4⟩,⟨529,0,2,4⟩]⟩)
def qv550 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨550,[⟨424,0,4,6⟩,⟨172,7,4,2⟩,⟨215,1,5,5⟩,⟨456,7,4,2⟩]⟩)
def qv551 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨551,[⟨300,6,4,3⟩,⟨172,7,4,3⟩,⟨319,3,5,7⟩,⟨527,4,5,7⟩,⟨176,5,4,3⟩]⟩)
def qv552 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨552,[⟨443,4,1,5⟩,⟨64,2,1,5⟩,⟨504,1,3,3⟩,⟨404,5,2,3⟩]⟩)
def qv553 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨553,[⟨63,0,3,5⟩,⟨261,4,5,4⟩,⟨471,0,5,1⟩,⟨442,0,4,5⟩,⟨504,0,3,3⟩,⟨180,0,4,5⟩]⟩)
def qv554 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨554,[⟨30,6,5,4⟩,⟨96,7,4,5⟩,⟨474,0,4,5⟩]⟩)
def qv555 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨555,[⟨504,5,3,5⟩,⟨513,0,1,5⟩,⟨55,0,5,4⟩,⟨443,4,1,5⟩,⟨471,1,1,5⟩]⟩)
def qv556 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨556,[⟨34,1,4,2⟩,⟨549,0,3,4⟩]⟩)
def qv557 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨557,[⟨460,0,5,4⟩,⟨460,4,2,4⟩,⟨460,2,5,4⟩,⟨411,4,5,4⟩,⟨531,0,3,6⟩,⟨531,4,4,6⟩,⟨406,5,5,4⟩]⟩)
def qv558 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨558,[⟨180,5,5,4⟩,⟨443,4,1,5⟩,⟨513,0,1,5⟩,⟨442,1,5,4⟩]⟩)
def qv559 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨559,[⟨228,4,5,2⟩,⟨7,3,3,4⟩,⟨155,4,4,5⟩,⟨538,5,4,5⟩]⟩)
def qv560 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨560,[⟨517,5,5,4⟩,⟨416,5,4,3⟩,⟨359,5,3,4⟩,⟨356,6,3,4⟩,⟨483,0,4,6⟩]⟩)
def qv561 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨561,[⟨295,0,5,4⟩,⟨173,2,5,4⟩,⟨263,6,1,4⟩,⟨236,1,5,5⟩,⟨546,4,5,4⟩,⟨176,2,5,4⟩,⟨535,0,4,5⟩]⟩)
def qv562 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨562,[⟨6,7,3,0⟩,⟨559,0,4,5⟩]⟩)
def qv563 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨563,[⟨167,0,7,4⟩,⟨538,0,3,4⟩,⟨514,0,7,4⟩,⟨330,4,3,4⟩,⟨545,0,5,5⟩]⟩)
def qv564 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨564,[⟨560,0,4,3⟩,⟨421,0,3,4⟩,⟨401,1,3,4⟩,⟨340,3,3,4⟩,⟨509,0,3,4⟩,⟨528,0,4,3⟩,⟨423,5,4,3⟩,⟨425,5,4,3⟩,⟨336,0,3,4⟩]⟩)
def qv565 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨565,[⟨443,4,4,5⟩,⟨131,3,3,4⟩,⟨538,0,3,4⟩,⟨459,0,5,5⟩,⟨144,4,3,4⟩]⟩)
def qv566 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨566,[⟨314,0,3,4⟩,⟨180,0,4,5⟩,⟨442,0,4,5⟩,⟨466,0,6,3⟩,⟨504,0,3,3⟩]⟩)
def qv567 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨567,[⟨21,1,4,3⟩,⟨561,0,6,4⟩,⟨500,4,3,1⟩]⟩)
def qv568 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨568,[⟨538,4,6,4⟩,⟨547,0,2,4⟩,⟨275,0,6,4⟩,⟨565,0,2,4⟩,⟨330,0,6,4⟩]⟩)
def qv569 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨569,[⟨34,3,4,2⟩,⟨568,4,5,4⟩]⟩)
def qv570 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨570,[⟨569,0,2,5⟩,⟨2,7,4,3⟩]⟩)
def qv571 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨571,[⟨293,0,4,3⟩,⟨570,0,4,3⟩,⟨382,0,4,3⟩,⟨556,4,2,4⟩]⟩)
def qv572 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨572,[⟨564,1,6,6⟩,⟨465,3,3,4⟩,⟨385,4,3,4⟩,⟨364,7,3,4⟩,⟨499,1,6,5⟩]⟩)
def qv573 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨573,[⟨527,2,3,1⟩,⟨499,4,3,4⟩,⟨527,6,5,1⟩,⟨499,0,5,4⟩,⟨407,4,4,1⟩,⟨531,7,2,4⟩,⟨407,0,4,1⟩]⟩)
def qv574 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨574,[⟨497,0,2,4⟩,⟨539,4,4,6⟩,⟨355,0,2,4⟩,⟨390,3,2,4⟩,⟨544,0,2,4⟩,⟨462,1,4,5⟩,⟨563,4,5,4⟩,⟨540,4,4,6⟩,⟨518,0,2,4⟩,⟨495,4,2,4⟩]⟩)
def qv575 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨575,[⟨314,4,5,4⟩,⟨504,4,5,3⟩,⟨180,4,4,5⟩,⟨442,4,4,5⟩,⟨559,0,4,5⟩]⟩)
def qv576 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨576,[⟨495,0,5,4⟩,⟨544,4,5,4⟩,⟨462,3,3,5⟩,⟨540,0,3,6⟩,⟨355,4,5,4⟩,⟨539,0,3,6⟩,⟨497,4,5,4⟩,⟨390,1,5,4⟩,⟨563,0,2,4⟩,⟨518,4,5,4⟩]⟩)
def qv577 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨577,[⟨64,7,5,4⟩,⟨64,1,3,1⟩,⟨443,1,5,4⟩,⟨443,7,3,1⟩]⟩)
def qv578 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨578,[⟨574,4,4,5⟩,⟨2,1,4,3⟩]⟩)
def qv579 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨579,[⟨2,1,4,3⟩,⟨576,4,4,5⟩]⟩)
def qv580 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨580,[⟨2,7,4,2⟩,⟨579,0,3,3⟩]⟩)
def qv581 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨581,[⟨578,4,5,3⟩,⟨2,5,4,2⟩]⟩)
def qv582 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨582,[⟨40,3,4,3⟩,⟨446,5,5,3⟩,⟨523,0,7,0⟩,⟨480,4,5,3⟩,⟨567,4,5,4⟩]⟩)
def qv583 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨583,[⟨25,5,4,3⟩,⟨525,0,5,4⟩,⟨582,0,2,8⟩,⟨221,3,3,7⟩]⟩)
def qv584 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨584,[⟨263,1,4,5⟩,⟨236,4,3,5⟩,⟨548,3,3,4⟩,⟨295,3,4,5⟩,⟨577,0,4,5⟩,⟨173,1,4,5⟩]⟩)
def qv585 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨585,[⟨236,2,5,1⟩,⟨300,4,4,5⟩,⟨479,1,4,5⟩,⟨577,0,4,5⟩,⟨183,3,4,5⟩,⟨527,6,5,1⟩]⟩)
def qv586 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨586,[⟨465,4,4,5⟩,⟨558,1,4,5⟩,⟨385,1,4,5⟩,⟨379,4,4,5⟩,⟨524,0,4,5⟩,⟨469,2,4,5⟩,⟨467,2,4,5⟩,⟨527,4,5,5⟩,⟨553,0,4,5⟩,⟨552,1,4,5⟩,⟨555,1,4,5⟩,⟨564,0,6,4⟩,⟨583,0,5,2⟩]⟩)
def qv587 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨587,[⟨300,2,4,1⟩,⟨479,1,4,5⟩,⟨319,3,5,5⟩,⟨477,6,4,1⟩,⟨252,3,4,5⟩,⟨467,2,4,5⟩]⟩)
def qv588 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨588,[⟨3,1,3,3⟩,⟨586,0,4,5⟩]⟩)
def qv589 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨589,[⟨4,1,4,3⟩,⟨588,0,4,5⟩]⟩)
def qv590 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨590,[⟨295,7,4,3⟩,⟨173,7,4,3⟩,⟨577,0,4,7⟩,⟨490,0,4,7⟩,⟨217,5,4,3⟩]⟩)
def qv591 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨591,[⟨524,0,4,5⟩,⟨529,1,4,1⟩,⟨529,3,4,1⟩,⟨538,1,4,1⟩,⟨538,3,4,1⟩,⟨197,5,4,1⟩]⟩)
def qv592 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨592,[⟨588,0,4,5⟩,⟨108,7,3,0⟩]⟩)
def qv593 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨593,[⟨2,7,4,2⟩,⟨586,0,4,5⟩]⟩)
def qv594 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨594,[⟨30,1,4,3⟩,⟨476,1,4,3⟩,⟨588,0,4,5⟩]⟩)
def qv595 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨595,[⟨460,4,2,4⟩,⟨460,2,5,4⟩,⟨586,1,5,4⟩,⟨411,4,5,4⟩,⟨551,1,2,4⟩,⟨406,5,5,4⟩,⟨572,0,2,4⟩]⟩)
def qv596 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨596,[⟨385,5,4,2⟩,⟨592,0,5,6⟩,⟨330,1,4,6⟩,⟨529,5,4,6⟩,⟨385,1,4,6⟩,⟨330,5,4,2⟩]⟩)
def qv597 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨597,[⟨24,6,2,3⟩,⟨221,0,6,4⟩,⟨199,3,2,4⟩,⟨594,1,6,5⟩]⟩)
def qv598 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨598,[⟨594,0,5,6⟩,⟨456,5,4,2⟩,⟨254,1,3,2⟩,⟨554,1,3,2⟩,⟨465,0,4,6⟩]⟩)
def qv599 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨599,[⟨578,4,5,3⟩,⟨492,0,3,1⟩,⟨512,4,3,1⟩,⟨586,4,4,5⟩,⟨485,0,5,3⟩,⟨579,4,5,3⟩]⟩)
def qv600 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨600,[⟨448,0,4,5⟩,⟨278,2,1,4⟩,⟨592,5,5,3⟩,⟨403,5,5,4⟩,⟨146,5,4,3⟩]⟩)
def qv601 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨601,[⟨437,6,4,1⟩,⟨553,0,4,5⟩,⟨592,0,5,5⟩,⟨236,4,3,5⟩,⟨469,4,4,1⟩]⟩)
def qv602 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨602,[⟨553,0,4,7⟩,⟨467,4,4,3⟩,⟨592,0,5,7⟩,⟨437,6,4,3⟩,⟨236,4,3,7⟩]⟩)
def qv603 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨603,[⟨505,1,5,4⟩,⟨505,5,5,4⟩,⟨586,5,5,4⟩,⟨551,7,5,4⟩,⟨531,6,4,2⟩,⟨586,1,5,4⟩,⟨585,1,5,4⟩,⟨585,5,5,4⟩,⟨551,3,5,4⟩,⟨573,1,5,4⟩,⟨533,5,5,4⟩,⟨533,1,5,4⟩]⟩)
def qv604 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨604,[⟨597,0,3,4⟩,⟨375,2,4,3⟩,⟨597,1,4,3⟩,⟨375,3,3,4⟩,⟨350,3,4,3⟩,⟨350,2,3,4⟩]⟩)
def qv605 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨605,[⟨400,5,4,3⟩,⟨383,6,3,4⟩,⟨530,4,4,3⟩,⟨596,1,3,4⟩,⟨522,2,4,3⟩,⟨598,0,4,3⟩,⟨537,3,3,4⟩,⟨520,1,4,3⟩,⟨550,4,4,3⟩]⟩)
def qv606 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨606,[⟨123,1,4,3⟩,⟨274,0,4,3⟩,⟨605,0,6,4⟩,⟨119,1,4,3⟩]⟩)
def qv607 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨607,[⟨420,3,1,2⟩,⟨419,3,1,4⟩,⟨589,0,5,5⟩,⟨314,0,3,4⟩,⟨571,1,7,3⟩]⟩)
def qv608 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨608,[⟨486,4,4,5⟩,⟨515,1,4,5⟩,⟨580,0,4,5⟩,⟨521,0,4,5⟩,⟨581,4,4,5⟩,⟨593,0,4,5⟩,⟨599,4,4,5⟩,⟨606,1,6,2⟩]⟩)
def qv609 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨609,[⟨286,4,4,5⟩,⟨107,3,4,5⟩,⟨532,4,4,5⟩,⟨542,0,4,5⟩,⟨221,3,4,5⟩,⟨562,4,4,5⟩,⟨575,4,4,5⟩,⟨604,1,6,4⟩]⟩)
def qv610 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨610,[⟨221,2,5,4⟩,⟨286,5,5,4⟩,⟨107,2,5,4⟩,⟨472,1,5,4⟩,⟨566,1,5,4⟩,⟨532,5,5,4⟩,⟨542,1,5,4⟩,⟨609,0,2,6⟩]⟩)
def qv611 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨611,[⟨456,2,5,4⟩,⟨456,4,1,4⟩,⟨594,7,1,3⟩,⟨594,1,5,5⟩]⟩)
def qv612 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨612,[⟨589,1,5,5⟩,⟨589,7,0,3⟩]⟩)
def qv613 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨613,[⟨607,5,5,4⟩,⟨503,3,1,4⟩,⟨592,7,1,3⟩,⟨592,5,5,3⟩,⟨607,7,1,4⟩,⟨612,4,1,4⟩,⟨612,0,5,4⟩]⟩)
def qv614 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨614,[⟨608,1,7,5⟩,⟨543,3,5,6⟩,⟨370,6,3,4⟩,⟨392,7,3,4⟩,⟨610,3,5,6⟩,⟨600,0,6,4⟩,⟨613,0,6,4⟩]⟩)
def qv615 : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨615,[⟨602,7,6,4⟩,⟨614,1,4,3⟩,⟨533,5,6,4⟩,⟨590,7,6,4⟩,⟨611,6,3,4⟩,⟨587,3,3,4⟩,⟨601,5,6,4⟩,⟨406,1,6,4⟩,⟨591,3,3,4⟩,⟨586,3,3,4⟩,⟨584,5,6,4⟩,⟨406,3,3,4⟩]⟩)
def qu0 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv6,qv7,qv8,qv9,qv10,qv11,qv12,qv13,qv14,qv15,qv16,qv17,qv18,qv19,qv20,qv21,qv22,qv23,qv24,qv25])
def qu1 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv26,qv27,qv28,qv29,qv30,qv31,qv32,qv33,qv34,qv35,qv36,qv37,qv38,qv39,qv40,qv41,qv42,qv43,qv44,qv45])
def qu2 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv46,qv47,qv48,qv49,qv50,qv51,qv52,qv53,qv54,qv55,qv56,qv57,qv58,qv59,qv60,qv61,qv62,qv63,qv64,qv65])
def qu3 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv66,qv67,qv68,qv69,qv70,qv71,qv72,qv73,qv74,qv75,qv76,qv77,qv78,qv79,qv80,qv81,qv82,qv83,qv84,qv85])
def qu4 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv86,qv87,qv88,qv89,qv90,qv91,qv92,qv93,qv94,qv95,qv96,qv97,qv98,qv99,qv100,qv101,qv102,qv103,qv104,qv105])
def qu5 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv106,qv107,qv108,qv109,qv110,qv111,qv112,qv113,qv114,qv115,qv116,qv117,qv118,qv119,qv120,qv121,qv122,qv123,qv124,qv125])
def qu6 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv126,qv127,qv128,qv129,qv130,qv131,qv132,qv133,qv134,qv135,qv136,qv137,qv138,qv139,qv140,qv141,qv142,qv143,qv144,qv145])
def qu7 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv146,qv147,qv148,qv149,qv150,qv151,qv152,qv153,qv154,qv155,qv156,qv157,qv158,qv159,qv160,qv161,qv162,qv163,qv164,qv165])
def qu8 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv166,qv167,qv168,qv169,qv170,qv171,qv172,qv173,qv174,qv175,qv176,qv177,qv178,qv179,qv180,qv181,qv182,qv183,qv184,qv185])
def qu9 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv186,qv187,qv188,qv189,qv190,qv191,qv192,qv193,qv194,qv195,qv196,qv197,qv198,qv199,qv200,qv201,qv202,qv203,qv204,qv205])
def qu10 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv206,qv207,qv208,qv209,qv210,qv211,qv212,qv213,qv214,qv215,qv216,qv217,qv218,qv219,qv220,qv221,qv222,qv223,qv224,qv225])
def qu11 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv226,qv227,qv228,qv229,qv230,qv231,qv232,qv233,qv234,qv235,qv236,qv237,qv238,qv239,qv240,qv241,qv242,qv243,qv244,qv245])
def qu12 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv246,qv247,qv248,qv249,qv250,qv251,qv252,qv253,qv254,qv255,qv256,qv257,qv258,qv259,qv260,qv261,qv262,qv263,qv264,qv265])
def qu13 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv266,qv267,qv268,qv269,qv270,qv271,qv272,qv273,qv274,qv275,qv276,qv277,qv278,qv279,qv280,qv281,qv282,qv283,qv284,qv285])
def qu14 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv286,qv287,qv288,qv289,qv290,qv291,qv292,qv293,qv294,qv295,qv296,qv297,qv298,qv299,qv300,qv301,qv302,qv303,qv304,qv305])
def qu15 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv306,qv307,qv308,qv309,qv310,qv311,qv312,qv313,qv314,qv315,qv316,qv317,qv318,qv319,qv320,qv321,qv322,qv323,qv324,qv325])
def qu16 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv326,qv327,qv328,qv329,qv330,qv331,qv332,qv333,qv334,qv335,qv336,qv337,qv338,qv339,qv340,qv341,qv342,qv343,qv344,qv345])
def qu17 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv346,qv347,qv348,qv349,qv350,qv351,qv352,qv353,qv354,qv355,qv356,qv357,qv358,qv359,qv360,qv361,qv362,qv363,qv364,qv365])
def qu18 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv366,qv367,qv368,qv369,qv370,qv371,qv372,qv373,qv374,qv375,qv376,qv377,qv378,qv379,qv380,qv381,qv382,qv383,qv384,qv385])
def qu19 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv386,qv387,qv388,qv389,qv390,qv391,qv392,qv393,qv394,qv395,qv396,qv397,qv398,qv399,qv400,qv401,qv402,qv403,qv404,qv405])
def qu20 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv406,qv407,qv408,qv409,qv410,qv411,qv412,qv413,qv414,qv415,qv416,qv417,qv418,qv419,qv420,qv421,qv422,qv423,qv424,qv425])
def qu21 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv426,qv427,qv428,qv429,qv430,qv431,qv432,qv433,qv434,qv435,qv436,qv437,qv438,qv439,qv440,qv441,qv442,qv443,qv444,qv445])
def qu22 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv446,qv447,qv448,qv449,qv450,qv451,qv452,qv453,qv454,qv455,qv456,qv457,qv458,qv459,qv460,qv461,qv462,qv463,qv464,qv465])
def qu23 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv466,qv467,qv468,qv469,qv470,qv471,qv472,qv473,qv474,qv475,qv476,qv477,qv478,qv479,qv480,qv481,qv482,qv483,qv484,qv485])
def qu24 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv486,qv487,qv488,qv489,qv490,qv491,qv492,qv493,qv494,qv495,qv496,qv497,qv498,qv499,qv500,qv501,qv502,qv503,qv504,qv505])
def qu25 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv506,qv507,qv508,qv509,qv510,qv511,qv512,qv513,qv514,qv515,qv516,qv517,qv518,qv519,qv520,qv521,qv522,qv523,qv524,qv525])
def qu26 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv526,qv527,qv528,qv529,qv530,qv531,qv532,qv533,qv534,qv535,qv536,qv537,qv538,qv539,qv540,qv541,qv542,qv543,qv544,qv545])
def qu27 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv546,qv547,qv548,qv549,qv550,qv551,qv552,qv553,qv554,qv555,qv556,qv557,qv558,qv559,qv560,qv561,qv562,qv563,qv564,qv565])
def qu28 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv566,qv567,qv568,qv569,qv570,qv571,qv572,qv573,qv574,qv575,qv576,qv577,qv578,qv579,qv580,qv581,qv582,qv583,qv584,qv585])
def qu29 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv586,qv587,qv588,qv589,qv590,qv591,qv592,qv593,qv594,qv595,qv596,qv597,qv598,qv599,qv600,qv601,qv602,qv603,qv604,qv605])
def qu30 : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (#[qv606,qv607,qv608,qv609,qv610,qv611,qv612,qv613,qv614,qv615])
def qtable : Array qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (((((qu0 ++ (qu1 ++ qu2)) ++ ((qu3 ++ qu4) ++ (qu5 ++ qu6))) ++ (((qu7 ++ qu8) ++ (qu9 ++ qu10)) ++ ((qu11 ++ qu12) ++ (qu13 ++ qu14)))) ++ ((((qu15 ++ qu16) ++ (qu17 ++ qu18)) ++ ((qu19 ++ qu20) ++ (qu21 ++ qu22))) ++ (((qu23 ++ qu24) ++ (qu25 ++ qu26)) ++ ((qu27 ++ qu28) ++ (qu29 ++ qu30))))))
def qe (i : ℕ) : qE := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (qtable[i - 6]?.getD qemptyEntry)
def qTableValid : Prop := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (qtable.size = 610 ∧ ∀ k,k < qtable.size →
    let e := qtable[k]?.getD qemptyEntry
    e.index = k + 6 ∧ e.terms ≠ [] ∧ ∀ t ∈ e.terms,t.child < e.index)
def qplacementCount : ℕ := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ((qtable.toList.map fun e => e.terms.length).sum)
abbrev qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (Finset qCell × Finset qCell × ℕ)
def qR.A (x : qR) : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (x.1)
def qR.H (x : qR) : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (x.2.1)
def qR.height (x : qR) : ℕ := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (x.2.2)
def qemptyRow : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨∅,∅,0⟩)
def qbaseRow (i : Fin 6) : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨qbaseRequired i,qbaseEnvelope i,1⟩)
def qplaceRow (t : qT) (d : qR) : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨d.A.image (qplacement t.rotation t.shift),
   d.H.image (qplacement t.rotation t.shift),d.height⟩)
def qunionA (ds : List qR) : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ((ds.map qR.A).foldr (· ∪ ·) ∅)
def qunionH (ds : List qR) : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ((ds.map qR.H).foldr (· ∪ ·) ∅)
def qcommonH (ds : List qR) : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (match ds with
  | [] => ∅
  | d :: rest => (rest.map qR.H).foldr (· ∩ ·) d.H)
def qforkRow (ds : List qR) : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨(qunionA ds ∪ qcommonH ds).erase qorigin,
   insert qorigin (qunionH ds),1 + (ds.map qR.height).foldr max 0⟩)
def qr (i : ℕ) : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (if h : i < 6 then qbaseRow ⟨i,h⟩ else
    qforkRow ((qe i).terms.map fun t =>
      qplaceRow t (if _ : t.child < i then qr t.child else qemptyRow)))
  termination_by i
def qOutput (i : ℕ) (p : qCell) (size height : ℕ) (omitted : Set qCell) : Prop := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ((qr i).A = {p} ∧ (qr i).H.card = size ∧ (qr i).height = height ∧
  Disjoint (↑(qr i).H : Set qCell) omitted)
def qAllRows : Prop := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (∀ i,i < 616 →
  (qr i).A ⊆ (qr i).H ∧ qorigin ∈ (qr i).H ∧
  qorigin ∉ (qr i).A ∧ (qr i).height ≤ 34)
lemma qtable_valid_probe : qTableValid := by
  run_tac
    withTheReader Lean.Core.Context (fun c => { c with maxHeartbeats := 0 }) do
      Lean.Elab.Tactic.evalTactic (← `(tactic| (
          constructor
          · decide +kernel
          · have h : ∀ k : Fin qtable.size,
                let e := qtable[k.val]?.getD qemptyEntry
                e.index = k.val + 6 ∧ e.terms ≠ [] ∧ ∀ t ∈ e.terms,t.child < e.index := by
              run_tac
                withTheReader Lean.Core.Context (fun c => { c with maxHeartbeats := 0 }) do
                  Lean.Elab.Tactic.evalTactic (← `(tactic| decide +kernel))
            intro k hk
            exact h ⟨k,hk⟩)))
def qx (a b : qR) (ha : a.A = b.A) (hh : a.H = b.H) (ht : a.height = b.height) : a = b := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          apply Prod.ext
          · exact ha
          · apply Prod.ext
            · exact hh
            · exact ht)
def qz0 : qu0.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz1 : qu1.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz2 : qu2.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz3 : qu3.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz4 : qu4.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz5 : qu5.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz6 : qu6.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz7 : qu7.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz8 : qu8.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz9 : qu9.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz10 : qu10.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz11 : qu11.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz12 : qu12.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz13 : qu13.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz14 : qu14.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz15 : qu15.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz16 : qu16.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz17 : qu17.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz18 : qu18.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz19 : qu19.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz20 : qu20.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz21 : qu21.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz22 : qu22.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz23 : qu23.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz24 : qu24.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz25 : qu25.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz26 : qu26.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz27 : qu27.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz28 : qu28.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz29 : qu29.size = 20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qz30 : qu30.size = 10 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by rfl)
def qm0 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,0),(2,0),(3,0),(3,1),(4,1)},{(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)},1⟩)
def qentryLookup : Lean.Elab.Tactic.TacticM Unit := do
  Lean.Elab.Tactic.evalTactic (← `(tactic| (
    simp only [qe,qtable,Array.getElem?_append,Array.size_append,qz0,qz1,qz2,qz3,qz4,qz5,qz6,qz7,qz8,qz9,qz10,qz11,qz12,qz13,qz14,qz15,qz16,qz17,qz18,qz19,qz20,qz21,qz22,qz23,qz24,qz25,qz26,qz27,qz28,qz29,qz30,Nat.reduceSub,Nat.reduceLT,ite_true,ite_false]
    rfl)))
def qmeq_0 : qr 0 = qm0 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          rw [qr]
          run_tac
            withTheReader Lean.Core.Context (fun c => { c with maxHeartbeats := 0 }) do
              Lean.Elab.Tactic.evalTactic (← `(tactic| decide +kernel)))))
def qm1 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0),(1,0),(2,0),(2,1),(3,1)},{(-1,0),(0,0),(1,0),(2,0),(2,1),(3,1)},1⟩)
def qmeq_1 : qr 1 = qm1 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          rw [qr]
          run_tac
            withTheReader Lean.Core.Context (fun c => { c with maxHeartbeats := 0 }) do
              Lean.Elab.Tactic.evalTactic (← `(tactic| decide +kernel)))))
def qm2 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-1,0),(1,0),(1,1),(2,1)},{(-2,0),(-1,0),(0,0),(1,0),(1,1),(2,1)},1⟩)
def qmeq_2 : qr 2 = qm2 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          rw [qr]
          run_tac
            withTheReader Lean.Core.Context (fun c => { c with maxHeartbeats := 0 }) do
              Lean.Elab.Tactic.evalTactic (← `(tactic| decide +kernel)))))
def qm3 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0),(0,1),(1,1)},{(-3,0),(-2,0),(-1,0),(0,0),(0,1),(1,1)},1⟩)
def qmeq_3 : qr 3 = qm3 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          rw [qr]
          run_tac
            withTheReader Lean.Core.Context (fun c => { c with maxHeartbeats := 0 }) do
              Lean.Elab.Tactic.evalTactic (← `(tactic| decide +kernel)))))
def qm4 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-2,-1),(-1,-1),(0,-1),(1,0)},{(-3,-1),(-2,-1),(-1,-1),(0,-1),(0,0),(1,0)},1⟩)
def qmeq_4 : qr 4 = qm4 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          rw [qr]
          run_tac
            withTheReader Lean.Core.Context (fun c => { c with maxHeartbeats := 0 }) do
              Lean.Elab.Tactic.evalTactic (← `(tactic| decide +kernel)))))
def qm5 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,-1),(-3,-1),(-2,-1),(-1,-1),(-1,0)},{(-4,-1),(-3,-1),(-2,-1),(-1,-1),(-1,0),(0,0)},1⟩)
def qmeq_5 : qr 5 = qm5 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          rw [qr]
          run_tac
            withTheReader Lean.Core.Context (fun c => { c with maxHeartbeats := 0 }) do
              Lean.Elab.Tactic.evalTactic (← `(tactic| decide +kernel)))))
def qm6 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,-1),(-3,-1),(-2,-1),(-1,-1),(-1,0)},{(-4,-1),(-3,-1),(-2,-1),(-1,-1),(-1,0),(0,0)},2⟩)
def qmeq_6 : qr 6 = qm6 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 6 = qv6 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 6 < 6 by decide,↓reduceDIte,he,qv6,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm7 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,-1),(-3,-1),(-2,-1),(-1,-1),(0,-1)},{(-4,-1),(-3,-1),(-2,-1),(-1,-1),(-1,0),(0,-1),(0,0),(1,0)},3⟩)
def qmeq_7 : qr 7 = qm7 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 7 = qv7 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 7 < 6 by decide,↓reduceDIte,he,qv7,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_6]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm8 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-1),(1,-1),(1,0),(2,-1),(3,-1)},{(-1,0),(0,-1),(0,0),(1,-1),(1,0),(2,-1),(3,-1),(4,-1)},3⟩)
def qmeq_8 : qr 8 = qm8 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 8 = qv8 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 8 < 6 by decide,↓reduceDIte,he,qv8,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_6]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm9 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-3,1),(-2,0),(-2,1),(-1,0)},{(-4,1),(-3,0),(-3,1),(-2,0),(-2,1),(-1,0),(0,0),(1,0)},3⟩)
def qmeq_9 : qr 9 = qm9 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 9 = qv9 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 9 < 6 by decide,↓reduceDIte,he,qv9,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_6]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm10 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,-1),(-3,-1),(-3,0),(-1,-1),(-1,0)},{(-4,-1),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,0)},2⟩)
def qmeq_10 : qr 10 = qm10 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 10 = qv10 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 10 < 6 by decide,↓reduceDIte,he,qv10,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_2]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm11 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(-1,0),(-1,1),(1,0),(2,0)},{(-2,-1),(-2,1),(-1,-1),(-1,0),(-1,1),(0,0),(1,0),(2,0)},3⟩)
def qmeq_11 : qr 11 = qm11 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 11 = qv11 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 11 < 6 by decide,↓reduceDIte,he,qv11,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm12 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-2,-1),(-2,0),(-1,-1),(-1,0)},{(-4,-1),(-3,-1),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,0),(1,0)},2⟩)
def qmeq_12 : qr 12 = qm12 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 12 = qv12 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 12 < 6 by decide,↓reduceDIte,he,qv12,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm13 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-3,0),(-3,1),(-2,0),(-1,0)},{(-4,-1),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,0),(-1,0),(0,0)},3⟩)
def qmeq_13 : qr 13 = qm13 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 13 = qv13 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 13 < 6 by decide,↓reduceDIte,he,qv13,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm14 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,-1),(-3,-1),(-2,-1),(-2,0),(-1,0)},{(-4,-1),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,0),(0,0),(1,0)},2⟩)
def qmeq_14 : qr 14 = qm14 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 14 = qv14 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 14 < 6 by decide,↓reduceDIte,he,qv14,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_3]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm15 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-2,-1),(-1,-1),(-1,0),(1,0)},{(-3,-1),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,0),(1,0),(2,0)},2⟩)
def qmeq_15 : qr 15 = qm15 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 15 = qv15 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 15 < 6 by decide,↓reduceDIte,he,qv15,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_3]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm16 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-1),(0,-1),(1,0),(2,0)},{(-2,-1),(-1,-1),(-1,0),(0,-1),(0,0),(1,0),(2,0),(3,0)},2⟩)
def qmeq_16 : qr 16 = qm16 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 16 = qv16 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 16 < 6 by decide,↓reduceDIte,he,qv16,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_3]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm17 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,-1),(-3,-1),(-2,-1),(-2,0),(-1,0)},{(-4,-1),(-3,-1),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,0),(1,0)},2⟩)
def qmeq_17 : qr 17 = qm17 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 17 = qv17 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 17 < 6 by decide,↓reduceDIte,he,qv17,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_3]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm18 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-2,-1),(-1,-1),(-1,0),(1,0)},{(-3,-1),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,-1),(0,0),(1,0)},2⟩)
def qmeq_18 : qr 18 = qm18 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 18 = qv18 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 18 < 6 by decide,↓reduceDIte,he,qv18,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_3]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm19 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-2,1),(-1,0),(1,0),(1,1)},{(-3,1),(-2,0),(-2,1),(-1,0),(0,0),(1,0),(1,1),(2,1)},3⟩)
def qmeq_19 : qr 19 = qm19 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 19 = qv19 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 19 < 6 by decide,↓reduceDIte,he,qv19,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm20 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-3,1),(-2,0),(-1,0),(0,1)},{(-4,1),(-3,0),(-3,1),(-2,0),(-1,0),(0,0),(0,1),(1,1)},3⟩)
def qmeq_20 : qr 20 = qm20 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 20 = qv20 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 20 < 6 by decide,↓reduceDIte,he,qv20,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm21 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-2,0),(-1,0),(1,0),(1,1)},{(-3,-1),(-2,-1),(-2,0),(-1,0),(0,0),(1,0),(1,1),(2,1)},3⟩)
def qmeq_21 : qr 21 = qm21 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 21 = qv21 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 21 < 6 by decide,↓reduceDIte,he,qv21,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_6]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm22 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-1,0),(0,1),(1,1),(2,1)},{(-2,0),(-1,0),(0,0),(0,1),(1,0),(1,1),(2,1),(3,1)},2⟩)
def qmeq_22 : qr 22 = qm22 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 22 = qv22 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 22 < 6 by decide,↓reduceDIte,he,qv22,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_3]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm23 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-1),(-1,0),(0,-1),(1,0)},{(-3,-1),(-2,-1),(-1,-1),(-1,0),(0,-1),(0,0),(1,0),(2,0)},2⟩)
def qmeq_23 : qr 23 = qm23 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 23 = qv23 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 23 < 6 by decide,↓reduceDIte,he,qv23,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm24 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-2,-1),(-1,-1),(-1,0)},{(-4,-1),(-3,-1),(-2,-1),(-1,-1),(-1,0),(0,-1),(0,0),(1,0),(2,0)},3⟩)
def qmeq_24 : qr 24 = qm24 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 24 = qv24 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 24 < 6 by decide,↓reduceDIte,he,qv24,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_17]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm25 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-2,-1),(-1,-1),(-1,0)},{(-4,-1),(-3,-1),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,0),(1,0),(2,0)},3⟩)
def qmeq_25 : qr 25 = qm25 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 25 = qv25 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 25 < 6 by decide,↓reduceDIte,he,qv25,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_14]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm26 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-2,1),(-1,0),(-1,1),(1,0),(1,1)},{(-2,0),(-2,1),(-1,0),(-1,1),(0,0),(1,0),(1,1),(2,0),(2,1)},3⟩)
def qmeq_26 : qr 26 = qm26 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 26 = qv26 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 26 < 6 by decide,↓reduceDIte,he,qv26,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_6]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm27 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-1,0)},{(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-1,0),(0,0),(1,0)},3⟩)
def qmeq_27 : qr 27 = qm27 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 27 = qv27 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 27 < 6 by decide,↓reduceDIte,he,qv27,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_6]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm28 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-3),(-1,-2),(-1,-1),(-1,0),(1,0)},{(-2,-1),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,0),(0,1),(1,0),(2,0)},3⟩)
def qmeq_28 : qr 28 = qm28 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 28 = qv28 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 28 < 6 by decide,↓reduceDIte,he,qv28,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_6]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm29 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-3),(1,-2),(1,-1),(1,0),(2,-1),(4,-1)},{(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(2,-1),(3,-1),(4,-1)},3⟩)
def qmeq_29 : qr 29 = qm29 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 29 = qv29 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 29 < 6 by decide,↓reduceDIte,he,qv29,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_1,qmeq_6]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm30 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-1),(0,-1),(1,0)},{(-3,-1),(-2,-1),(-1,-1),(-1,0),(0,-1),(0,0),(1,0),(2,0),(3,0)},3⟩)
def qmeq_30 : qr 30 = qm30 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 30 = qv30 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 30 < 6 by decide,↓reduceDIte,he,qv30,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_14]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm31 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-1,0),(0,1),(1,1)},{(-3,0),(-2,0),(-1,0),(0,0),(0,1),(1,0),(1,1),(2,1),(3,1)},3⟩)
def qmeq_31 : qr 31 = qm31 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 31 = qv31 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 31 < 6 by decide,↓reduceDIte,he,qv31,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_17]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm32 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-3),(1,-2),(1,-1),(1,0),(2,-1),(3,-1)},{(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(2,-1),(3,-1),(4,-1)},3⟩)
def qmeq_32 : qr 32 = qm32 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 32 = qv32 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 32 < 6 by decide,↓reduceDIte,he,qv32,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_6]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm33 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0),(1,0),(1,1),(2,1)},{(-2,0),(-1,0),(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)},3⟩)
def qmeq_33 : qr 33 = qm33 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 33 = qv33 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 33 < 6 by decide,↓reduceDIte,he,qv33,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_17]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm34 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-3),(-1,-2),(-1,-1),(-1,0),(2,0)},{(-2,-1),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,0),(0,1),(1,0),(2,0)},3⟩)
def qmeq_34 : qr 34 = qm34 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 34 = qv34 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 34 < 6 by decide,↓reduceDIte,he,qv34,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_1,qmeq_6]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm35 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0),(1,0),(1,1),(2,1)},{(-2,0),(-1,0),(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1)},3⟩)
def qmeq_35 : qr 35 = qm35 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 35 = qv35 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 35 < 6 by decide,↓reduceDIte,he,qv35,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_14]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm36 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,0),(2,0),(2,1),(3,1)},{(-1,0),(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)},3⟩)
def qmeq_36 : qr 36 = qm36 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 36 = qv36 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 36 < 6 by decide,↓reduceDIte,he,qv36,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_17]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm37 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-3),(1,-2),(1,-1),(1,0),(3,-1),(4,-1)},{(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(2,-1),(3,-1),(4,-1)},3⟩)
def qmeq_37 : qr 37 = qm37 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 37 = qv37 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 37 < 6 by decide,↓reduceDIte,he,qv37,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_2,qmeq_6]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm38 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,-1),(-3,-1),(-2,-1),(-1,0)},{(-4,-1),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,0),(1,0)},3⟩)
def qmeq_38 : qr 38 = qm38 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 38 = qv38 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 38 < 6 by decide,↓reduceDIte,he,qv38,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_3,qmeq_16]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm39 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-1),(0,-1),(1,0)},{(-3,-1),(-2,-1),(-1,-1),(0,-1),(0,0),(1,-1),(1,0),(2,0),(3,0)},3⟩)
def qmeq_39 : qr 39 = qm39 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 39 = qv39 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 39 < 6 by decide,↓reduceDIte,he,qv39,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_17]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm40 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-2,-1),(-1,-1),(1,0)},{(-3,-1),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,-1),(0,0),(1,0),(2,0)},3⟩)
def qmeq_40 : qr 40 = qm40 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 40 = qv40 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 40 < 6 by decide,↓reduceDIte,he,qv40,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_3,qmeq_16]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm41 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0),(0,-3),(0,-2),(0,-1),(1,-1),(3,-1)},{(-1,0),(-1,1),(0,-3),(0,-2),(0,-1),(0,0),(1,-1),(2,-1),(3,-1)},3⟩)
def qmeq_41 : qr 41 = qm41 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 41 = qv41 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 41 < 6 by decide,↓reduceDIte,he,qv41,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_1,qmeq_6]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm42 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(1,0)},{(-3,1),(-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(0,0),(1,0),(2,0)},3⟩)
def qmeq_42 : qr 42 = qm42 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 42 = qv42 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 42 < 6 by decide,↓reduceDIte,he,qv42,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_6]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm43 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0),(0,-3),(0,-2),(0,-1),(2,-1),(3,-1)},{(-1,0),(-1,1),(0,-3),(0,-2),(0,-1),(0,0),(1,-1),(2,-1),(3,-1)},3⟩)
def qmeq_43 : qr 43 = qm43 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 43 = qv43 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 43 < 6 by decide,↓reduceDIte,he,qv43,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_2,qmeq_6]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm44 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,0),(-4,1),(-3,0),(-2,0),(-1,0)},{(-4,0),(-4,1),(-3,0),(-3,1),(-2,0),(-1,0),(-1,1),(0,0),(0,1),(1,1)},4⟩)
def qmeq_44 : qr 44 = qm44 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 44 = qv44 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 44 < 6 by decide,↓reduceDIte,he,qv44,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_7]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm45 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,0),(-3,0),(-3,1),(-2,0),(-1,0)},{(-4,0),(-4,1),(-3,0),(-3,1),(-2,0),(-1,0),(-1,1),(0,0),(0,1),(1,1)},4⟩)
def qmeq_45 : qr 45 = qm45 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 45 = qv45 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 45 < 6 by decide,↓reduceDIte,he,qv45,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_7]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm46 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,0),(-3,-1),(-3,0),(-2,0),(-1,0)},{(-4,-1),(-4,0),(-3,-1),(-3,0),(-2,0),(-1,0),(-1,1),(0,0),(0,1),(1,1)},4⟩)
def qmeq_46 : qr 46 = qm46 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 46 = qv46 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 46 < 6 by decide,↓reduceDIte,he,qv46,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_7]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm47 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0),(0,-3),(0,-2),(0,-1),(1,0),(2,-1),(2,0)},{(-1,0),(-1,1),(0,-3),(0,-2),(0,-1),(0,0),(1,0),(2,-1),(2,0),(3,-1)},3⟩)
def qmeq_47 : qr 47 = qm47 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 47 = qv47 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 47 < 6 by decide,↓reduceDIte,he,qv47,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm48 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-3),(1,-2),(1,-1),(1,0),(2,0),(3,-1),(3,0)},{(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(2,0),(3,-1),(3,0),(4,-1)},3⟩)
def qmeq_48 : qr 48 = qm48 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 48 = qv48 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 48 < 6 by decide,↓reduceDIte,he,qv48,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm49 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-4),(0,-4),(0,-3),(0,-2),(0,-1)},{(-1,-4),(-1,-3),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(1,-1),(1,0),(1,1)},4⟩)
def qmeq_49 : qr 49 = qm49 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 49 = qv49 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 49 < 6 by decide,↓reduceDIte,he,qv49,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_7]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm50 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0),(0,-4),(0,-3),(0,-2),(0,-1)},{(-1,0),(-1,1),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(1,-1),(1,0),(1,1)},4⟩)
def qmeq_50 : qr 50 = qm50 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 50 = qv50 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 50 < 6 by decide,↓reduceDIte,he,qv50,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_7]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm51 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-3,0),(-2,-1),(-2,0),(0,-1)},{(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,-1),(0,0),(1,-1),(1,0)},4⟩)
def qmeq_51 : qr 51 = qm51 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 51 = qv51 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 51 < 6 by decide,↓reduceDIte,he,qv51,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_10,qmeq_26]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm52 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-2,-1),(-1,-1),(-1,0),(0,-1),(1,-1),(2,-1)},{(-4,-1),(-3,-1),(-2,-1),(-1,-1),(-1,0),(0,-1),(0,0),(1,-1),(2,-1),(3,-1)},2⟩)
def qmeq_52 : qr 52 = qm52 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 52 = qv52 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 52 < 6 by decide,↓reduceDIte,he,qv52,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm53 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-2),(0,-1),(1,-1),(1,1),(1,2),(2,-1),(3,-1)},{(-1,0),(0,-2),(0,-1),(0,0),(0,1),(1,-1),(1,1),(1,2),(2,-1),(3,-1)},3⟩)
def qmeq_53 : qr 53 = qm53 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 53 = qv53 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 53 < 6 by decide,↓reduceDIte,he,qv53,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_3,qmeq_6]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm54 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,-1),(-3,-1),(-2,0),(-1,0)},{(-4,-1),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,0),(1,0)},3⟩)
def qmeq_54 : qr 54 = qm54 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 54 = qv54 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 54 < 6 by decide,↓reduceDIte,he,qv54,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_3,qmeq_22]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm55 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,0),(-3,0),(-2,0),(-1,0)},{(-5,1),(-4,0),(-4,1),(-3,0),(-3,1),(-2,0),(-1,0),(-1,1),(0,0),(0,1),(1,1)},4⟩)
def qmeq_55 : qr 55 = qm55 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 55 = qv55 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 55 < 6 by decide,↓reduceDIte,he,qv55,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm56 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,0),(-3,0),(-2,0),(-1,0)},{(-5,-1),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,0),(-1,0),(0,0)},4⟩)
def qmeq_56 : qr 56 = qm56 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 56 = qv56 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 56 < 6 by decide,↓reduceDIte,he,qv56,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm57 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,0),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,0)},{(-4,0),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,0),(-1,1),(0,0),(0,1),(1,0),(1,1)},4⟩)
def qmeq_57 : qr 57 = qm57 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 57 = qv57 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 57 < 6 by decide,↓reduceDIte,he,qv57,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_7]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm58 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,0),(-3,0),(-3,1),(-2,0),(-2,1),(-1,0)},{(-4,0),(-3,0),(-3,1),(-2,0),(-2,1),(-1,0),(-1,1),(0,0),(0,1),(1,0),(1,1)},4⟩)
def qmeq_58 : qr 58 = qm58 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 58 = qv58 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 58 < 6 by decide,↓reduceDIte,he,qv58,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_7]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm59 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,0),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,0)},{(-5,1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-1,0),(0,0),(1,0)},4⟩)
def qmeq_59 : qr 59 = qm59 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 59 = qv59 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 59 < 6 by decide,↓reduceDIte,he,qv59,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_7]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm60 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(-1,0),(1,0)},{(-3,-1),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,0),(1,0),(1,1),(2,0),(2,1),(3,1)},5⟩)
def qmeq_60 : qr 60 = qm60 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 60 = qv60 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 60 < 6 by decide,↓reduceDIte,he,qv60,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_49]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm61 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-2,-1),(-1,-3),(-1,-2),(-1,-1),(0,-1)},{(-3,-1),(-2,-1),(-1,-3),(-1,-2),(-1,-1),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,0)},3⟩)
def qmeq_61 : qr 61 = qm61 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 61 = qv61 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 61 < 6 by decide,↓reduceDIte,he,qv61,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_14]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm62 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-3,0),(-2,0),(-2,2),(-2,3),(-1,0)},{(-4,-1),(-4,1),(-3,-1),(-3,0),(-3,1),(-3,2),(-2,0),(-2,2),(-2,3),(-1,0),(0,0)},4⟩)
def qmeq_62 : qr 62 = qm62 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 62 = qv62 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 62 < 6 by decide,↓reduceDIte,he,qv62,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_53]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm63 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-4),(1,-3),(1,-2),(1,-1)},{(0,-1),(0,0),(0,1),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(2,-1),(2,0),(2,1)},5⟩)
def qmeq_63 : qr 63 = qm63 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 63 = qv63 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 63 < 6 by decide,↓reduceDIte,he,qv63,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_50]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm64 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,1),(1,1),(2,1),(3,1)},{(-1,0),(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)},5⟩)
def qmeq_64 : qr 64 = qm64 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 64 = qv64 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 64 < 6 by decide,↓reduceDIte,he,qv64,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_49]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm65 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-3,0),(-2,0),(-1,0)},{(-4,-1),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,0),(0,0),(0,1),(1,0),(1,1),(2,1)},5⟩)
def qmeq_65 : qr 65 = qm65 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 65 = qv65 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 65 < 6 by decide,↓reduceDIte,he,qv65,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_49]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm66 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-3),(1,-2),(1,-1),(1,0),(3,-1),(4,-1)},{(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(2,0),(2,1),(3,-1),(3,0),(4,-1)},4⟩)
def qmeq_66 : qr 66 = qm66 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 66 = qv66 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 66 < 6 by decide,↓reduceDIte,he,qv66,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_53]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm67 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(-1,-3),(-1,-2),(-1,-1),(-1,0)},{(-3,-1),(-2,-1),(-2,0),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,0),(0,1),(1,0),(2,0)},4⟩)
def qmeq_67 : qr 67 = qm67 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 67 = qv67 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 67 < 6 by decide,↓reduceDIte,he,qv67,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_9]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm68 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-3,1),(-2,0),(-1,0)},{(-4,1),(-3,0),(-3,1),(-2,0),(-2,1),(-1,0),(0,0),(0,1),(1,0),(1,1),(2,1)},5⟩)
def qmeq_68 : qr 68 = qm68 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 68 = qv68 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 68 < 6 by decide,↓reduceDIte,he,qv68,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_44]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm69 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-3),(1,-2),(1,-1),(1,0),(1,1),(4,1)},{(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)},4⟩)
def qmeq_69 : qr 69 = qm69 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 69 = qv69 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 69 < 6 by decide,↓reduceDIte,he,qv69,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_34]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm70 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-4),(1,-3),(1,-2),(1,-1),(2,-1),(4,-1)},{(0,-1),(0,0),(0,1),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(2,-1),(3,-1),(4,-1)},4⟩)
def qmeq_70 : qr 70 = qm70 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 70 = qv70 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 70 < 6 by decide,↓reduceDIte,he,qv70,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_41]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm71 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-1,-3),(-1,-2),(-1,-1),(-1,0),(1,-1)},{(-3,0),(-2,0),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(1,-1),(2,-1)},3⟩)
def qmeq_71 : qr 71 = qm71 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 71 = qv71 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 71 < 6 by decide,↓reduceDIte,he,qv71,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_23]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm72 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,1),(-1,1),(-1,2),(-1,3),(0,1),(1,1)},{(-3,1),(-2,1),(-1,1),(-1,2),(-1,3),(-1,4),(0,0),(0,1),(1,0),(1,1),(2,0)},4⟩)
def qmeq_72 : qr 72 = qm72 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 72 = qv72 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 72 < 6 by decide,↓reduceDIte,he,qv72,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_8]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm73 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,1),(0,-3),(0,-2),(0,-1)},{(-1,0),(-1,1),(-1,2),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,0),(1,1),(1,2)},5⟩)
def qmeq_73 : qr 73 = qm73 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 73 = qv73 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 73 < 6 by decide,↓reduceDIte,he,qv73,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_50]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm74 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-2),(0,-2),(0,1),(1,-2),(2,-2)},{(-2,-1),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-2),(0,-1),(0,0),(0,1),(1,-2),(2,-2)},4⟩)
def qmeq_74 : qr 74 = qm74 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 74 = qv74 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 74 < 6 by decide,↓reduceDIte,he,qv74,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_2,qmeq_53]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm75 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-1),(0,-1),(1,-1),(1,0),(2,-1)},{(-3,-1),(-2,-1),(-1,-1),(-1,0),(0,-1),(0,0),(1,-1),(1,0),(2,-1),(3,-1),(4,-1)},4⟩)
def qmeq_75 : qr 75 = qm75 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 75 = qv75 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 75 < 6 by decide,↓reduceDIte,he,qv75,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_9]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm76 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0),(0,-1),(1,0),(1,1),(1,2),(2,1)},{(-1,0),(0,-1),(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)},3⟩)
def qmeq_76 : qr 76 = qm76 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 76 = qv76 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 76 < 6 by decide,↓reduceDIte,he,qv76,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_14]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm77 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-1),(-1,0),(-1,1),(-1,2),(0,-1)},{(-3,-1),(-2,-1),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-1),(0,0),(1,0),(2,0)},3⟩)
def qmeq_77 : qr 77 = qm77 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 77 = qv77 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 77 < 6 by decide,↓reduceDIte,he,qv77,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_12]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm78 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-1),(0,-1),(1,-1),(2,-1),(3,-1)},{(-3,-1),(-2,-1),(-1,-1),(-1,0),(0,-1),(0,0),(1,-1),(1,0),(2,-1),(3,-1),(4,-1)},3⟩)
def qmeq_78 : qr 78 = qm78 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 78 = qv78 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 78 < 6 by decide,↓reduceDIte,he,qv78,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_52]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm79 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(1,0),(2,-1),(2,0)},{(-1,0),(-1,1),(0,-3),(0,-2),(0,-1),(0,0),(1,0),(1,1),(2,-1),(2,0),(3,-1)},4⟩)
def qmeq_79 : qr 79 = qm79 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 79 = qv79 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 79 < 6 by decide,↓reduceDIte,he,qv79,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_48]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm80 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-1),(-1,0),(1,-1),(1,0),(1,1)},{(-2,-1),(-2,0),(-1,-1),(-1,0),(0,0),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1)},4⟩)
def qmeq_80 : qr 80 = qm80 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 80 = qv80 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 80 < 6 by decide,↓reduceDIte,he,qv80,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_13]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm81 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-4),(1,-3),(1,-2),(1,-1),(3,-1),(4,-1)},{(0,-1),(0,0),(0,1),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(2,-1),(3,-1),(4,-1)},4⟩)
def qmeq_81 : qr 81 = qm81 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 81 = qv81 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 81 < 6 by decide,↓reduceDIte,he,qv81,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_43]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm82 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-3),(-1,-2),(-1,-1),(-1,0)},{(-4,-1),(-3,-1),(-2,-1),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(1,0),(2,0)},4⟩)
def qmeq_82 : qr 82 = qm82 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 82 = qv82 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 82 < 6 by decide,↓reduceDIte,he,qv82,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_36]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm83 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-1),(1,-1),(1,0),(1,1),(1,2)},{(-1,0),(0,-1),(0,0),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-2),(2,-1),(3,-1),(4,-1)},5⟩)
def qmeq_83 : qr 83 = qm83 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 83 = qv83 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 83 < 6 by decide,↓reduceDIte,he,qv83,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_67]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm84 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-1),(1,-3),(1,-2),(1,-1),(1,0)},{(-1,-1),(0,-1),(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(2,0),(2,1),(3,0),(4,0)},5⟩)
def qmeq_84 : qr 84 = qm84 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 84 = qv84 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 84 < 6 by decide,↓reduceDIte,he,qv84,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_67]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm85 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-1),(-1,0),(0,-1),(1,-1)},{(-3,-1),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,-1),(0,0),(1,-1),(1,0),(2,-1),(2,0),(3,-1)},4⟩)
def qmeq_85 : qr 85 = qm85 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 85 = qv85 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 85 < 6 by decide,↓reduceDIte,he,qv85,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_8,qmeq_9]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm86 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,0)},{(-4,1),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-2,-2),(-2,-1),(-2,0),(-1,0),(0,0),(1,0)},5⟩)
def qmeq_86 : qr 86 = qm86 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 86 = qv86 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 86 < 6 by decide,↓reduceDIte,he,qv86,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_67]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm87 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-1,0),(-1,1),(-1,2),(0,-1)},{(-3,0),(-2,0),(-1,0),(-1,1),(-1,2),(-1,3),(0,-1),(0,0),(1,-1),(1,0),(2,-1),(3,-1)},4⟩)
def qmeq_87 : qr 87 = qm87 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 87 = qv87 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 87 < 6 by decide,↓reduceDIte,he,qv87,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_24]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm88 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(-1,-1),(-1,0),(1,0)},{(-3,1),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-2),(-1,-1),(-1,0),(0,0),(1,0),(2,0)},5⟩)
def qmeq_88 : qr 88 = qm88 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 88 = qv88 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 88 < 6 by decide,↓reduceDIte,he,qv88,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_67]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm89 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(0,-4),(0,-3),(0,-2),(0,-1)},{(-1,-4),(-1,-3),(-1,-2),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1)},4⟩)
def qmeq_89 : qr 89 = qm89 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 89 = qv89 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 89 < 6 by decide,↓reduceDIte,he,qv89,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_8]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm90 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-2,-1),(-1,0)},{(-5,-1),(-4,-1),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,-1),(0,0),(1,0),(2,0)},4⟩)
def qmeq_90 : qr 90 = qm90 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 90 = qv90 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 90 < 6 by decide,↓reduceDIte,he,qv90,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_31,qmeq_54]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm91 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-3),(1,-2),(1,-1),(1,0),(4,-1)},{(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(2,-1),(2,0),(2,1),(3,-1),(3,0),(4,-1)},5⟩)
def qmeq_91 : qr 91 = qm91 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 91 = qv91 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 91 < 6 by decide,↓reduceDIte,he,qv91,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_74]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm92 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-1,-3),(-1,-2),(-1,-1),(-1,0)},{(-4,-1),(-3,-1),(-2,-1),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(1,0),(2,0)},4⟩)
def qmeq_92 : qr 92 = qm92 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 92 = qv92 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 92 < 6 by decide,↓reduceDIte,he,qv92,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_33]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm93 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-4),(1,-3),(1,-2),(1,-1),(2,0),(3,-1),(3,0)},{(0,-1),(0,0),(0,1),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(2,0),(3,-1),(3,0),(4,-1)},4⟩)
def qmeq_93 : qr 93 = qm93 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 93 = qv93 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 93 < 6 by decide,↓reduceDIte,he,qv93,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_47]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm94 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(0,-1)},{(-2,-2),(-2,-1),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-1),(0,0),(0,1)},4⟩)
def qmeq_94 : qr 94 = qm94 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 94 = qv94 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 94 < 6 by decide,↓reduceDIte,he,qv94,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_27]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm95 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(0,-1),(2,0)},{(-2,1),(-2,2),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-1),(0,0),(1,0),(2,0)},4⟩)
def qmeq_95 : qr 95 = qm95 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 95 = qv95 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 95 < 6 by decide,↓reduceDIte,he,qv95,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_29]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm96 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(1,0),(3,0)},{(-1,0),(-1,1),(-1,2),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,0),(1,1),(2,0),(3,0)},5⟩)
def qmeq_96 : qr 96 = qm96 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 96 = qv96 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 96 < 6 by decide,↓reduceDIte,he,qv96,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_70]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm97 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-3,0),(-3,1),(-2,0),(-1,0)},{(-4,-1),(-3,-1),(-3,0),(-3,1),(-2,0),(-2,1),(-1,0),(0,0),(0,1),(1,0),(1,1),(2,1)},5⟩)
def qmeq_97 : qr 97 = qm97 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 97 = qv97 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 97 < 6 by decide,↓reduceDIte,he,qv97,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_44]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm98 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(-1,0),(-1,1),(1,0),(2,0)},{(-2,-1),(-1,-1),(-1,0),(-1,1),(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1)},5⟩)
def qmeq_98 : qr 98 = qm98 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 98 = qv98 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 98 < 6 by decide,↓reduceDIte,he,qv98,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_44]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm99 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-4),(-1,-3),(-1,-1),(0,-1)},{(-3,-1),(-2,-1),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(0,-1),(0,0),(1,-1),(1,0),(2,0),(3,0)},4⟩)
def qmeq_99 : qr 99 = qm99 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 99 = qv99 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 99 < 6 by decide,↓reduceDIte,he,qv99,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_2,qmeq_24]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm100 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-1,0),(0,-1)},{(-3,-1),(-3,0),(-3,1),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-1,0),(0,-1),(0,0),(1,-1),(1,0)},4⟩)
def qmeq_100 : qr 100 = qm100 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 100 = qv100 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 100 < 6 by decide,↓reduceDIte,he,qv100,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_48]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm101 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-2),(-1,-1),(0,-1),(0,1)},{(-3,-1),(-2,-1),(-1,-2),(-1,-1),(0,-1),(0,0),(0,1),(0,2),(1,-1),(1,0),(2,0),(3,0)},4⟩)
def qmeq_101 : qr 101 = qm101 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 101 = qv101 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 101 < 6 by decide,↓reduceDIte,he,qv101,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_24]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm102 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0),(1,-3),(1,-2),(1,-1),(1,0)},{(-2,0),(-1,0),(0,-1),(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(2,-1),(3,-1),(4,-1)},4⟩)
def qmeq_102 : qr 102 = qm102 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 102 = qv102 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 102 < 6 by decide,↓reduceDIte,he,qv102,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_25]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm103 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-3),(1,-2),(1,-1),(1,0),(3,-1)},{(-1,0),(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(2,-1),(2,0),(2,1),(3,-1),(4,-1)},4⟩)
def qmeq_103 : qr 103 = qm103 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 103 = qv103 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 103 < 6 by decide,↓reduceDIte,he,qv103,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_71]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm104 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-2,-1),(-1,-1),(0,-1),(1,-1)},{(-4,-1),(-3,-1),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,-1),(0,0),(1,-1),(1,0),(2,-1),(3,-1)},5⟩)
def qmeq_104 : qr 104 = qm104 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 104 = qv104 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 104 < 6 by decide,↓reduceDIte,he,qv104,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_75]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm105 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-1,0),(-1,1),(-1,2),(-1,3)},{(-3,0),(-2,0),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(0,1),(1,1),(2,1)},4⟩)
def qmeq_105 : qr 105 = qm105 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 105 = qv105 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 105 < 6 by decide,↓reduceDIte,he,qv105,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_77]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm106 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-3),(-1,-2),(-1,-1),(-1,0)},{(-4,-1),(-3,-1),(-2,-1),(-2,0),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,0),(0,1),(1,0),(2,0)},4⟩)
def qmeq_106 : qr 106 = qm106 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 106 = qv106 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 106 < 6 by decide,↓reduceDIte,he,qv106,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_36]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm107 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-3,0),(-2,0),(-1,0)},{(-4,-1),(-3,-1),(-3,0),(-2,0),(-1,0),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,1)},6⟩)
def qmeq_107 : qr 107 = qm107 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 107 = qv107 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 107 < 6 by decide,↓reduceDIte,he,qv107,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_63]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm108 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,-1),(-3,0),(-2,0),(-1,0)},{(-4,-1),(-3,-1),(-3,0),(-2,0),(-1,0),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,1)},6⟩)
def qmeq_108 : qr 108 = qm108 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 108 = qv108 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 108 < 6 by decide,↓reduceDIte,he,qv108,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_63]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm109 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,-1),(-3,0),(-2,0),(-1,0)},{(-4,-1),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,0),(-2,1),(-1,0),(0,0),(0,1),(1,0),(1,1),(2,1)},5⟩)
def qmeq_109 : qr 109 = qm109 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 109 = qv109 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 109 < 6 by decide,↓reduceDIte,he,qv109,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_55]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm110 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(-1,0),(1,0)},{(-3,-1),(-2,-1),(-2,0),(-1,0),(0,0),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,1)},6⟩)
def qmeq_110 : qr 110 = qm110 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 110 = qv110 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 110 < 6 by decide,↓reduceDIte,he,qv110,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_63]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm111 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,0),(1,1),(1,2),(1,3)},{(-1,1),(0,-1),(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(3,0),(4,0)},6⟩)
def qmeq_111 : qr 111 = qm111 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 111 = qv111 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 111 < 6 by decide,↓reduceDIte,he,qv111,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_83]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm112 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(1,1),(2,0),(2,1)},{(-1,0),(-1,1),(-1,2),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0)},5⟩)
def qmeq_112 : qr 112 = qm112 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 112 = qv112 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 112 < 6 by decide,↓reduceDIte,he,qv112,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_93]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm113 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(0,-1),(1,0),(1,1),(2,1),(3,0)},{(-2,0),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)},4⟩)
def qmeq_113 : qr 113 = qm113 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 113 = qv113 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 113 < 6 by decide,↓reduceDIte,he,qv113,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_1,qmeq_36]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm114 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(-1,-1),(-1,0),(1,0),(1,1)},{(-3,1),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-2),(-1,-1),(-1,0),(0,0),(1,0),(1,1),(2,1)},5⟩)
def qmeq_114 : qr 114 = qm114 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 114 = qv114 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 114 < 6 by decide,↓reduceDIte,he,qv114,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_67]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm115 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-1),(-1,0),(1,0),(2,-1),(2,0)},{(-3,1),(-2,0),(-2,1),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(0,0),(1,0),(2,-1),(2,0),(3,-1)},5⟩)
def qmeq_115 : qr 115 = qm115 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 115 = qv115 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 115 < 6 by decide,↓reduceDIte,he,qv115,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_70]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm116 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,1),(-1,-2),(-1,-1),(-1,1),(0,-1),(0,1)},{(-3,1),(-2,1),(-1,-2),(-1,-1),(-1,1),(0,-1),(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0)},4⟩)
def qmeq_116 : qr 116 = qm116 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 116 = qv116 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 116 < 6 by decide,↓reduceDIte,he,qv116,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_24]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm117 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-3),(-1,-2),(-1,-1),(-1,0),(1,-1)},{(-2,-1),(-2,0),(-2,1),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,0),(0,1),(1,-1),(1,0),(2,-1),(2,0)},5⟩)
def qmeq_117 : qr 117 = qm117 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 117 = qv117 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 117 < 6 by decide,↓reduceDIte,he,qv117,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_100]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm118 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-4),(-1,-1),(0,-3),(0,-2),(0,-1)},{(-2,-1),(-1,-4),(-1,-3),(-1,-1),(-1,0),(0,-3),(0,-2),(0,-1),(0,0),(1,0),(1,1),(2,0),(3,0)},4⟩)
def qmeq_118 : qr 118 = qm118 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 118 = qv118 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 118 < 6 by decide,↓reduceDIte,he,qv118,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_61]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm119 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(-1,0),(1,0)},{(-3,-1),(-3,1),(-2,-1),(-2,0),(-2,1),(-1,0),(-1,1),(0,0),(1,0),(1,1),(2,0),(2,1),(3,1)},5⟩)
def qmeq_119 : qr 119 = qm119 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 119 = qv119 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 119 < 6 by decide,↓reduceDIte,he,qv119,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_55]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm120 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,-1),(-2,0),(-1,-1),(-1,0),(1,1)},{(-3,0),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0)},5⟩)
def qmeq_120 : qr 120 = qm120 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 120 = qv120 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 120 < 6 by decide,↓reduceDIte,he,qv120,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_58]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm121 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(-1,-1),(0,-4),(0,-3),(0,-2),(0,-1)},{(-1,-3),(-1,-2),(-1,-1),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-1),(1,0),(1,1)},4⟩)
def qmeq_121 : qr 121 = qm121 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 121 = qv121 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 121 < 6 by decide,↓reduceDIte,he,qv121,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_9]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm122 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-1),(1,0),(2,0),(3,0)},{(-1,-1),(-1,1),(0,-2),(0,-1),(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)},5⟩)
def qmeq_122 : qr 122 = qm122 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 122 = qv122 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 122 < 6 by decide,↓reduceDIte,he,qv122,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_105]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm123 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(-1,0),(1,0)},{(-3,-1),(-3,1),(-2,-1),(-2,0),(-2,1),(-1,0),(-1,1),(0,0),(1,-1),(1,0),(2,-1),(2,0),(3,-1)},6⟩)
def qmeq_123 : qr 123 = qm123 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 123 = qv123 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 123 < 6 by decide,↓reduceDIte,he,qv123,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_64]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm124 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-2),(-1,-1),(-1,0),(1,-1),(2,-1)},{(-2,0),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,0),(0,1),(1,-1),(1,0),(2,-1),(2,0),(3,-1),(4,-1)},4⟩)
def qmeq_124 : qr 124 = qm124 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 124 = qv124 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 124 < 6 by decide,↓reduceDIte,he,qv124,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_31]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm125 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-2,-1),(-2,1),(-1,-1),(-1,1),(1,0)},{(-3,-1),(-3,1),(-2,-1),(-2,1),(-1,-1),(-1,1),(0,-1),(0,0),(0,1),(1,0),(1,1),(2,0),(3,0)},4⟩)
def qmeq_125 : qr 125 = qm125 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 125 = qv125 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 125 < 6 by decide,↓reduceDIte,he,qv125,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_3,qmeq_31]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm126 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2)},{(0,-1),(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)},5⟩)
def qmeq_126 : qr 126 = qm126 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 126 = qv126 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 126 < 6 by decide,↓reduceDIte,he,qv126,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_46]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm127 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,0),(-3,-1),(-3,0),(-2,0),(-1,0)},{(-4,0),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,0),(-1,1),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1)},5⟩)
def qmeq_127 : qr 127 = qm127 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 127 = qv127 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 127 < 6 by decide,↓reduceDIte,he,qv127,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_44]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm128 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,1),(-1,0),(-1,1),(0,1),(1,1)},{(-4,1),(-3,1),(-2,1),(-1,0),(-1,1),(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)},5⟩)
def qmeq_128 : qr 128 = qm128 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 128 = qv128 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 128 < 6 by decide,↓reduceDIte,he,qv128,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_9,qmeq_57]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm129 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(-1,-1),(-1,0),(-1,1),(0,-1),(1,0),(2,0)},{(-2,1),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,0),(2,0)},5⟩)
def qmeq_129 : qr 129 = qm129 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 129 = qv129 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 129 < 6 by decide,↓reduceDIte,he,qv129,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_58]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm130 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-2),(-1,-1),(-1,0),(2,0)},{(-2,-1),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1)},6⟩)
def qmeq_130 : qr 130 = qm130 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 130 = qv130 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 130 < 6 by decide,↓reduceDIte,he,qv130,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_60]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm131 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(0,-4),(0,-3),(0,-2),(0,-1)},{(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1)},5⟩)
def qmeq_131 : qr 131 = qm131 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 131 = qv131 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 131 < 6 by decide,↓reduceDIte,he,qv131,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_45]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm132 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-3),(1,-2),(1,-1),(1,0),(1,1)},{(0,-2),(0,-1),(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)},5⟩)
def qmeq_132 : qr 132 = qm132 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 132 = qv132 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 132 < 6 by decide,↓reduceDIte,he,qv132,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_89]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm133 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-1,-2),(0,-2),(0,-1),(0,1)},{(-3,0),(-2,0),(-1,-3),(-1,-2),(-1,0),(0,-2),(0,-1),(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1)},5⟩)
def qmeq_133 : qr 133 = qm133 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 133 = qv133 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 133 < 6 by decide,↓reduceDIte,he,qv133,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_92]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm134 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-1),(0,-3),(0,-2),(0,-1)},{(-3,-1),(-2,-1),(-1,-4),(-1,-3),(-1,-1),(0,-3),(0,-2),(0,-1),(0,0),(1,-1),(1,0),(1,1),(2,0),(3,0)},5⟩)
def qmeq_134 : qr 134 = qm134 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 134 = qv134 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 134 < 6 by decide,↓reduceDIte,he,qv134,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_82]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm135 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,0),(-3,0),(-3,1),(-2,0),(-1,0)},{(-6,0),(-5,0),(-4,0),(-3,0),(-3,1),(-2,0),(-2,1),(-1,0),(-1,1),(0,0),(0,1),(1,0),(1,1),(2,1)},5⟩)
def qmeq_135 : qr 135 = qm135 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 135 = qv135 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 135 < 6 by decide,↓reduceDIte,he,qv135,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_44,qmeq_75]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm136 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,2),(0,-1),(0,1),(0,2)},{(-3,-1),(-2,-1),(-1,-2),(-1,-1),(-1,0),(-1,2),(-1,3),(0,-1),(0,0),(0,1),(0,2),(1,0),(2,0),(3,0)},5⟩)
def qmeq_136 : qr 136 = qm136 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 136 = qv136 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 136 < 6 by decide,↓reduceDIte,he,qv136,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_102]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm137 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-4),(-1,-3),(-1,-2),(-1,-1),(2,0)},{(-2,0),(-2,1),(-2,2),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(0,-1),(0,0),(0,1),(1,0),(2,0)},6⟩)
def qmeq_137 : qr 137 = qm137 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 137 = qv137 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 137 < 6 by decide,↓reduceDIte,he,qv137,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_96]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm138 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,2),(0,2)},{(-3,1),(-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),(-1,2),(0,0),(0,1),(0,2),(0,3),(1,0),(2,0)},4⟩)
def qmeq_138 : qr 138 = qm138 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 138 = qv138 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 138 < 6 by decide,↓reduceDIte,he,qv138,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_10,qmeq_27]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm139 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(0,2)},{(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0)},4⟩)
def qmeq_139 : qr 139 = qm139 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 139 = qv139 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 139 < 6 by decide,↓reduceDIte,he,qv139,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_27,qmeq_28]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm140 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(-1,1),(0,-1),(0,1),(0,2)},{(-3,1),(-2,1),(-1,-2),(-1,-1),(-1,1),(0,-1),(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,2)},5⟩)
def qmeq_140 : qr 140 = qm140 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 140 = qv140 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 140 < 6 by decide,↓reduceDIte,he,qv140,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_82]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm141 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-5,0),(-4,0),(-3,0),(-2,0),(-1,0)},{(-6,0),(-5,0),(-4,-1),(-4,0),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,0),(-1,1),(0,0),(0,1),(1,0),(1,1)},4⟩)
def qmeq_141 : qr 141 = qm141 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 141 = qv141 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 141 < 6 by decide,↓reduceDIte,he,qv141,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_78]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm142 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0),(-1,1),(-1,2)},{(-4,-1),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,0),(-1,1),(-1,2),(-1,3),(0,-1),(0,0),(1,-1),(1,0),(2,-1)},5⟩)
def qmeq_142 : qr 142 = qm142 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 142 = qv142 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 142 < 6 by decide,↓reduceDIte,he,qv142,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_32,qmeq_55,qmeq_72]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm143 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,1),(1,1),(2,1),(3,1)},{(-1,0),(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1),(5,2),(6,0),(6,2)},7⟩)
def qmeq_143 : qr 143 = qm143 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 143 = qv143 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 143 < 6 by decide,↓reduceDIte,he,qv143,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_108]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm144 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,0),(-3,0),(-2,0),(-1,0)},{(-6,0),(-5,0),(-4,0),(-4,1),(-3,0),(-3,1),(-2,0),(-2,1),(-1,0),(-1,1),(0,0),(0,1),(1,0),(1,1),(2,1)},6⟩)
def qmeq_144 : qr 144 = qm144 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 144 = qv144 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 144 < 6 by decide,↓reduceDIte,he,qv144,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_55,qmeq_104]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm145 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(1,-3),(1,-2),(3,-1)},{(-1,0),(-1,1),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(2,-1),(2,0),(3,-1)},6⟩)
def qmeq_145 : qr 145 = qm145 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 145 = qv145 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 145 < 6 by decide,↓reduceDIte,he,qv145,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_91]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm146 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-2),(-1,-1),(-1,0)},{(-4,-1),(-3,-1),(-2,-1),(-2,0),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(0,0),(0,1),(0,2),(0,3),(1,0),(2,0)},4⟩)
def qmeq_146 : qr 146 = qm146 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 146 = qv146 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 146 < 6 by decide,↓reduceDIte,he,qv146,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_24,qmeq_36]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm147 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-3,0),(-2,0),(-2,2),(-2,3),(-1,0)},{(-4,1),(-3,-1),(-3,0),(-3,1),(-3,2),(-2,-1),(-2,0),(-2,2),(-2,3),(-1,0),(0,-1),(0,0),(1,-1),(1,0),(2,-1)},5⟩)
def qmeq_147 : qr 147 = qm147 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 147 = qv147 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 147 < 6 by decide,↓reduceDIte,he,qv147,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_44,qmeq_53]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm148 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(0,-4),(0,-3),(0,-2),(0,-1),(1,-2)},{(-1,-3),(-1,-2),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3)},6⟩)
def qmeq_148 : qr 148 = qm148 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 148 = qv148 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 148 < 6 by decide,↓reduceDIte,he,qv148,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_46,qmeq_94,qmeq_97]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm149 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,1),(-1,-3),(-1,-2),(-1,-1),(-1,1),(0,1)},{(-3,1),(-2,1),(-1,-3),(-1,-2),(-1,-1),(-1,1),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0)},4⟩)
def qmeq_149 : qr 149 = qm149 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 149 = qv149 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 149 < 6 by decide,↓reduceDIte,he,qv149,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_16,qmeq_24]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm150 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-5,0),(-4,-1),(-4,0),(-3,0),(-2,0),(-1,0)},{(-5,0),(-4,-1),(-4,0),(-3,-1),(-3,0),(-3,1),(-2,0),(-2,1),(-1,0),(-1,1),(0,-1),(0,0),(1,-1),(1,0),(2,-1)},6⟩)
def qmeq_150 : qr 150 = qm150 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 150 = qv150 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 150 < 6 by decide,↓reduceDIte,he,qv150,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_126]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm151 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(1,0),(1,1),(2,-2),(2,0)},{(-1,0),(0,-3),(0,-2),(0,-1),(0,0),(1,0),(1,1),(2,-3),(2,-2),(2,-1),(2,0),(3,-1),(3,0),(4,-1),(5,-1)},5⟩)
def qmeq_151 : qr 151 = qm151 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 151 = qv151 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 151 < 6 by decide,↓reduceDIte,he,qv151,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_2,qmeq_101]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm152 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-3),(1,-2),(1,-1),(1,0),(2,0),(4,-1)},{(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(2,0),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,1)},6⟩)
def qmeq_152 : qr 152 = qm152 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 152 = qv152 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 152 < 6 by decide,↓reduceDIte,he,qv152,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_73]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm153 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0)},{(-5,0),(-4,0),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),(0,0),(0,1),(1,0),(1,1),(2,0)},5⟩)
def qmeq_153 : qr 153 = qm153 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 153 = qv153 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 153 < 6 by decide,↓reduceDIte,he,qv153,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_27,qmeq_59]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm154 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,0),(2,0),(3,0),(4,0)},{(-1,-1),(-1,0),(0,-1),(0,0),(1,-1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0)},6⟩)
def qmeq_154 : qr 154 = qm154 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 154 = qv154 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 154 < 6 by decide,↓reduceDIte,he,qv154,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_104]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm155 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-4),(0,-3),(0,-2),(0,-1)},{(-1,-4),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1)},5⟩)
def qmeq_155 : qr 155 = qm155 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 155 = qv155 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 155 < 6 by decide,↓reduceDIte,he,qv155,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_55]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm156 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-3,0),(-3,1),(-1,-1),(-1,0)},{(-4,-1),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,-1),(0,0),(1,-1),(1,0),(2,-1),(2,0)},6⟩)
def qmeq_156 : qr 156 = qm156 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 156 = qv156 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 156 < 6 by decide,↓reduceDIte,he,qv156,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_11,qmeq_33,qmeq_98]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm157 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-1),(1,-3),(1,-2),(1,-1),(1,0),(1,1)},{(0,-1),(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)},5⟩)
def qmeq_157 : qr 157 = qm157 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 157 = qv157 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 157 < 6 by decide,↓reduceDIte,he,qv157,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_57]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm158 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(1,-2),(2,-1),(3,-1)},{(-1,0),(-1,1),(-1,2),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-3),(1,-2),(1,0),(1,1),(1,2),(2,-1),(2,0),(3,-1)},5⟩)
def qmeq_158 : qr 158 = qm158 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 158 = qv158 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 158 < 6 by decide,↓reduceDIte,he,qv158,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_45,qmeq_46,qmeq_66]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm159 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(0,-4),(0,-3),(0,-2),(0,-1)},{(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,1),(1,2),(1,3)},6⟩)
def qmeq_159 : qr 159 = qm159 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 159 = qv159 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 159 < 6 by decide,↓reduceDIte,he,qv159,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_45,qmeq_65]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm160 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,0),(1,1),(1,2),(2,0),(3,0)},{(-1,-1),(0,-1),(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,1)},6⟩)
def qmeq_160 : qr 160 = qm160 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 160 = qv160 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 160 < 6 by decide,↓reduceDIte,he,qv160,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_32,qmeq_63]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm161 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(-1,-2),(-1,-1),(-1,0),(0,2)},{(-3,1),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-2),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,0),(2,0)},6⟩)
def qmeq_161 : qr 161 = qm161 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 161 = qv161 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 161 < 6 by decide,↓reduceDIte,he,qv161,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_15,qmeq_86]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm162 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(0,-4),(0,-3),(0,-2),(0,-1)},{(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,0),(1,1),(1,2)},6⟩)
def qmeq_162 : qr 162 = qm162 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 162 = qv162 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 162 < 6 by decide,↓reduceDIte,he,qv162,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_63,qmeq_127,qmeq_157]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm163 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-3,0),(-2,0),(-1,0)},{(-4,0),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,-1),(-1,0),(-1,1),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,1)},5⟩)
def qmeq_163 : qr 163 = qm163 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 163 = qv163 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 163 < 6 by decide,↓reduceDIte,he,qv163,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_44,qmeq_49,qmeq_56]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm164 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-2),(-1,-1),(-1,0),(2,0)},{(-2,-1),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,0),(0,1),(1,0),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,1)},7⟩)
def qmeq_164 : qr 164 = qm164 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 164 = qv164 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 164 < 6 by decide,↓reduceDIte,he,qv164,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_110]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm165 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,1),(1,1),(1,2),(1,3),(2,1)},{(-1,0),(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)},7⟩)
def qmeq_165 : qr 165 = qm165 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 165 = qv165 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 165 < 6 by decide,↓reduceDIte,he,qv165,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_107]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm166 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(-1,0),(0,2),(0,3),(1,0)},{(-2,-1),(-1,-1),(-1,0),(0,0),(0,1),(0,2),(0,3),(1,0),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,1)},7⟩)
def qmeq_166 : qr 166 = qm166 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 166 = qv166 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 166 < 6 by decide,↓reduceDIte,he,qv166,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_2,qmeq_107]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm167 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,-1),(-2,0),(-1,-1),(-1,0)},{(-5,0),(-5,1),(-4,0),(-4,1),(-3,0),(-3,1),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,0),(0,1),(1,0),(1,1),(2,0),(2,1)},5⟩)
def qmeq_167 : qr 167 = qm167 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 167 = qv167 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 167 < 6 by decide,↓reduceDIte,he,qv167,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_57]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm168 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(1,0),(3,-1)},{(-1,0),(-1,1),(0,-3),(0,-2),(0,-1),(0,0),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,1)},7⟩)
def qmeq_168 : qr 168 = qm168 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 168 = qv168 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 168 < 6 by decide,↓reduceDIte,he,qv168,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_152]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm169 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,2),(1,-1),(1,0),(2,0),(3,0)},{(-1,1),(0,0),(0,1),(0,2),(0,3),(1,-1),(1,0),(2,0),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,1)},6⟩)
def qmeq_169 : qr 169 = qm169 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 169 = qv169 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 169 < 6 by decide,↓reduceDIte,he,qv169,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_28,qmeq_63]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm170 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,-1),(-3,0),(-2,0),(-2,1),(-1,0)},{(-4,-1),(-3,-1),(-3,0),(-2,0),(-2,1),(-1,0),(-1,1),(0,-1),(0,0),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,1)},6⟩)
def qmeq_170 : qr 170 = qm170 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 170 = qv170 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 170 < 6 by decide,↓reduceDIte,he,qv170,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_127]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm171 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-2),(-3,-1),(-3,0),(-3,1),(-2,-1),(-1,-1),(0,-1)},{(-4,1),(-4,2),(-3,-2),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-2,2),(-1,-1),(-1,0),(-1,1),(0,-1),(0,0),(1,0)},6⟩)
def qmeq_171 : qr 171 = qm171 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 171 = qv171 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 171 < 6 by decide,↓reduceDIte,he,qv171,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_91]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm172 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0)},{(-5,-1),(-4,-1),(-4,0),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,1)},6⟩)
def qmeq_172 : qr 172 = qm172 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 172 = qv172 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 172 < 6 by decide,↓reduceDIte,he,qv172,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_63,qmeq_64]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm173 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0)},{(-5,-1),(-4,-1),(-4,0),(-3,-1),(-3,0),(-2,0),(-1,-1),(-1,0),(-1,1),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,1)},6⟩)
def qmeq_173 : qr 173 = qm173 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 173 = qv173 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 173 < 6 by decide,↓reduceDIte,he,qv173,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_63,qmeq_64]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm174 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(-1,-1),(0,-3),(0,-2),(0,-1)},{(-2,-1),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0)},6⟩)
def qmeq_174 : qr 174 = qm174 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 174 = qv174 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 174 < 6 by decide,↓reduceDIte,he,qv174,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_57,qmeq_58,qmeq_84]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm175 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,0),(-3,0),(-2,0),(-1,0)},{(-5,0),(-4,0),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1)},6⟩)
def qmeq_175 : qr 175 = qm175 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 175 = qv175 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 175 < 6 by decide,↓reduceDIte,he,qv175,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_63,qmeq_141]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm176 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0)},{(-5,-1),(-4,-1),(-4,0),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,0),(-1,1),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,1)},6⟩)
def qmeq_176 : qr 176 = qm176 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 176 = qv176 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 176 < 6 by decide,↓reduceDIte,he,qv176,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_63,qmeq_64]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm177 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-2),(-1,-1),(-1,0),(2,-2),(2,0)},{(-2,-1),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,0),(0,1),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-3),(2,-2),(2,-1),(2,0),(3,-1)},6⟩)
def qmeq_177 : qr 177 = qm177 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 177 = qv177 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 177 < 6 by decide,↓reduceDIte,he,qv177,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_136]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm178 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(1,-2),(2,-1),(3,-1)},{(-1,0),(-1,1),(-1,2),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-3),(1,-2),(1,-1),(1,1),(1,2),(1,3),(2,-1),(3,-1)},6⟩)
def qmeq_178 : qr 178 = qm178 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 178 = qv178 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 178 < 6 by decide,↓reduceDIte,he,qv178,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_37,qmeq_46,qmeq_68]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm179 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-3,0),(-2,0),(-1,-1),(-1,0),(-1,1)},{(-4,-1),(-3,-1),(-3,0),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),(0,-1),(0,0),(1,-1),(1,0),(2,-1),(2,0),(3,-1),(3,0),(4,-1)},7⟩)
def qmeq_179 : qr 179 = qm179 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 179 = qv179 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 179 < 6 by decide,↓reduceDIte,he,qv179,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_148]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm180 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-4),(0,-3),(0,-2),(0,-1)},{(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,0),(1,1),(1,2)},6⟩)
def qmeq_180 : qr 180 = qm180 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 180 = qv180 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 180 < 6 by decide,↓reduceDIte,he,qv180,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_63,qmeq_132,qmeq_155]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm181 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-2),(1,-1),(1,0),(2,1)},{(-2,0),(-1,0),(0,0),(0,1),(0,2),(0,3),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)},5⟩)
def qmeq_181 : qr 181 = qm181 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 181 = qv181 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 181 < 6 by decide,↓reduceDIte,he,qv181,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_24,qmeq_87,qmeq_90]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm182 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-1),(1,0),(1,1),(2,-1),(2,0),(3,2)},{(-1,0),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(3,-1),(3,0),(3,1),(3,2),(3,3),(4,-1),(4,0),(4,1),(5,0)},5⟩)
def qmeq_182 : qr 182 = qm182 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 182 = qv182 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 182 < 6 by decide,↓reduceDIte,he,qv182,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_12,qmeq_139]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm183 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0)},{(-5,-1),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-1,0),(0,-1),(0,0),(1,-1),(1,0),(2,-1)},6⟩)
def qmeq_183 : qr 183 = qm183 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 183 = qv183 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 183 < 6 by decide,↓reduceDIte,he,qv183,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_63,qmeq_64]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm184 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(1,-4),(1,-3),(2,-3),(2,-1),(2,0),(3,-3),(3,-1)},{(-1,-2),(-1,0),(0,-3),(0,-2),(0,-1),(0,0),(1,-4),(1,-3),(1,-1),(1,0),(2,-3),(2,-1),(2,0),(3,-3),(3,-1),(4,-1),(5,-1)},4⟩)
def qmeq_184 : qr 184 = qm184 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 184 = qv184 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 184 < 6 by decide,↓reduceDIte,he,qv184,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_34,qmeq_35]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm185 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-1),(0,-3),(0,-2),(0,-1)},{(-2,-1),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0)},6⟩)
def qmeq_185 : qr 185 = qm185 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 185 = qv185 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 185 < 6 by decide,↓reduceDIte,he,qv185,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_44,qmeq_49,qmeq_84]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm186 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,0),(-3,0),(-2,0),(-1,0)},{(-5,-1),(-5,0),(-4,-1),(-4,0),(-3,-1),(-3,0),(-3,1),(-2,0),(-2,1),(-1,0),(-1,1),(0,-1),(0,0),(1,-1),(1,0),(2,-1),(2,0)},5⟩)
def qmeq_186 : qr 186 = qm186 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 186 = qv186 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 186 < 6 by decide,↓reduceDIte,he,qv186,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_141]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm187 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-2),(0,-1),(1,-3),(1,-1),(2,-1),(3,-1)},{(-1,0),(-1,1),(-1,2),(-1,3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-3),(1,-2),(1,-1),(1,1),(1,2),(1,3),(2,-1),(3,-1)},7⟩)
def qmeq_187 : qr 187 = qm187 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 187 = qv187 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 187 < 6 by decide,↓reduceDIte,he,qv187,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_108]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm188 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-3),(1,-2),(1,-1),(1,0),(2,0),(3,-2),(4,-2),(4,-1)},{(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(2,0),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(4,-2),(4,-1),(4,0),(4,1),(5,1)},6⟩)
def qmeq_188 : qr 188 = qm188 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 188 = qv188 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 188 < 6 by decide,↓reduceDIte,he,qv188,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_112]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm189 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(-1,-1),(-1,0),(0,-1)},{(-4,0),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,-2),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0)},6⟩)
def qmeq_189 : qr 189 = qm189 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 189 = qv189 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 189 < 6 by decide,↓reduceDIte,he,qv189,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_12,qmeq_86]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm190 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,-1),(-2,0),(-1,0)},{(-4,0),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,-2),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-1),(1,0),(1,1),(2,0),(2,1)},7⟩)
def qmeq_190 : qr 190 = qm190 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 190 = qv190 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 190 < 6 by decide,↓reduceDIte,he,qv190,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_46,qmeq_85,qmeq_111]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm191 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-2),(0,-1),(1,-2),(1,-1),(2,-1),(3,-1),(3,0)},{(-1,0),(-1,1),(-1,2),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-1),(2,0),(2,1),(3,-1),(3,0)},7⟩)
def qmeq_191 : qr 191 = qm191 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 191 = qv191 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 191 < 6 by decide,↓reduceDIte,he,qv191,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_145]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm192 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(2,-1)},{(-2,0),(-1,-4),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(1,2),(2,-1),(3,-1)},6⟩)
def qmeq_192 : qr 192 = qm192 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 192 = qv192 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 192 < 6 by decide,↓reduceDIte,he,qv192,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_64,qmeq_103]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm193 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(-1,0),(1,-1),(1,0),(2,0)},{(-2,-1),(-1,-1),(-1,0),(0,0),(1,-1),(1,0),(2,-1),(2,0),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1),(6,-1)},7⟩)
def qmeq_193 : qr 193 = qm193 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 193 = qv193 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 193 < 6 by decide,↓reduceDIte,he,qv193,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_162]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm194 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-2,-1),(-1,-1),(-1,0),(-1,1)},{(-4,-1),(-4,1),(-3,-1),(-3,1),(-2,-1),(-2,1),(-2,2),(-2,3),(-2,4),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(0,0),(0,1),(1,0),(2,0)},5⟩)
def qmeq_194 : qr 194 = qm194 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 194 = qv194 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 194 < 6 by decide,↓reduceDIte,he,qv194,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_146]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm195 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-3,0),(-2,0),(-1,-1),(-1,0)},{(-4,-1),(-3,-1),(-3,0),(-2,0),(-1,-1),(-1,0),(0,-1),(0,0),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1)},7⟩)
def qmeq_195 : qr 195 = qm195 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 195 = qv195 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 195 < 6 by decide,↓reduceDIte,he,qv195,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_162]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm196 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(1,-3),(1,-2),(1,-1),(1,0)},{(-1,-1),(0,-1),(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,1)},8⟩)
def qmeq_196 : qr 196 = qm196 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 196 = qv196 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 196 < 6 by decide,↓reduceDIte,he,qv196,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_187]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm197 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0)},{(-5,-1),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,0),(-1,0),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,1)},6⟩)
def qmeq_197 : qr 197 = qm197 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 197 = qv197 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 197 < 6 by decide,↓reduceDIte,he,qv197,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_63]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm198 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,0),(-3,0),(-2,0),(-1,-1),(-1,0)},{(-5,1),(-4,0),(-4,1),(-3,0),(-3,1),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1)},6⟩)
def qmeq_198 : qr 198 = qm198 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 198 = qv198 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 198 < 6 by decide,↓reduceDIte,he,qv198,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_131]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm199 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(0,-3),(0,-2),(0,-1)},{(-2,-1),(-1,-1),(-1,0),(-1,1),(-1,2),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-4),(1,-3),(1,-2),(1,0),(1,1),(1,2),(2,0),(3,0)},6⟩)
def qmeq_199 : qr 199 = qm199 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 199 = qv199 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 199 < 6 by decide,↓reduceDIte,he,qv199,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_64,qmeq_84]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm200 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(2,-1)},{(-2,0),(-1,0),(-1,1),(-1,2),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-1),(3,-1)},6⟩)
def qmeq_200 : qr 200 = qm200 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 200 = qv200 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 200 < 6 by decide,↓reduceDIte,he,qv200,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_64,qmeq_103]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm201 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-2),(1,-1),(1,0),(1,1),(1,2)},{(-2,0),(-1,0),(0,-1),(0,0),(0,2),(0,3),(0,4),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)},5⟩)
def qmeq_201 : qr 201 = qm201 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 201 = qv201 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 201 < 6 by decide,↓reduceDIte,he,qv201,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_45,qmeq_82]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm202 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,0),(-3,-1),(-3,0),(-2,0),(-1,0)},{(-4,0),(-3,-1),(-3,0),(-2,-1),(-2,0),(-2,1),(-1,0),(-1,1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,1)},7⟩)
def qmeq_202 : qr 202 = qm202 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 202 = qv202 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 202 < 6 by decide,↓reduceDIte,he,qv202,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_108,qmeq_150]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm203 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,-1),(-2,-1),(-2,0),(-1,0)},{(-4,-1),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,1)},7⟩)
def qmeq_203 : qr 203 = qm203 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 203 = qv203 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 203 < 6 by decide,↓reduceDIte,he,qv203,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_18,qmeq_107,qmeq_163]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm204 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-1),(1,-4),(1,-3),(2,-1)},{(-1,0),(0,-3),(0,-2),(0,-1),(0,0),(1,-4),(1,-3),(1,-2),(1,-1),(2,-1),(3,-2),(3,-1),(3,0),(4,-2),(4,-1),(4,0),(5,-2),(5,0)},8⟩)
def qmeq_204 : qr 204 = qm204 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 204 = qv204 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 204 < 6 by decide,↓reduceDIte,he,qv204,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_2,qmeq_166]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm205 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-4),(-1,-3),(-1,-2),(-1,-1),(2,-1)},{(-2,0),(-2,1),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,1)},8⟩)
def qmeq_205 : qr 205 = qm205 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 205 = qv205 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 205 < 6 by decide,↓reduceDIte,he,qv205,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_168]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm206 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,2),(1,-1),(1,0),(2,0),(3,0)},{(-2,0),(-1,0),(-1,1),(0,0),(0,1),(0,2),(0,3),(1,-1),(1,0),(2,-1),(2,0),(3,-1),(3,0),(4,-1),(4,0),(5,-1),(5,0),(6,-1)},6⟩)
def qmeq_206 : qr 206 = qm206 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 206 = qv206 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 206 < 6 by decide,↓reduceDIte,he,qv206,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_28,qmeq_135]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm207 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,2),(1,-1),(1,0),(2,0),(3,0)},{(-1,1),(0,0),(0,1),(0,2),(0,3),(1,-1),(1,0),(2,-1),(2,0),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1),(6,-1)},6⟩)
def qmeq_207 : qr 207 = qm207 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 207 = qv207 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 207 < 6 by decide,↓reduceDIte,he,qv207,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_28,qmeq_127]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm208 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,0),(-3,0),(-2,-1),(-2,0),(-1,0)},{(-5,1),(-4,0),(-4,1),(-3,0),(-3,1),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1)},6⟩)
def qmeq_208 : qr 208 = qm208 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 208 = qv208 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 208 < 6 by decide,↓reduceDIte,he,qv208,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_127]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm209 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,2),(-2,-1),(-2,2),(-1,-1),(-1,2),(0,-1),(0,2)},{(-3,-1),(-3,2),(-2,-1),(-2,2),(-1,-1),(-1,0),(-1,2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(3,0)},5⟩)
def qmeq_209 : qr 209 = qm209 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 209 = qv209 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 209 < 6 by decide,↓reduceDIte,he,qv209,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_25,qmeq_81]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm210 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,-1),(-2,0),(-1,-1),(-1,0),(-1,2)},{(-3,0),(-2,-1),(-2,0),(-1,-1),(-1,0),(-1,2),(-1,3),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1)},6⟩)
def qmeq_210 : qr 210 = qm210 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 210 = qv210 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 210 < 6 by decide,↓reduceDIte,he,qv210,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_57,qmeq_58,qmeq_117]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm211 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-3,0),(-3,1),(-2,0),(-1,0)},{(-4,-1),(-3,-1),(-3,0),(-3,1),(-2,0),(-2,1),(-1,0),(0,-1),(0,0),(1,-1),(1,0),(2,-1)},5⟩)
def qmeq_211 : qr 211 = qm211 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 211 = qv211 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 211 < 6 by decide,↓reduceDIte,he,qv211,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_49]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm212 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-2),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,1),(-1,-1),(0,-1)},{(-4,1),(-4,2),(-3,-2),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,1),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(0,-1),(0,0),(0,1),(0,2),(1,0),(1,2)},7⟩)
def qmeq_212 : qr 212 = qm212 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 212 = qv212 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 212 < 6 by decide,↓reduceDIte,he,qv212,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_188]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm213 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(-1,0),(0,-1),(1,0),(2,0),(2,1)},{(-2,1),(-2,2),(-2,3),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)},8⟩)
def qmeq_213 : qr 213 = qm213 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 213 = qv213 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 213 < 6 by decide,↓reduceDIte,he,qv213,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_191]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm214 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-4),(0,-3),(0,-2),(0,-1),(1,-3),(3,-2)},{(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-3),(1,-2),(1,1),(1,2),(1,3),(2,-2),(3,-2)},7⟩)
def qmeq_214 : qr 214 = qm214 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 214 = qv214 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 214 < 6 by decide,↓reduceDIte,he,qv214,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_95,qmeq_108]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm215 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-1),(0,-1),(0,1)},{(-3,-1),(-2,-1),(-1,-2),(-1,-1),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-1),(1,0),(1,2),(1,3),(1,4),(2,0),(3,0)},7⟩)
def qmeq_215 : qr 215 = qm215 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 215 = qv215 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 215 < 6 by decide,↓reduceDIte,he,qv215,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_24,qmeq_107]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm216 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,0),(-3,0),(-2,0),(-1,0)},{(-5,-1),(-4,-1),(-4,0),(-3,-1),(-3,0),(-3,1),(-2,0),(-2,1),(-1,0),(-1,1),(0,-1),(0,0),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,1)},6⟩)
def qmeq_216 : qr 216 = qm216 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 216 = qv216 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 216 < 6 by decide,↓reduceDIte,he,qv216,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_155]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm217 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0)},{(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-2,-2),(-2,-1),(-2,0),(-1,0),(-1,1),(0,0),(0,1),(1,0),(1,1),(2,1)},7⟩)
def qmeq_217 : qr 217 = qm217 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 217 = qv217 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 217 < 6 by decide,↓reduceDIte,he,qv217,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_64,qmeq_111]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm218 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(-1,0),(-1,1),(-1,2),(0,-1),(1,2)},{(-3,0),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-1),(0,0),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-1),(2,0),(2,1),(3,0)},6⟩)
def qmeq_218 : qr 218 = qm218 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 218 = qv218 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 218 < 6 by decide,↓reduceDIte,he,qv218,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_182]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm219 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0),(-1,1),(-1,2),(0,-1),(1,-1),(1,0),(1,1)},{(-2,1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-1),(0,0),(1,-1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)},8⟩)
def qmeq_219 : qr 219 = qm219 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 219 = qv219 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 219 < 6 by decide,↓reduceDIte,he,qv219,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_179]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm220 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0)},{(-5,0),(-4,0),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,-1),(-1,0),(-1,1),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1)},7⟩)
def qmeq_220 : qr 220 = qm220 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 220 = qv220 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 220 < 6 by decide,↓reduceDIte,he,qv220,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_56,qmeq_63,qmeq_144,qmeq_154,qmeq_155]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm221 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-3,0),(-2,0),(-1,0)},{(-4,-1),(-3,-1),(-3,0),(-2,0),(-2,1),(-1,0),(-1,1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,1)},7⟩)
def qmeq_221 : qr 221 = qm221 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 221 = qv221 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 221 < 6 by decide,↓reduceDIte,he,qv221,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_180]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm222 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-3),(0,-2)},{(-2,-1),(-2,0),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-3),(0,-2),(0,0),(0,1),(1,-2),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,1)},6⟩)
def qmeq_222 : qr 222 = qm222 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 222 = qv222 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 222 < 6 by decide,↓reduceDIte,he,qv222,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_158]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm223 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,-1),(-2,0),(-1,0)},{(-5,0),(-4,0),(-3,0),(-2,-1),(-2,0),(-1,-2),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1)},7⟩)
def qmeq_223 : qr 223 = qm223 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 223 = qv223 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 223 < 6 by decide,↓reduceDIte,he,qv223,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_63,qmeq_111,qmeq_127,qmeq_128,qmeq_135]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm224 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-2),(1,-2),(2,-2)},{(-2,0),(-2,1),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-2),(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(2,-2),(2,-1),(2,0),(2,1),(3,-1),(3,1)},8⟩)
def qmeq_224 : qr 224 = qm224 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 224 = qv224 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 224 < 6 by decide,↓reduceDIte,he,qv224,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_212]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm225 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-2),(1,-1),(1,0),(2,0),(3,0)},{(-1,0),(-1,1),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-2),(1,-1),(1,0),(2,0),(2,1),(2,2),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(4,-1),(4,1)},7⟩)
def qmeq_225 : qr 225 = qm225 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 225 = qv225 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 225 < 6 by decide,↓reduceDIte,he,qv225,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_61,qmeq_111]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm226 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-3,0),(-1,-1),(-1,0)},{(-4,-1),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,-1),(0,0),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,1)},8⟩)
def qmeq_226 : qr 226 = qm226 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 226 = qv226 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 226 < 6 by decide,↓reduceDIte,he,qv226,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_10,qmeq_33,qmeq_193,qmeq_203]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm227 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(1,-2),(1,0),(2,-2),(3,-2)},{(-1,0),(-1,1),(0,-3),(0,-2),(0,-1),(0,0),(1,-2),(1,0),(1,1),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(3,-2),(3,-1),(3,0),(3,1),(4,-1),(4,1)},8⟩)
def qmeq_227 : qr 227 = qm227 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 227 = qv227 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 227 < 6 by decide,↓reduceDIte,he,qv227,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_212]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm228 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-2),(1,-1),(1,0),(1,1),(1,2)},{(-2,0),(-1,0),(0,-1),(0,0),(0,1),(0,3),(0,4),(0,5),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1)},6⟩)
def qmeq_228 : qr 228 = qm228 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 228 = qv228 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 228 < 6 by decide,↓reduceDIte,he,qv228,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_68,qmeq_82]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm229 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(1,-2),(2,-2),(3,-2)},{(-1,0),(-1,1),(-1,2),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-2),(2,-1),(2,0),(3,-2),(3,-1),(4,-1)},7⟩)
def qmeq_229 : qr 229 = qm229 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 229 = qv229 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 229 < 6 by decide,↓reduceDIte,he,qv229,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_45,qmeq_46,qmeq_171]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm230 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,1),(2,0),(2,1),(3,1)},{(-1,0),(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1),(5,2),(6,0),(6,1),(6,2),(7,0),(7,2)},8⟩)
def qmeq_230 : qr 230 = qm230 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 230 = qv230 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 230 < 6 by decide,↓reduceDIte,he,qv230,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_10,qmeq_33,qmeq_193,qmeq_203]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm231 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-3),(1,-2),(1,-1),(1,0),(2,-3),(2,-2)},{(0,-1),(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(2,-3),(2,-2),(2,0),(2,1),(3,-2),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,1)},7⟩)
def qmeq_231 : qr 231 = qm231 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 231 = qv231 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 231 < 6 by decide,↓reduceDIte,he,qv231,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_222]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm232 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,1),(-1,-1),(-1,1),(0,-1),(0,1)},{(-3,1),(-2,1),(-1,-2),(-1,-1),(-1,1),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)},7⟩)
def qmeq_232 : qr 232 = qm232 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 232 = qv232 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 232 < 6 by decide,↓reduceDIte,he,qv232,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_24,qmeq_107]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm233 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(0,-2),(0,-1),(1,-2),(2,-2),(2,-1),(2,1)},{(-2,-3),(-1,-3),(-1,-2),(-1,0),(0,-2),(0,-1),(0,0),(0,1),(1,-3),(1,-2),(1,0),(2,-2),(2,-1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)},6⟩)
def qmeq_233 : qr 233 = qm233 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 233 = qv233 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 233 < 6 by decide,↓reduceDIte,he,qv233,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_32,qmeq_133]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm234 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(1,-2),(2,-1),(3,-1)},{(-1,0),(-1,1),(-1,2),(-1,3),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(3,-1)},7⟩)
def qmeq_234 : qr 234 = qm234 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 234 = qv234 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 234 < 6 by decide,↓reduceDIte,he,qv234,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_37,qmeq_63,qmeq_129,qmeq_180]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm235 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-4),(0,-3),(0,-2),(0,-1),(1,0),(3,0)},{(-1,-1),(-1,0),(-1,1),(-1,2),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,0),(2,0),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,1)},7⟩)
def qmeq_235 : qr 235 = qm235 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 235 = qv235 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 235 < 6 by decide,↓reduceDIte,he,qv235,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_70,qmeq_110]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm236 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-2),(-1,-1)},{(-4,-1),(-3,-1),(-2,-1),(-2,0),(-2,1),(-2,2),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-1),(1,0),(2,0),(3,0)},6⟩)
def qmeq_236 : qr 236 = qm236 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 236 = qv236 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 236 < 6 by decide,↓reduceDIte,he,qv236,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_30,qmeq_38,qmeq_122,qmeq_181]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm237 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-3),(1,-2),(1,-1),(1,0),(2,0)},{(-2,-1),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(2,-1),(2,0),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,1)},7⟩)
def qmeq_237 : qr 237 = qm237 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 237 = qv237 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 237 < 6 by decide,↓reduceDIte,he,qv237,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_172]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm238 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-3),(1,-2),(1,-1),(1,0),(2,-3),(2,-2),(2,0)},{(0,-1),(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(2,-3),(2,-2),(2,-1),(2,0),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1),(6,-1)},7⟩)
def qmeq_238 : qr 238 = qm238 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 238 = qv238 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 238 < 6 by decide,↓reduceDIte,he,qv238,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_178]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm239 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(-1,-1),(-1,0),(0,-1),(1,-1),(2,-1)},{(-4,1),(-3,1),(-2,1),(-2,2),(-2,3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-1),(1,0),(2,-1),(3,-1)},7⟩)
def qmeq_239 : qr 239 = qm239 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 239 = qv239 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 239 < 6 by decide,↓reduceDIte,he,qv239,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_174]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm240 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-2),(-1,-1),(-1,0)},{(-4,-1),(-3,-1),(-3,0),(-2,-1),(-2,0),(-2,1),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,1)},8⟩)
def qmeq_240 : qr 240 = qm240 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 240 = qv240 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 240 < 6 by decide,↓reduceDIte,he,qv240,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_237]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm241 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,-2),(-1,-1),(-1,0)},{(-3,0),(-2,-1),(-2,0),(-1,-2),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,1)},7⟩)
def qmeq_241 : qr 241 = qm241 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 241 = qv241 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 241 < 6 by decide,↓reduceDIte,he,qv241,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_61,qmeq_131,qmeq_159]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm242 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-1,-3),(-1,-2),(-1,-1),(-1,0)},{(-3,0),(-2,-1),(-2,0),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-2),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-1),(2,0),(2,1),(3,0),(3,1)},8⟩)
def qmeq_242 : qr 242 = qm242 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 242 = qv242 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 242 < 6 by decide,↓reduceDIte,he,qv242,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_190]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm243 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-2,-1),(-2,0),(-1,-1),(0,-1),(0,2)},{(-4,-2),(-3,-2),(-3,-1),(-3,1),(-2,-1),(-2,0),(-2,1),(-2,2),(-1,-2),(-1,-1),(-1,1),(0,-1),(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)},7⟩)
def qmeq_243 : qr 243 = qm243 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 243 = qv243 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 243 < 6 by decide,↓reduceDIte,he,qv243,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_233]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm244 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-1,-3),(-1,-2),(-1,0)},{(-5,1),(-4,1),(-3,0),(-3,1),(-2,0),(-2,1),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,1)},7⟩)
def qmeq_244 : qr 244 = qm244 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 244 = qv244 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 244 < 6 by decide,↓reduceDIte,he,qv244,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_11,qmeq_99,qmeq_173]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm245 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0)},{(-6,-1),(-6,0),(-6,1),(-5,-1),(-5,0),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,-1),(-1,0),(-1,1),(0,0),(0,1),(1,0),(1,1),(2,1)},8⟩)
def qmeq_245 : qr 245 = qm245 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 245 = qv245 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 245 < 6 by decide,↓reduceDIte,he,qv245,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_64,qmeq_143,qmeq_175,qmeq_186]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm246 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0)},{(-5,-1),(-4,-1),(-4,0),(-3,-1),(-3,0),(-2,-1),(-2,0),(-2,1),(-1,0),(-1,1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1)},8⟩)
def qmeq_246 : qr 246 = qm246 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 246 = qv246 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 246 < 6 by decide,↓reduceDIte,he,qv246,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_64,qmeq_143,qmeq_175,qmeq_186]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm247 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-2),(0,-1),(1,-1),(2,-1),(3,-1)},{(-1,0),(-1,1),(-1,2),(-1,3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-1),(2,0),(2,1),(3,-1),(3,0),(4,0)},8⟩)
def qmeq_247 : qr 247 = qm247 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 247 = qv247 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 247 < 6 by decide,↓reduceDIte,he,qv247,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_229]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm248 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0),(1,0),(2,0)},{(-3,-1),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1)},8⟩)
def qmeq_248 : qr 248 = qm248 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 248 = qv248 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 248 < 6 by decide,↓reduceDIte,he,qv248,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_64,qmeq_143,qmeq_175,qmeq_186]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm249 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-2),(-1,-3),(-1,-2),(0,-2),(0,-1)},{(-3,0),(-2,-2),(-2,0),(-1,-3),(-1,-2),(-1,0),(-1,1),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-4),(1,-3),(1,-1),(1,0),(1,1),(2,-3),(2,-1),(3,-3)},8⟩)
def qmeq_249 : qr 249 = qm249 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 249 = qv249 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 249 < 6 by decide,↓reduceDIte,he,qv249,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_225]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm250 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-3),(0,-2)},{(-2,-1),(-2,0),(-2,1),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1)},8⟩)
def qmeq_250 : qr 250 = qm250 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 250 = qv250 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 250 < 6 by decide,↓reduceDIte,he,qv250,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_238]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm251 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,1),(-2,1),(-1,1),(0,1),(0,2)},{(-4,1),(-3,1),(-2,1),(-2,2),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(1,5),(2,3),(3,3)},8⟩)
def qmeq_251 : qr 251 = qm251 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 251 = qv251 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 251 < 6 by decide,↓reduceDIte,he,qv251,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_239]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm252 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0)},{(-5,0),(-4,0),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,-2),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1)},7⟩)
def qmeq_252 : qr 252 = qm252 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 252 = qv252 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 252 < 6 by decide,↓reduceDIte,he,qv252,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_63,qmeq_111,qmeq_144,qmeq_154,qmeq_155]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm253 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(0,-3),(0,-2),(1,-3),(2,-3),(2,0)},{(-2,-4),(-1,-4),(-1,-3),(-1,0),(0,-3),(0,-2),(0,-1),(0,0),(1,-4),(1,-3),(1,-1),(1,0),(1,1),(2,-3),(2,-2),(2,-1),(2,0),(3,-2),(3,-1),(4,-1),(5,-1)},7⟩)
def qmeq_253 : qr 253 = qm253 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 253 = qv253 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 253 < 6 by decide,↓reduceDIte,he,qv253,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_29,qmeq_177]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm254 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-2),(1,1),(2,1),(3,1)},{(-2,2),(-1,0),(-1,1),(-1,2),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1),(5,2),(6,0),(6,2)},7⟩)
def qmeq_254 : qr 254 = qm254 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 254 = qv254 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 254 < 6 by decide,↓reduceDIte,he,qv254,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_96,qmeq_108]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm255 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-4),(0,-3),(0,-2),(0,-1),(3,0)},{(-1,-1),(-1,0),(-1,1),(-1,2),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)},9⟩)
def qmeq_255 : qr 255 = qm255 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 255 = qv255 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 255 < 6 by decide,↓reduceDIte,he,qv255,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_69,qmeq_205]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm256 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(1,-3),(1,-2)},{(-1,-1),(-1,0),(-1,1),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-3),(1,-2),(1,0),(1,1),(2,-2),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,1)},8⟩)
def qmeq_256 : qr 256 = qm256 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 256 = qv256 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 256 < 6 by decide,↓reduceDIte,he,qv256,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_231]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm257 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(1,1),(3,1)},{(-1,0),(-1,1),(-1,2),(-1,3),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)},8⟩)
def qmeq_257 : qr 257 = qm257 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 257 = qv257 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 257 < 6 by decide,↓reduceDIte,he,qv257,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_235]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm258 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-2),(0,-1),(1,-1),(1,1),(2,-1),(3,-1)},{(-1,0),(-1,1),(-1,2),(0,-2),(0,-1),(0,0),(0,1),(1,-1),(1,1),(1,2),(2,-2),(2,-1),(2,0),(2,1),(2,2),(3,-1),(3,0),(3,1),(3,2),(4,0),(4,2)},9⟩)
def qmeq_258 : qr 258 = qm258 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 258 = qv258 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 258 < 6 by decide,↓reduceDIte,he,qv258,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_227]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm259 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-1),(1,-1),(1,0),(2,-1),(3,-1)},{(-1,0),(0,-1),(0,0),(1,-1),(1,0),(1,1),(2,-2),(2,-1),(2,1),(2,2),(2,3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(4,-2),(4,0),(4,1),(4,2),(4,3)},8⟩)
def qmeq_259 : qr 259 = qm259 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 259 = qv259 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 259 < 6 by decide,↓reduceDIte,he,qv259,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_231]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm260 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-2),(0,-1),(0,1),(1,-2),(1,-1)},{(-1,0),(-1,1),(-1,2),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-2),(1,-1),(1,1),(1,2),(2,-1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)},8⟩)
def qmeq_260 : qr 260 = qm260 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 260 = qv260 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 260 < 6 by decide,↓reduceDIte,he,qv260,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_231]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm261 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-3),(1,-2),(1,-1),(1,0)},{(-1,0),(0,-1),(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(2,-2),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(3,2),(3,3),(4,-1),(4,0),(4,1),(5,0),(5,1)},9⟩)
def qmeq_261 : qr 261 = qm261 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 261 = qv261 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 261 < 6 by decide,↓reduceDIte,he,qv261,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_242]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm262 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(-1,-1),(0,-1),(1,0),(1,1),(1,2)},{(-3,1),(-3,2),(-3,3),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-1),(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1)},9⟩)
def qmeq_262 : qr 262 = qm262 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 262 = qv262 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 262 < 6 by decide,↓reduceDIte,he,qv262,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_213]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm263 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0)},{(-6,-1),(-5,-1),(-5,0),(-4,-1),(-4,0),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,-1),(0,0),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1)},8⟩)
def qmeq_263 : qr 263 = qm263 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 263 = qv263 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 263 < 6 by decide,↓reduceDIte,he,qv263,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_143,qmeq_144,qmeq_175]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm264 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-1),(1,-1),(1,0),(2,-1),(3,-1)},{(-1,0),(0,-1),(0,0),(1,-1),(1,0),(2,-2),(2,-1),(2,0),(2,2),(2,3),(2,4),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(4,-2),(4,0),(4,1),(4,2),(4,3)},9⟩)
def qmeq_264 : qr 264 = qm264 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 264 = qv264 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 264 < 6 by decide,↓reduceDIte,he,qv264,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_250]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm265 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,1),(1,1),(2,1),(3,1)},{(-1,0),(-1,2),(-1,3),(-1,4),(-1,5),(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)},9⟩)
def qmeq_265 : qr 265 = qm265 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 265 = qv265 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 265 < 6 by decide,↓reduceDIte,he,qv265,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_247]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm266 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0),(0,-3),(0,-2),(0,-1)},{(-2,0),(-1,-1),(-1,0),(-1,1),(0,-3),(0,-2),(0,-1),(0,0),(1,-2),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-1),(3,0),(3,1),(4,0),(4,1)},9⟩)
def qmeq_266 : qr 266 = qm266 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 266 = qv266 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 266 < 6 by decide,↓reduceDIte,he,qv266,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_242]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm267 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-1,0),(1,0)},{(-5,-1),(-5,0),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,-1),(0,0),(1,-1),(1,0),(2,-1),(2,0),(3,-1),(3,0),(4,-1)},8⟩)
def qmeq_267 : qr 267 = qm267 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 267 = qv267 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 267 < 6 by decide,↓reduceDIte,he,qv267,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_143,qmeq_144,qmeq_175]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm268 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-2,-1),(-1,-1),(0,-1)},{(-4,-1),(-3,-1),(-2,-1),(-2,0),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)},9⟩)
def qmeq_268 : qr 268 = qm268 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 268 = qv268 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 268 < 6 by decide,↓reduceDIte,he,qv268,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_251]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm269 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,1),(-1,3),(0,1),(1,1),(2,1)},{(-2,2),(-1,1),(-1,2),(-1,3),(-1,4),(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1),(5,2),(6,0),(6,2)},8⟩)
def qmeq_269 : qr 269 = qm269 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 269 = qv269 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 269 < 6 by decide,↓reduceDIte,he,qv269,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_28,qmeq_202]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm270 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(0,-1),(0,1),(0,2)},{(-1,-2),(-1,-1),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4)},6⟩)
def qmeq_270 : qr 270 = qm270 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 270 = qv270 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 270 < 6 by decide,↓reduceDIte,he,qv270,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_63]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm271 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-1),(0,1),(1,-1),(2,-1)},{(-1,0),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-2),(1,-1),(1,2),(1,3),(1,4),(2,-1),(3,-2),(3,-1),(3,0),(4,-2),(4,-1),(4,0),(5,-2),(5,0)},7⟩)
def qmeq_271 : qr 271 = qm271 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 271 = qv271 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 271 < 6 by decide,↓reduceDIte,he,qv271,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_107]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm272 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-4),(-1,-2),(-1,-1),(0,-1)},{(-3,1),(-2,-1),(-2,1),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,1),(-1,2),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-3),(1,-2),(1,0),(1,1),(1,2),(2,-2),(2,0),(3,-2)},9⟩)
def qmeq_272 : qr 272 = qm272 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 272 = qv272 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 272 < 6 by decide,↓reduceDIte,he,qv272,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_1,qmeq_249]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm273 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-1,-3),(-1,-2),(-1,-1),(-1,0)},{(-4,0),(-3,0),(-2,0),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-2),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1)},8⟩)
def qmeq_273 : qr 273 = qm273 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 273 = qv273 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 273 < 6 by decide,↓reduceDIte,he,qv273,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_223]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm274 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(0,-2),(0,-1),(0,1)},{(-3,0),(-2,0),(-2,1),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(0,-2),(0,-1),(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)},9⟩)
def qmeq_274 : qr 274 = qm274 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 274 = qv274 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 274 < 6 by decide,↓reduceDIte,he,qv274,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_240]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm275 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-3,0),(-2,0),(-1,0)},{(-7,-1),(-6,-1),(-6,0),(-6,1),(-5,-1),(-5,0),(-5,1),(-4,0),(-4,1),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,0),(-1,1),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,1)},7⟩)
def qmeq_275 : qr 275 = qm275 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 275 = qv275 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 275 < 6 by decide,↓reduceDIte,he,qv275,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_44,qmeq_63,qmeq_198]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm276 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-4),(0,-3),(0,-2),(0,-1),(3,-2),(3,0)},{(-1,-1),(-1,0),(-1,1),(-1,2),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,0),(1,1),(1,2),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-3),(3,-2),(3,-1),(3,0),(4,-1)},7⟩)
def qmeq_276 : qr 276 = qm276 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 276 = qv276 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 276 < 6 by decide,↓reduceDIte,he,qv276,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_63,qmeq_177]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm277 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-1),(0,-1),(1,-3),(1,-2),(1,-1)},{(-2,-4),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-3),(1,-2),(1,-1),(2,-4),(2,-3),(2,-2),(3,-4),(3,-3),(3,-2),(4,-4),(4,-2)},9⟩)
def qmeq_277 : qr 277 = qm277 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 277 = qv277 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 277 < 6 by decide,↓reduceDIte,he,qv277,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_14,qmeq_33,qmeq_204]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm278 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,0),(2,-1),(2,0),(3,0)},{(-2,-1),(-2,1),(-1,-1),(-1,0),(-1,1),(0,-1),(0,0),(0,1),(1,0),(2,-1),(2,0),(3,-1),(3,0),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1),(6,-1),(6,0),(6,1),(7,-1)},7⟩)
def qmeq_278 : qr 278 = qm278 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 278 = qv278 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 278 < 6 by decide,↓reduceDIte,he,qv278,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_63,qmeq_162]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm279 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-3),(1,-2),(1,-1),(1,0),(2,-3),(2,-2),(2,0)},{(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(2,-3),(2,-2),(2,-1),(2,0),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1),(6,-1),(6,0),(6,1),(7,-1)},8⟩)
def qmeq_279 : qr 279 = qm279 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 279 = qv279 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 279 < 6 by decide,↓reduceDIte,he,qv279,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_234]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm280 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-2),(-2,-3),(-2,-2),(-1,-2),(-1,0),(-1,1),(0,-2)},{(-4,-1),(-4,1),(-3,-2),(-3,-1),(-3,0),(-3,1),(-2,-3),(-2,-2),(-2,0),(-2,1),(-1,-2),(-1,0),(-1,1),(0,-3),(0,-2),(0,-1),(0,0),(1,-2),(1,-1),(1,0),(2,-1),(2,0),(3,-1)},5⟩)
def qmeq_280 : qr 280 = qm280 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 280 = qv280 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 280 < 6 by decide,↓reduceDIte,he,qv280,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_116,qmeq_184]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm281 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-2,1),(-1,0),(-1,1)},{(-4,1),(-3,0),(-3,1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-1),(1,0),(1,1),(1,2),(2,-1),(2,0),(2,1),(3,-1),(3,1)},7⟩)
def qmeq_281 : qr 281 = qm281 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 281 = qv281 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 281 < 6 by decide,↓reduceDIte,he,qv281,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_36,qmeq_163,qmeq_189]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm282 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0)},{(-4,-1),(-4,1),(-4,2),(-4,3),(-4,4),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-1,0),(-1,1),(-1,2),(0,0),(0,1),(1,0),(1,1),(2,1)},10⟩)
def qmeq_282 : qr 282 = qm282 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 282 = qv282 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 282 < 6 by decide,↓reduceDIte,he,qv282,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_56,qmeq_64,qmeq_265]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm283 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,-2),(-1,0)},{(-4,-1),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,-2),(-1,-1),(-1,0),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,1)},9⟩)
def qmeq_283 : qr 283 = qm283 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 283 = qv283 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 283 < 6 by decide,↓reduceDIte,he,qv283,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_64,qmeq_196]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm284 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(1,-2),(2,-2),(3,-2)},{(-1,0),(-1,1),(-1,2),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-3),(1,-2),(1,0),(1,1),(1,2),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(3,-2),(3,-1),(3,0),(3,1),(4,-1),(4,1)},9⟩)
def qmeq_284 : qr 284 = qm284 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 284 = qv284 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 284 < 6 by decide,↓reduceDIte,he,qv284,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_45,qmeq_46,qmeq_224]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm285 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-3),(1,-2),(1,-1),(1,0)},{(-2,0),(-1,0),(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(2,-2),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(3,2),(3,3),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1),(6,-1)},9⟩)
def qmeq_285 : qr 285 = qm285 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 285 = qv285 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 285 < 6 by decide,↓reduceDIte,he,qv285,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_273]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm286 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(0,-3),(0,-2),(0,-1)},{(-2,0),(-1,-4),(-1,-3),(-1,-1),(-1,0),(-1,1),(0,-3),(0,-2),(0,-1),(0,0),(1,-2),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-1),(3,0),(3,1),(4,0),(4,1)},10⟩)
def qmeq_286 : qr 286 = qm286 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 286 = qv286 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 286 < 6 by decide,↓reduceDIte,he,qv286,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_261]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm287 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0),(-1,1)},{(-4,-1),(-4,1),(-4,2),(-4,3),(-4,4),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,-1),(-2,0),(-2,1),(-2,3),(-2,4),(-2,5),(-1,0),(-1,1),(0,0),(0,1),(1,0),(1,1),(2,1)},10⟩)
def qmeq_287 : qr 287 = qm287 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 287 = qv287 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 287 < 6 by decide,↓reduceDIte,he,qv287,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_56,qmeq_64,qmeq_264]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm288 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-3),(-3,-2),(-3,-1),(-2,-3),(-2,0),(-1,-3),(0,-3)},{(-4,0),(-4,1),(-4,2),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-2,-3),(-2,0),(-2,1),(-1,-4),(-1,-3),(-1,-2),(-1,0),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-2),(1,0),(1,1),(1,2)},7⟩)
def qmeq_288 : qr 288 = qm288 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 288 = qv288 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 288 < 6 by decide,↓reduceDIte,he,qv288,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_96,qmeq_130]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm289 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-3),(0,-2)},{(-2,0),(-2,1),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1)},9⟩)
def qmeq_289 : qr 289 = qm289 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 289 = qv289 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 289 < 6 by decide,↓reduceDIte,he,qv289,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_279]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm290 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-2),(-1,-1),(0,-2),(0,-1),(0,1)},{(-4,0),(-4,2),(-3,0),(-3,1),(-3,2),(-2,-1),(-2,0),(-2,1),(-2,2),(-1,-2),(-1,-1),(-1,1),(-1,2),(0,-2),(0,-1),(0,0),(0,1),(1,-3),(1,-2),(1,0),(1,1),(1,2),(2,-2),(3,-2)},8⟩)
def qmeq_290 : qr 290 = qm290 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 290 = qv290 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 290 < 6 by decide,↓reduceDIte,he,qv290,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_67,qmeq_231]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm291 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-1),(1,0),(2,0),(3,0)},{(-2,0),(-2,1),(-1,0),(-1,1),(0,0),(0,1),(1,-1),(1,0),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,0),(4,1),(5,-1),(5,0),(5,1),(6,-1),(6,0),(6,1),(7,-1),(7,1)},8⟩)
def qmeq_291 : qr 291 = qm291 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 291 = qv291 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 291 < 6 by decide,↓reduceDIte,he,qv291,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_89,qmeq_202]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm292 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-2,-1),(-2,1),(-1,-1),(-1,1),(0,1)},{(-4,-1),(-3,-1),(-2,-2),(-2,-1),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-2),(0,-1),(0,0),(0,1),(1,-2),(1,0),(2,0)},9⟩)
def qmeq_292 : qr 292 = qm292 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 292 = qv292 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 292 < 6 by decide,↓reduceDIte,he,qv292,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_39,qmeq_79,qmeq_219]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm293 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-2),(-1,-3),(-1,-2),(0,-2),(0,1),(1,-2)},{(-3,-1),(-3,1),(-2,-2),(-2,-1),(-2,0),(-2,1),(-1,-3),(-1,-2),(-1,0),(-1,1),(0,-2),(0,-1),(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(2,-2),(2,-1),(2,0),(3,-1),(3,0),(4,-1)},6⟩)
def qmeq_293 : qr 293 = qm293 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 293 = qv293 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 293 < 6 by decide,↓reduceDIte,he,qv293,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_2,qmeq_280]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm294 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,-2),(-2,0),(-1,0)},{(-4,-1),(-4,1),(-4,2),(-4,3),(-4,4),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-2,-2),(-2,-1),(-2,0),(-2,2),(-2,3),(-2,4),(-1,0),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,1)},9⟩)
def qmeq_294 : qr 294 = qm294 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 294 = qv294 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 294 < 6 by decide,↓reduceDIte,he,qv294,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_63,qmeq_196]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm295 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0)},{(-4,1),(-3,0),(-3,1),(-2,0),(-2,1),(-2,2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,1)},10⟩)
def qmeq_295 : qr 295 = qm295 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 295 = qv295 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 295 < 6 by decide,↓reduceDIte,he,qv295,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_63,qmeq_64,qmeq_265]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm296 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-3),(-3,-2),(-3,-1),(-3,0),(-1,-2),(0,-2),(0,-1)},{(-4,0),(-4,1),(-4,2),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-2,0),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,1),(1,2),(1,3)},7⟩)
def qmeq_296 : qr 296 = qm296 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 296 = qv296 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 296 < 6 by decide,↓reduceDIte,he,qv296,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_65,qmeq_107,qmeq_209]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm297 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-1),(1,-1),(1,0),(2,-1),(3,-1)},{(-1,0),(0,-1),(0,0),(1,-1),(1,0),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-2),(4,0),(4,1),(4,2),(4,3),(4,4)},10⟩)
def qmeq_297 : qr 297 = qm297 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 297 = qv297 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 297 < 6 by decide,↓reduceDIte,he,qv297,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_289]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm298 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-1),(1,0),(2,-1),(2,0)},{(-3,-1),(-3,1),(-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),(0,-1),(0,0),(1,0),(2,-1),(2,0),(3,-1),(3,0),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1),(6,-1),(6,0),(6,1),(7,-1)},8⟩)
def qmeq_298 : qr 298 = qm298 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 298 = qv298 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 298 < 6 by decide,↓reduceDIte,he,qv298,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_24,qmeq_107,qmeq_195]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm299 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-2),(0,-1),(1,-1),(2,-1),(3,-1)},{(-1,0),(-1,1),(-1,2),(-1,3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-2),(1,-1),(1,1),(1,2),(1,3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(3,-1),(3,0),(3,1),(3,2),(4,0),(4,2)},10⟩)
def qmeq_299 : qr 299 = qm299 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 299 = qv299 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 299 < 6 by decide,↓reduceDIte,he,qv299,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_284]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm300 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1)},{(-3,-2),(-2,-3),(-2,-2),(-1,-4),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-4),(1,-3),(1,-2),(2,-4),(2,-3),(2,-2),(3,-4),(3,-3),(3,-2),(4,-4),(4,-2)},9⟩)
def qmeq_300 : qr 300 = qm300 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 300 = qv300 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 300 < 6 by decide,↓reduceDIte,he,qv300,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_64,qmeq_240]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm301 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,-1),(-2,0),(-1,-1),(-1,0),(-1,2),(0,-1)},{(-4,1),(-4,3),(-3,0),(-3,1),(-3,2),(-3,3),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-1),(-1,0),(-1,2),(-1,3),(0,-1),(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)},10⟩)
def qmeq_301 : qr 301 = qm301 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 301 = qv301 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 301 < 6 by decide,↓reduceDIte,he,qv301,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_57,qmeq_59,qmeq_258]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm302 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-2),(-1,-2),(-1,-1),(-1,0),(-1,1),(0,-2),(2,-1)},{(-2,-2),(-2,0),(-2,2),(-2,3),(-2,4),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-2),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-2),(1,-1),(1,0),(2,-1),(2,0),(3,-1),(4,-1)},7⟩)
def qmeq_302 : qr 302 = qm302 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 302 = qv302 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 302 < 6 by decide,↓reduceDIte,he,qv302,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_125,qmeq_162]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm303 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(1,-3)},{(-2,0),(-1,-1),(-1,0),(-1,1),(-1,2),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-1),(3,0),(3,1),(4,0),(4,1)},10⟩)
def qmeq_303 : qr 303 = qm303 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 303 = qv303 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 303 < 6 by decide,↓reduceDIte,he,qv303,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_44,qmeq_49,qmeq_63,qmeq_261]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm304 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-1),(1,0),(2,0),(3,0)},{(-3,-1),(-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),(0,0),(0,1),(1,-1),(1,0),(2,-1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,-1),(5,0),(5,1),(6,-1),(6,0),(6,1),(7,-1),(7,1)},8⟩)
def qmeq_304 : qr 304 = qm304 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 304 = qv304 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 304 < 6 by decide,↓reduceDIte,he,qv304,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_131,qmeq_202]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm305 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-1,-3),(-1,-2),(-1,-1),(-1,0)},{(-5,-1),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,0),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1)},8⟩)
def qmeq_305 : qr 305 = qm305 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 305 = qv305 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 305 < 6 by decide,↓reduceDIte,he,qv305,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_278]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm306 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-4),(-1,-3),(-1,-2),(-1,-1),(0,-3),(1,-3),(2,-3)},{(-2,0),(-2,1),(-2,2),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(0,-3),(0,-1),(0,0),(0,1),(1,-4),(1,-3),(1,-2),(1,0),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(3,-2),(3,0),(3,1),(3,2)},8⟩)
def qmeq_306 : qr 306 = qm306 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 306 = qv306 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 306 < 6 by decide,↓reduceDIte,he,qv306,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_288]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm307 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(-1,-1),(-1,1),(0,-2),(0,-1),(0,1)},{(-3,1),(-2,1),(-1,-2),(-1,-1),(-1,1),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)},9⟩)
def qmeq_307 : qr 307 = qm307 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 307 = qv307 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 307 < 6 by decide,↓reduceDIte,he,qv307,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_273]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm308 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,1),(1,1),(2,1),(3,1)},{(-1,0),(-1,2),(-1,3),(-1,4),(-1,5),(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3),(3,4),(4,2),(4,4)},11⟩)
def qmeq_308 : qr 308 = qm308 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 308 = qv308 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 308 < 6 by decide,↓reduceDIte,he,qv308,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_299]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm309 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(0,1),(0,2),(0,3),(1,1)},{(-3,0),(-2,0),(-1,-1),(-1,0),(-1,3),(-1,4),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(2,5),(2,6),(3,2),(3,3),(3,4),(4,2),(4,3),(4,4)},10⟩)
def qmeq_309 : qr 309 = qm309 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 309 = qv309 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 309 < 6 by decide,↓reduceDIte,he,qv309,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_28,qmeq_268]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm310 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-1)},{(-3,0),(-2,-1),(-2,0),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-2),(0,-1),(0,0),(0,1),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-2),(2,-1),(2,0),(2,1),(3,-2),(3,-1),(3,0),(4,-2),(4,0)},8⟩)
def qmeq_310 : qr 310 = qm310 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 310 = qv310 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 310 < 6 by decide,↓reduceDIte,he,qv310,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_281]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm311 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0),(0,-3),(0,-2),(0,-1),(1,0)},{(-4,-1),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-1,0),(-1,1),(0,-3),(0,-2),(0,-1),(0,0),(1,-1),(1,0),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1)},8⟩)
def qmeq_311 : qr 311 = qm311 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 311 = qv311 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 311 < 6 by decide,↓reduceDIte,he,qv311,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_278]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm312 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(-1,-3),(-1,-1),(-1,0)},{(-3,-1),(-3,2),(-2,-1),(-2,0),(-2,2),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,2),(-1,3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-1),(2,0),(2,1),(3,-1)},10⟩)
def qmeq_312 : qr 312 = qm312 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 312 = qv312 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 312 < 6 by decide,↓reduceDIte,he,qv312,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_9,qmeq_272]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm313 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-1),(0,-3),(0,-2),(0,-1),(1,-1)},{(-2,-1),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-2),(2,-1),(3,-2),(3,-1),(4,-2),(4,-1),(5,-2)},7⟩)
def qmeq_313 : qr 313 = qm313 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 313 = qv313 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 313 < 6 by decide,↓reduceDIte,he,qv313,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_148,qmeq_162]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm314 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-3),(1,-2),(1,-1),(1,0)},{(-3,-1),(-3,1),(-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1),(6,-1)},9⟩)
def qmeq_314 : qr 314 = qm314 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 314 = qv314 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 314 < 6 by decide,↓reduceDIte,he,qv314,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_305]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm315 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-2),(-3,-1),(-3,0),(-3,1),(-2,-1),(-1,-1),(0,-1)},{(-4,1),(-4,2),(-4,3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-2,-1),(-2,1),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4)},8⟩)
def qmeq_315 : qr 315 = qm315 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 315 = qv315 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 315 < 6 by decide,↓reduceDIte,he,qv315,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_296]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm316 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,1),(0,2),(0,3),(1,1),(2,1),(3,1)},{(-1,0),(-1,4),(-1,5),(-1,6),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4),(3,1),(3,2),(3,3),(3,4),(3,5),(4,2),(4,4),(4,5),(4,6)},9⟩)
def qmeq_316 : qr 316 = qm316 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 316 = qv316 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 316 < 6 by decide,↓reduceDIte,he,qv316,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_306]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm317 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-2),(-1,0),(0,-3),(0,-2),(1,0)},{(-4,1),(-3,0),(-3,1),(-2,0),(-2,1),(-1,-3),(-1,-2),(-1,0),(-1,1),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1)},9⟩)
def qmeq_317 : qr 317 = qm317 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 317 = qv317 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 317 < 6 by decide,↓reduceDIte,he,qv317,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_26,qmeq_99,qmeq_263]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm318 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1)},{(-2,0),(-1,-1),(-1,0),(-1,1),(-1,2),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-1),(3,0),(3,1),(4,0),(4,1)},10⟩)
def qmeq_318 : qr 318 = qm318 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 318 = qv318 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 318 < 6 by decide,↓reduceDIte,he,qv318,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_63,qmeq_64,qmeq_261]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm319 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,1),(-2,1),(-1,1)},{(-6,2),(-5,1),(-5,2),(-4,1),(-4,2),(-3,1),(-2,1),(-2,2),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,3)},10⟩)
def qmeq_319 : qr 319 = qm319 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 319 = qv319 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 319 < 6 by decide,↓reduceDIte,he,qv319,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_39,qmeq_109,qmeq_122,qmeq_266]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm320 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(1,-3),(1,0),(3,0)},{(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),(-1,2),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-4),(1,-3),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)},9⟩)
def qmeq_320 : qr 320 = qm320 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 320 = qv320 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 320 < 6 by decide,↓reduceDIte,he,qv320,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_19,qmeq_115,qmeq_267]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm321 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,1),(0,2),(1,1),(2,1)},{(-3,3),(-2,3),(-1,-1),(-1,0),(-1,3),(-1,4),(-1,5),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,2)},8⟩)
def qmeq_321 : qr 321 = qm321 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 321 = qv321 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 321 < 6 by decide,↓reduceDIte,he,qv321,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_97,qmeq_165,qmeq_223]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm322 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-3),(-3,-2),(-3,-1),(-2,-3),(-2,0),(-1,-3),(0,-3)},{(-4,0),(-4,1),(-4,2),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-2,-3),(-2,0),(-2,1),(-1,-3),(-1,0),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(2,-4),(2,-2),(2,-1),(2,0),(2,1)},9⟩)
def qmeq_322 : qr 322 = qm322 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 322 = qv322 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 322 < 6 by decide,↓reduceDIte,he,qv322,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_96,qmeq_205]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm323 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-1,-2),(-1,-1),(-1,0)},{(-5,-1),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,0),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1)},8⟩)
def qmeq_323 : qr 323 = qm323 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 323 = qv323 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 323 < 6 by decide,↓reduceDIte,he,qv323,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_25,qmeq_165,qmeq_278]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm324 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(1,-3),(1,-2),(1,-1),(1,0)},{(-4,-1),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(2,-1),(2,0),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1),(6,-1)},9⟩)
def qmeq_324 : qr 324 = qm324 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 324 = qv324 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 324 < 6 by decide,↓reduceDIte,he,qv324,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_298]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm325 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0),(1,-2),(1,-1),(1,0),(1,1)},{(-2,0),(-1,0),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1),(6,1)},8⟩)
def qmeq_325 : qr 325 = qm325 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 325 = qv325 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 325 < 6 by decide,↓reduceDIte,he,qv325,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_24,qmeq_25,qmeq_313]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm326 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,-3),(-3,0),(-2,0),(-1,0)},{(-6,-4),(-6,-3),(-6,-2),(-6,-1),(-6,1),(-5,-3),(-5,-2),(-5,-1),(-5,0),(-5,1),(-4,-4),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-3,0),(-3,1),(-2,0),(-1,0),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,1)},10⟩)
def qmeq_326 : qr 326 = qm326 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 326 = qv326 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 326 < 6 by decide,↓reduceDIte,he,qv326,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_63,qmeq_255]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm327 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(-1,0),(1,-1),(1,0)},{(-6,-1),(-5,-1),(-5,0),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,0),(1,-1),(1,0),(2,-1),(2,0),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1),(6,-1)},8⟩)
def qmeq_327 : qr 327 = qm327 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 327 = qv327 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 327 < 6 by decide,↓reduceDIte,he,qv327,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_24,qmeq_195]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm328 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(0,-3),(0,-2),(0,-1)},{(-3,0),(-2,0),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1)},10⟩)
def qmeq_328 : qr 328 = qm328 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 328 = qv328 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 328 < 6 by decide,↓reduceDIte,he,qv328,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_44,qmeq_49,qmeq_285]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm329 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(-1,-1),(-1,1),(0,-2),(0,-1),(0,1)},{(-4,0),(-4,2),(-3,0),(-3,1),(-3,2),(-2,0),(-2,1),(-2,2),(-1,-2),(-1,-1),(-1,1),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)},9⟩)
def qmeq_329 : qr 329 = qm329 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 329 = qv329 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 329 < 6 by decide,↓reduceDIte,he,qv329,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_305]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm330 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0)},{(-5,0),(-4,0),(-3,0),(-3,1),(-2,0),(-2,1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,2),(3,1),(3,2)},10⟩)
def qmeq_330 : qr 330 = qm330 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 330 = qv330 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 330 < 6 by decide,↓reduceDIte,he,qv330,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_63,qmeq_144,qmeq_154,qmeq_155,qmeq_268]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm331 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,-1),(-3,-1),(-2,-1),(-2,0),(-2,1),(-1,1)},{(-7,0),(-6,0),(-6,1),(-6,2),(-5,0),(-5,1),(-5,2),(-4,-1),(-4,0),(-4,1),(-4,2),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-1,0),(-1,1),(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)},9⟩)
def qmeq_331 : qr 331 = qm331 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 331 = qv331 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 331 < 6 by decide,↓reduceDIte,he,qv331,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_15,qmeq_90,qmeq_113,qmeq_298]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm332 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(1,-1),(1,0)},{(-3,0),(-2,0),(-1,-4),(-1,-3),(-1,0),(-1,1),(0,-3),(0,-2),(0,-1),(0,0),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(2,-4),(2,-3),(2,-2),(2,-1),(3,-4),(3,-3),(3,-2),(4,-4),(4,-3),(4,-2),(5,-4),(5,-3),(5,-2),(6,-2)},10⟩)
def qmeq_332 : qr 332 = qm332 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 332 = qv332 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 332 < 6 by decide,↓reduceDIte,he,qv332,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_67,qmeq_289]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm333 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(1,-4),(1,-3),(1,-2),(2,0)},{(-3,1),(-2,0),(-2,1),(-1,0),(-1,1),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1),(6,-1),(6,0),(6,1)},10⟩)
def qmeq_333 : qr 333 = qm333 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 333 = qv333 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 333 < 6 by decide,↓reduceDIte,he,qv333,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_1,qmeq_317]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm334 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-2),(0,-1),(0,1),(1,-2),(1,-1)},{(-3,-2),(-2,-2),(-1,-3),(-1,-2),(-1,1),(-1,2),(0,-2),(0,-1),(0,0),(0,1),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1),(5,2),(6,0)},10⟩)
def qmeq_334 : qr 334 = qm334 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 334 = qv334 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 334 < 6 by decide,↓reduceDIte,he,qv334,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_67,qmeq_289]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm335 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,-2),(-2,0),(-1,-1),(-1,0)},{(-4,-1),(-4,1),(-4,2),(-4,3),(-4,4),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-2,-2),(-2,-1),(-2,0),(-2,2),(-2,3),(-2,4),(-1,-1),(-1,0),(0,-1),(0,0),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1)},9⟩)
def qmeq_335 : qr 335 = qm335 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 335 = qv335 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 335 < 6 by decide,↓reduceDIte,he,qv335,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_162,qmeq_196]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm336 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(-1,0),(1,0)},{(-5,-1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-2),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,1)},9⟩)
def qmeq_336 : qr 336 = qm336 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 336 = qv336 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 336 < 6 by decide,↓reduceDIte,he,qv336,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_25,qmeq_65,qmeq_199,qmeq_304]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm337 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-1,0),(-1,1),(-1,2)},{(-4,1),(-3,0),(-3,1),(-2,0),(-2,1),(-2,3),(-2,4),(-2,5),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(0,1),(0,3),(0,4),(0,5),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,1)},9⟩)
def qmeq_337 : qr 337 = qm337 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 337 = qv337 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 337 < 6 by decide,↓reduceDIte,he,qv337,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_107,qmeq_230]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm338 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0),(1,-2),(1,-1),(1,0)},{(-4,-1),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-1,0),(-1,1),(0,-1),(0,0),(1,-2),(1,-1),(1,0),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1),(6,1)},8⟩)
def qmeq_338 : qr 338 = qm338 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 338 = qv338 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 338 < 6 by decide,↓reduceDIte,he,qv338,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_107,qmeq_241,qmeq_275]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm339 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-4),(-1,-3),(-1,-2),(-1,-1),(0,-3),(1,-3),(2,-3)},{(-2,0),(-2,1),(-2,2),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(0,-3),(0,-1),(0,0),(0,1),(1,-3),(1,0),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(4,-4),(4,-2),(4,-1),(4,0),(4,1)},10⟩)
def qmeq_339 : qr 339 = qm339 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 339 = qv339 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 339 < 6 by decide,↓reduceDIte,he,qv339,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_322]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm340 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,1),(0,-1),(0,1)},{(-4,-2),(-4,0),(-3,-2),(-3,-1),(-3,0),(-2,-2),(-2,-1),(-2,0),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-2),(1,-1),(1,0),(1,2),(1,3),(1,4),(2,-1),(2,0),(3,0)},10⟩)
def qmeq_340 : qr 340 = qm340 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 340 = qv340 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 340 < 6 by decide,↓reduceDIte,he,qv340,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_24,qmeq_25,qmeq_300]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm341 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0),(-1,1)},{(-4,-1),(-4,1),(-4,2),(-4,3),(-4,4),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-2,-1),(-2,0),(-2,2),(-2,3),(-2,4),(-1,0),(-1,1),(-1,2),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,1)},9⟩)
def qmeq_341 : qr 341 = qm341 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 341 = qv341 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 341 < 6 by decide,↓reduceDIte,he,qv341,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_143,qmeq_162,qmeq_208,qmeq_259]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm342 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-2),(-1,-3),(-1,-2),(0,-3),(0,-2)},{(-4,-1),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-2),(-2,-1),(-2,0),(-2,1),(-1,-3),(-1,-2),(-1,0),(-1,1),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(2,-3),(2,-2),(2,-1),(3,-3),(3,-2),(3,-1)},9⟩)
def qmeq_342 : qr 342 = qm342 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 342 = qv342 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 342 < 6 by decide,↓reduceDIte,he,qv342,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_88,qmeq_210,qmeq_260,qmeq_290]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm343 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(1,-3),(1,-2)},{(-1,-1),(-1,0),(-1,1),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1)},9⟩)
def qmeq_343 : qr 343 = qm343 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 343 = qv343 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 343 < 6 by decide,↓reduceDIte,he,qv343,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_250]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm344 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-4),(0,-3),(0,-2),(0,-1),(1,-3),(2,-3),(3,-3),(3,-2)},{(-1,-1),(-1,1),(-1,2),(-1,3),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1)},10⟩)
def qmeq_344 : qr 344 = qm344 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 344 = qv344 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 344 < 6 by decide,↓reduceDIte,he,qv344,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_108,qmeq_262]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm345 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-3,3),(-2,0),(-1,0),(-1,3),(0,1)},{(-6,4),(-5,3),(-5,4),(-4,3),(-4,4),(-3,0),(-3,3),(-3,4),(-2,0),(-2,3),(-2,4),(-1,-1),(-1,0),(-1,3),(-1,4),(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)},10⟩)
def qmeq_345 : qr 345 = qm345 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 345 = qv345 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 345 < 6 by decide,↓reduceDIte,he,qv345,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_320]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm346 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-1,-3),(0,-3),(0,-2)},{(-4,-1),(-4,0),(-4,1),(-4,2),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-2,0),(-2,1),(-2,2),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-1),(1,0),(1,1),(1,2)},10⟩)
def qmeq_346 : qr 346 = qm346 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 346 = qv346 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 346 < 6 by decide,↓reduceDIte,he,qv346,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_60,qmeq_255,qmeq_276]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm347 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,1),(0,2),(0,3),(1,1),(2,1),(3,1)},{(-1,0),(-1,4),(-1,5),(-1,6),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(1,4),(1,5),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(3,5),(4,0),(4,1),(4,2),(4,3),(4,4),(5,0),(5,2),(5,3),(5,4),(5,5)},11⟩)
def qmeq_347 : qr 347 = qm347 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 347 = qv347 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 347 < 6 by decide,↓reduceDIte,he,qv347,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_339]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm348 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-2,1),(-1,-1),(0,-2),(0,-1),(1,-1),(1,0)},{(-3,1),(-2,0),(-2,1),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)},11⟩)
def qmeq_348 : qr 348 = qm348 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 348 = qv348 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 348 < 6 by decide,↓reduceDIte,he,qv348,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_114,qmeq_139,qmeq_312]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm349 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-2),(-1,-1),(0,-1)},{(-4,0),(-3,0),(-2,-4),(-2,-3),(-2,0),(-2,1),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-4),(1,-3),(1,-2),(1,-1),(2,-4),(2,-3),(2,-2),(3,-4),(3,-3),(3,-2),(4,-4),(4,-3),(4,-2),(5,-2)},11⟩)
def qmeq_349 : qr 349 = qm349 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 349 = qv349 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 349 < 6 by decide,↓reduceDIte,he,qv349,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_14,qmeq_17,qmeq_332]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm350 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0),(-1,1),(1,0),(1,2)},{(-4,-1),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-1,0),(-1,1),(0,-1),(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,3),(2,4),(2,5),(3,-1),(3,0),(3,1),(4,-1),(4,1)},8⟩)
def qmeq_350 : qr 350 = qm350 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 350 = qv350 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 350 < 6 by decide,↓reduceDIte,he,qv350,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_24,qmeq_107,qmeq_215,qmeq_271]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm351 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(-2,1),(-1,0)},{(-5,1),(-4,0),(-4,1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),(-1,3),(-1,4),(-1,5),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(3,-1),(3,1)},11⟩)
def qmeq_351 : qr 351 = qm351 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 351 = qv351 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 351 < 6 by decide,↓reduceDIte,he,qv351,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_25,qmeq_163,qmeq_287]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm352 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(1,-2),(2,-2),(3,-2),(3,-1)},{(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-2),(2,-1),(2,0),(2,1),(2,2),(3,-2),(3,-1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)},11⟩)
def qmeq_352 : qr 352 = qm352 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 352 = qv352 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 352 < 6 by decide,↓reduceDIte,he,qv352,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_63,qmeq_91,qmeq_180,qmeq_214,qmeq_344]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm353 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-3,1),(-3,2),(-2,0),(-1,0)},{(-4,-1),(-4,1),(-4,3),(-4,4),(-4,5),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,0),(-2,2),(-2,3),(-2,4),(-1,0),(-1,3),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-1),(2,1),(2,2),(2,3),(2,4)},12⟩)
def qmeq_353 : qr 353 = qm353 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 353 = qv353 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 353 < 6 by decide,↓reduceDIte,he,qv353,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_347]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm354 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(-1,0),(-1,1),(0,-2),(0,1),(1,-2)},{(-3,0),(-2,-1),(-2,0),(-2,3),(-1,-1),(-1,0),(-1,1),(-1,3),(0,-2),(0,-1),(0,0),(0,1),(0,3),(0,4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0)},11⟩)
def qmeq_354 : qr 354 = qm354 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 354 = qv354 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 354 < 6 by decide,↓reduceDIte,he,qv354,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_114,qmeq_138,qmeq_182,qmeq_312]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm355 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-1),(1,0),(2,-1),(2,0)},{(-2,0),(-2,1),(-2,3),(-1,0),(-1,1),(-1,2),(-1,3),(0,0),(0,1),(0,2),(0,3),(1,-1),(1,0),(1,2),(1,3),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1)},10⟩)
def qmeq_355 : qr 355 = qm355 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 355 = qv355 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 355 < 6 by decide,↓reduceDIte,he,qv355,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_12,qmeq_167,qmeq_342]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm356 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(-1,0),(1,-1),(1,0),(1,1)},{(-4,-1),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(3,-1),(3,0),(4,-1),(4,0),(5,-1),(5,0),(6,-1)},8⟩)
def qmeq_356 : qr 356 = qm356 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 356 = qv356 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 356 < 6 by decide,↓reduceDIte,he,qv356,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_24,qmeq_179,qmeq_211]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm357 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,2),(-1,-1),(-1,0),(-1,1),(-1,2),(0,2)},{(-4,-1),(-3,-1),(-3,1),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-1,-1),(-1,0),(-1,1),(-1,2),(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,1),(3,3)},10⟩)
def qmeq_357 : qr 357 = qm357 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 357 = qv357 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 357 < 6 by decide,↓reduceDIte,he,qv357,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_82,qmeq_283]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm358 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-2),(-3,-1),(-3,0),(-3,1),(-2,-1),(-1,-1),(0,-1)},{(-4,1),(-4,2),(-4,3),(-4,4),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-2,-1),(-2,2),(-2,3),(-2,4),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)},11⟩)
def qmeq_358 : qr 358 = qm358 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 358 = qv358 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 358 < 6 by decide,↓reduceDIte,he,qv358,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_346]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm359 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(-1,1),(0,-1),(0,1)},{(-4,0),(-4,2),(-3,0),(-3,1),(-3,2),(-2,0),(-2,1),(-2,2),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,1),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)},9⟩)
def qmeq_359 : qr 359 = qm359 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 359 = qv359 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 359 < 6 by decide,↓reduceDIte,he,qv359,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_24,qmeq_134,qmeq_323]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm360 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-2),(0,-4),(0,-3),(0,-2),(0,-1)},{(-3,-1),(-2,-2),(-2,-1),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-3),(1,-2),(1,-1),(1,1),(1,2),(1,3),(2,-3),(2,-2),(2,-1),(3,-3),(3,-2),(3,-1),(4,-3),(4,-2),(4,-1),(5,-3),(5,-1)},10⟩)
def qmeq_360 : qr 360 = qm360 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 360 = qv360 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 360 < 6 by decide,↓reduceDIte,he,qv360,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_155,qmeq_228,qmeq_337]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm361 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-2),(0,-1),(1,-1),(2,-1),(3,-1),(3,0)},{(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(4,3)},12⟩)
def qmeq_361 : qr 361 = qm361 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 361 = qv361 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 361 < 6 by decide,↓reduceDIte,he,qv361,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_352]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm362 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,-1),(-3,-1),(-3,2),(-2,-1),(-1,-1),(-1,2)},{(-6,3),(-5,2),(-5,3),(-4,-1),(-4,2),(-4,3),(-3,-1),(-3,2),(-3,3),(-2,-1),(-2,2),(-2,3),(-1,-2),(-1,-1),(-1,0),(-1,2),(-1,3),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)},11⟩)
def qmeq_362 : qr 362 = qm362 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 362 = qv362 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 362 < 6 by decide,↓reduceDIte,he,qv362,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_345]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm363 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,-3),(-3,-3),(-3,0),(-2,-3),(-1,-3),(-1,0)},{(-5,-1),(-4,-3),(-4,-1),(-4,0),(-3,-3),(-3,-1),(-3,0),(-2,-3),(-2,-1),(-2,0),(-2,1),(-1,-3),(-1,-2),(-1,0),(-1,1),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(2,-4),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1)},9⟩)
def qmeq_363 : qr 363 = qm363 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 363 = qv363 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 363 < 6 by decide,↓reduceDIte,he,qv363,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_137,qmeq_248]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm364 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1)},{(-4,-4),(-4,-2),(-3,-4),(-3,-3),(-3,-2),(-2,-4),(-2,-3),(-2,-2),(-1,-4),(-1,-3),(-1,0),(-1,1),(-1,2),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-4),(1,-3),(1,-2),(1,0),(1,1),(1,2),(2,-4),(2,-3),(2,-2),(3,-4),(3,-3),(3,-2),(4,-4),(4,-3),(4,-2),(5,-2)},10⟩)
def qmeq_364 : qr 364 = qm364 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 364 = qv364 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 364 < 6 by decide,↓reduceDIte,he,qv364,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_63,qmeq_314]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm365 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-3),(1,-3)},{(-3,-1),(-2,-2),(-2,-1),(-2,2),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,2),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-1),(3,0),(3,1),(4,-1)},12⟩)
def qmeq_365 : qr 365 = qm365 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 365 = qv365 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 365 < 6 by decide,↓reduceDIte,he,qv365,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_354]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm366 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-3),(1,-2),(1,-1),(1,0),(2,0)},{(-2,-3),(-1,-3),(-1,-1),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-3),(1,-2),(1,-1),(1,0),(2,-2),(2,-1),(2,0),(2,2),(2,3),(2,4),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,-1),(5,1)},11⟩)
def qmeq_366 : qr 366 = qm366 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 366 = qv366 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 366 < 6 by decide,↓reduceDIte,he,qv366,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_357]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm367 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,1),(-3,2),(-2,1),(-1,1),(0,1)},{(-4,3),(-4,4),(-4,5),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)},13⟩)
def qmeq_367 : qr 367 = qm367 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 367 = qv367 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 367 < 6 by decide,↓reduceDIte,he,qv367,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_361]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm368 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-2),(-1,-1),(-1,0)},{(-4,-3),(-3,-3),(-3,-1),(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,1)},12⟩)
def qmeq_368 : qr 368 = qm368 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 368 = qv368 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 368 < 6 by decide,↓reduceDIte,he,qv368,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_366]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm369 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-2,-1),(-1,-1),(0,-1)},{(-4,-2),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)},14⟩)
def qmeq_369 : qr 369 = qm369 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 369 = qv369 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 369 < 6 by decide,↓reduceDIte,he,qv369,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_367]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm370 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(-1,0)},{(-5,-1),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-2,-2),(-2,-1),(-2,0),(-1,0),(-1,1),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,2),(4,2)},11⟩)
def qmeq_370 : qr 370 = qm370 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 370 = qv370 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 370 < 6 by decide,↓reduceDIte,he,qv370,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_24,qmeq_199,qmeq_286,qmeq_319]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm371 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,-3),(-3,-3),(-3,0),(-2,-3),(-1,-3),(-1,0)},{(-6,1),(-5,0),(-5,1),(-4,-3),(-4,0),(-4,1),(-3,-3),(-3,0),(-3,1),(-2,-3),(-2,0),(-2,1),(-1,-3),(-1,-2),(-1,0),(-1,1),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(2,-4),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1)},9⟩)
def qmeq_371 : qr 371 = qm371 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 371 = qv371 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 371 < 6 by decide,↓reduceDIte,he,qv371,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_137,qmeq_267]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm372 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-3),(-2,-2),(-1,-4),(-1,-3),(-1,-2)},{(-5,1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-2),(1,0),(1,1),(2,-2),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1)},11⟩)
def qmeq_372 : qr 372 = qm372 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 372 = qv372 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 372 < 6 by decide,↓reduceDIte,he,qv372,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_40,qmeq_120,qmeq_161,qmeq_333]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm373 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(0,-1),(0,1),(2,-1),(2,0),(2,1)},{(-5,0),(-5,2),(-4,0),(-4,1),(-4,2),(-3,0),(-3,1),(-3,2),(-2,0),(-2,1),(-2,2),(-1,-1),(-1,0),(-1,1),(0,-1),(0,0),(0,1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1),(5,2),(6,0),(6,1),(6,2),(7,0)},9⟩)
def qmeq_373 : qr 373 = qm373 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 373 = qv373 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 373 < 6 by decide,↓reduceDIte,he,qv373,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_80,qmeq_156,qmeq_226,qmeq_327]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm374 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-2),(1,0),(2,-1),(2,0)},{(-3,-1),(-3,1),(-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-2),(1,-1),(1,0),(1,2),(1,3),(1,4),(2,-1),(2,0),(3,-1),(3,0),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1),(6,-1),(6,0),(6,1),(7,-1)},10⟩)
def qmeq_374 : qr 374 = qm374 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 374 = qv374 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 374 < 6 by decide,↓reduceDIte,he,qv374,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_24,qmeq_65,qmeq_163,qmeq_335]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm375 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(-1,1),(0,-1),(0,1)},{(-7,0),(-6,-2),(-6,-1),(-6,0),(-5,-2),(-5,-1),(-5,0),(-4,-2),(-4,-1),(-4,0),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,-1),(-1,1),(-1,2),(-1,3),(-1,4),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-1),(1,0),(2,-2),(2,-1),(2,0),(3,-2),(3,-1),(3,0),(4,-2),(4,-1),(4,0),(5,0)},9⟩)
def qmeq_375 : qr 375 = qm375 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 375 = qv375 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 375 < 6 by decide,↓reduceDIte,he,qv375,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_24,qmeq_327]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm376 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,-1),(-1,0)},{(-6,2),(-5,2),(-4,-1),(-4,1),(-4,2),(-4,3),(-4,4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-1,-1),(-1,0),(-1,1),(0,-1),(0,0),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1)},10⟩)
def qmeq_376 : qr 376 = qm376 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 376 = qv376 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 376 < 6 by decide,↓reduceDIte,he,qv376,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_162,qmeq_285]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm377 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(0,-3),(0,-2),(1,-3),(2,-3),(2,0)},{(-3,1),(-2,-4),(-2,0),(-2,1),(-1,-4),(-1,-3),(-1,0),(-1,1),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-3),(1,0),(1,1),(2,-4),(2,-3),(2,-2),(2,0),(2,1),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(4,-2),(4,-1),(4,0),(4,1),(4,2),(5,-1),(5,0),(5,1),(6,-1),(6,0),(6,1)},12⟩)
def qmeq_377 : qr 377 = qm377 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 377 = qv377 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 377 < 6 by decide,↓reduceDIte,he,qv377,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_29,qmeq_362]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm378 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-1,-2),(-1,0)},{(-5,-1),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,0),(-2,1),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,1)},11⟩)
def qmeq_378 : qr 378 = qm378 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 378 = qv378 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 378 < 6 by decide,↓reduceDIte,he,qv378,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_172,qmeq_176,qmeq_183,qmeq_294,qmeq_295]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm379 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1)},{(-3,-3),(-2,-3),(-2,-1),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-1),(4,1)},13⟩)
def qmeq_379 : qr 379 = qm379 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 379 = qv379 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 379 < 6 by decide,↓reduceDIte,he,qv379,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_63,qmeq_64,qmeq_368]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm380 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-2,2),(-1,-1),(-1,0)},{(-5,-1),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,3),(-3,4),(-3,5),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-1,-1),(-1,0),(-1,3),(-1,4),(-1,5),(0,-2),(0,-1),(0,0),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1)},8⟩)
def qmeq_380 : qr 380 = qm380 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 380 = qv380 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 380 < 6 by decide,↓reduceDIte,he,qv380,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_101,qmeq_192,qmeq_223,qmeq_271]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm381 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,0),(2,-1),(2,0),(2,1)},{(-3,-1),(-3,1),(-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-1),(1,0),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1),(6,-1),(6,0),(6,1),(7,1)},10⟩)
def qmeq_381 : qr 381 = qm381 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 381 = qv381 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 381 < 6 by decide,↓reduceDIte,he,qv381,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_24,qmeq_163,qmeq_211,qmeq_341]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm382 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-2),(-1,-3),(-1,-2),(0,-2),(0,1),(1,-2)},{(-2,-2),(-1,-3),(-1,-2),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(2,-1)},5⟩)
def qmeq_382 : qr 382 = qm382 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 382 = qv382 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 382 < 6 by decide,↓reduceDIte,he,qv382,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_2,qmeq_124]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm383 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0),(-1,2),(1,0)},{(-4,-1),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,3),(-2,4),(-2,5),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(0,3),(0,4),(0,5),(1,-1),(1,0),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,1)},8⟩)
def qmeq_383 : qr 383 = qm383 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 383 = qv383 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 383 < 6 by decide,↓reduceDIte,he,qv383,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_172,qmeq_192,qmeq_197,qmeq_215,qmeq_271]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm384 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0),(1,0)},{(-4,1),(-3,0),(-3,1),(-2,0),(-2,1),(-1,0),(-1,1),(-1,2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1)},11⟩)
def qmeq_384 : qr 384 = qm384 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 384 = qv384 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 384 < 6 by decide,↓reduceDIte,he,qv384,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_173,qmeq_183,qmeq_220,qmeq_246,qmeq_263,qmeq_282,qmeq_295]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm385 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0)},{(-4,1),(-4,2),(-4,3),(-4,4),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,-1),(2,1)},15⟩)
def qmeq_385 : qr 385 = qm385 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 385 = qv385 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 385 < 6 by decide,↓reduceDIte,he,qv385,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_63,qmeq_64,qmeq_369]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm386 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-1,-2),(-1,0)},{(-5,-1),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-2),(-1,-1),(-1,0),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(3,-1),(3,1)},10⟩)
def qmeq_386 : qr 386 = qm386 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 386 = qv386 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 386 < 6 by decide,↓reduceDIte,he,qv386,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_172,qmeq_173,qmeq_217,qmeq_294]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm387 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(-1,-1),(-1,0),(0,1)},{(-4,-1),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-2),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,1),(3,2),(3,3),(3,4),(4,-1),(4,2),(5,2)},12⟩)
def qmeq_387 : qr 387 = qm387 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 387 = qv387 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 387 < 6 by decide,↓reduceDIte,he,qv387,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_14,qmeq_370]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm388 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-2),(1,-3),(1,-2),(1,-1),(1,0)},{(-4,-1),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-3),(1,-2),(1,-1),(1,0),(2,-1),(2,0),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1),(6,-1)},11⟩)
def qmeq_388 : qr 388 = qm388 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 388 = qv388 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 388 < 6 by decide,↓reduceDIte,he,qv388,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_374]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm389 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-2),(0,-2),(0,-1)},{(-5,-3),(-5,-1),(-4,-3),(-4,-2),(-4,-1),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-2,-2),(-2,0),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(-1,3),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-5),(1,-4),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-3),(2,0),(2,1),(3,1),(4,1)},8⟩)
def qmeq_389 : qr 389 = qm389 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 389 = qv389 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 389 < 6 by decide,↓reduceDIte,he,qv389,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_192,qmeq_197,qmeq_215,qmeq_236,qmeq_271]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm390 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(-1,-1),(0,-2),(0,-1)},{(-4,-5),(-3,-5),(-3,-4),(-2,-5),(-2,-4),(-2,-3),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-5),(2,-4),(2,-2),(3,-5),(3,-4),(3,-3),(3,-2),(4,-5),(4,-4),(4,-3),(5,-5),(5,-4),(5,-3)},12⟩)
def qmeq_390 : qr 390 = qm390 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 390 = qv390 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 390 < 6 by decide,↓reduceDIte,he,qv390,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_12,qmeq_167,qmeq_372]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm391 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(0,-2),(0,-1),(0,1),(1,-2)},{(-5,0),(-5,2),(-4,0),(-4,1),(-4,2),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-2),(0,-1),(0,0),(0,1),(1,-3),(1,-2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)},12⟩)
def qmeq_391 : qr 391 = qm391 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 391 = qv391 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 391 < 6 by decide,↓reduceDIte,he,qv391,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_388]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm392 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(0,-2),(0,-1)},{(-4,-1),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(-1,3),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-5),(1,-4),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1)},11⟩)
def qmeq_392 : qr 392 = qm392 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 392 = qv392 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 392 < 6 by decide,↓reduceDIte,he,qv392,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_24,qmeq_107,qmeq_236,qmeq_364]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm393 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-2),(0,-1),(1,-2),(2,-3),(2,-2),(3,-2),(3,-1)},{(-2,1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-2),(3,-1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(6,-1),(6,0),(6,1)},12⟩)
def qmeq_393 : qr 393 = qm393 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 393 = qv393 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 393 < 6 by decide,↓reduceDIte,he,qv393,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_65,qmeq_107,qmeq_303,qmeq_348]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm394 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(0,-1)},{(-7,-2),(-7,-1),(-7,0),(-7,1),(-6,-2),(-6,-1),(-6,0),(-6,1),(-5,-2),(-5,-1),(-5,0),(-5,1),(-4,-2),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,-1),(0,0),(1,-1),(1,0),(2,-2),(2,-1),(2,0),(2,1),(3,-2),(3,-1),(3,0),(3,1),(4,-2),(4,-1),(4,0),(4,1),(5,-2),(5,-1),(5,0),(5,1)},9⟩)
def qmeq_394 : qr 394 = qm394 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 394 = qv394 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 394 < 6 by decide,↓reduceDIte,he,qv394,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_226,qmeq_327]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm395 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0),(1,-1),(1,0),(1,1)},{(-4,-1),(-4,1),(-4,2),(-3,-1),(-3,0),(-3,1),(-3,2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-1),(1,0),(1,1),(2,-1),(2,0),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1),(6,-1)},11⟩)
def qmeq_395 : qr 395 = qm395 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 395 = qv395 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 395 < 6 by decide,↓reduceDIte,he,qv395,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_24,qmeq_211,qmeq_236,qmeq_376]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm396 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-2),(0,-1),(1,-2),(2,-2),(3,-2)},{(-2,1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-2),(3,-1),(3,0),(3,1),(3,2),(4,-1),(4,0),(4,1),(4,2),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(6,-1),(6,0),(6,1)},13⟩)
def qmeq_396 : qr 396 = qm396 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 396 = qv396 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 396 < 6 by decide,↓reduceDIte,he,qv396,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_65,qmeq_107,qmeq_303,qmeq_365]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm397 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-2),(1,-2),(1,-1),(1,0)},{(-4,-1),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(2,-5),(2,-4),(2,-3),(2,-1),(2,0),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1),(6,-1)},11⟩)
def qmeq_397 : qr 397 = qm397 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 397 = qv397 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 397 < 6 by decide,↓reduceDIte,he,qv397,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_24,qmeq_65,qmeq_374]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm398 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-4),(-3,-3),(-3,-2),(-2,-3),(-2,0),(-1,-3),(0,-3)},{(-4,-1),(-4,0),(-4,1),(-4,2),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-2,-3),(-2,-1),(-2,0),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(3,-4),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1)},10⟩)
def qmeq_398 : qr 398 = qm398 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 398 = qv398 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 398 < 6 by decide,↓reduceDIte,he,qv398,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_130,qmeq_177,qmeq_257,qmeq_363]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm399 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-2),(0,-2),(0,-1)},{(-5,-3),(-5,-1),(-4,-3),(-4,-2),(-4,-1),(-3,-3),(-3,-2),(-3,-1),(-2,-2),(-2,1),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(-1,3),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-5),(1,-4),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1),(4,2)},11⟩)
def qmeq_399 : qr 399 = qm399 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 399 = qv399 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 399 < 6 by decide,↓reduceDIte,he,qv399,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_173,qmeq_192,qmeq_215,qmeq_271,qmeq_319]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm400 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(-1,0),(1,-2),(1,0)},{(-5,-1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(1,-2),(1,-1),(1,0),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-1),(4,0),(4,1)},10⟩)
def qmeq_400 : qr 400 = qm400 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 400 = qv400 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 400 < 6 by decide,↓reduceDIte,he,qv400,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_176,qmeq_197,qmeq_245,qmeq_252,qmeq_283]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm401 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(0,-1),(0,1)},{(-4,0),(-4,2),(-3,0),(-3,1),(-3,2),(-2,0),(-2,1),(-2,2),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,1),(-1,2),(-1,3),(-1,4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-4),(1,-3),(1,-2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,0)},11⟩)
def qmeq_401 : qr 401 = qm401 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 401 = qv401 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 401 < 6 by decide,↓reduceDIte,he,qv401,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_24,qmeq_286,qmeq_319,qmeq_364]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm402 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(0,-3),(0,-2),(1,-3),(2,-3),(2,0)},{(-3,1),(-2,-4),(-2,0),(-2,1),(-1,-4),(-1,-3),(-1,0),(-1,1),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-3),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,-1),(5,0),(5,1),(6,-1),(6,0),(6,1)},12⟩)
def qmeq_402 : qr 402 = qm402 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 402 = qv402 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 402 < 6 by decide,↓reduceDIte,he,qv402,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_29,qmeq_384]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm403 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(0,-3),(0,-2),(0,-1)},{(-5,-1),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1)},12⟩)
def qmeq_403 : qr 403 = qm403 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 403 = qv403 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 403 < 6 by decide,↓reduceDIte,he,qv403,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_63,qmeq_180,qmeq_202,qmeq_314,qmeq_388]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm404 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(-1,0),(-1,1),(-1,2)},{(-6,1),(-5,1),(-5,2),(-5,3),(-4,-1),(-4,1),(-4,2),(-4,3),(-3,-1),(-3,1),(-3,2),(-3,3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-1,-1),(-1,0),(-1,1),(-1,2),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,1),(3,2),(3,3),(4,1),(4,3)},12⟩)
def qmeq_404 : qr 404 = qm404 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 404 = qv404 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 404 < 6 by decide,↓reduceDIte,he,qv404,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_82,qmeq_388]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm405 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-2),(-1,-3),(-1,-2),(0,-3),(0,-2),(1,-3)},{(-5,-1),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(2,-2),(2,-1),(2,0),(2,1),(3,-2),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1)},13⟩)
def qmeq_405 : qr 405 = qm405 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 405 = qv405 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 405 < 6 by decide,↓reduceDIte,he,qv405,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_42,qmeq_301,qmeq_391]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def ql406b0 : List qCell := [(-4,-1),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-1,-5),(-1,-4),(-1,-3),(-1,0),(-1,1),(-1,2),(-1,3),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-5),(1,-4)]
def ql406b1 : List qCell := [(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-1),(2,0),(2,1),(2,2),(3,-1),(3,0),(3,1),(3,2),(4,-1),(4,0),(4,1),(4,2),(5,-1)]
def ql406 : List qCell := ql406b0 ++ ql406b1
def qn406 : (ql406).Nodup := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qm406 : qR := ⟨{(0,-2),(0,-1)},⟨(ql406 : Multiset qCell), Multiset.coe_nodup.mpr qn406⟩,11⟩
def qmeq_406 : qr 406 = qm406 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 406 = qv406 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 406 < 6 by decide,↓reduceDIte,he,qv406,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_172,qmeq_176,qmeq_197,qmeq_236,qmeq_245,qmeq_295,qmeq_364]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm407 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,1),(0,2),(0,3)},{(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-3,3),(-2,-1),(-2,0),(-2,1),(-2,3),(-1,-1),(-1,0),(-1,1),(-1,3),(-1,4),(0,0),(0,1),(0,2),(0,3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-1),(4,1),(4,2),(4,3),(4,4),(5,2)},10⟩)
def qmeq_407 : qr 407 = qm407 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 407 = qv407 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 407 < 6 by decide,↓reduceDIte,he,qv407,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_285,qmeq_314]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm408 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0),(0,-3),(0,-2),(0,-1),(1,0)},{(-5,-1),(-4,-1),(-4,0),(-4,1),(-3,-3),(-3,-1),(-3,0),(-3,1),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-3),(0,-2),(0,-1),(0,0),(1,-2),(1,-1),(1,0),(1,2),(1,3),(1,4),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-1),(4,0),(4,1),(5,-1)},11⟩)
def qmeq_408 : qr 408 = qm408 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 408 = qv408 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 408 < 6 by decide,↓reduceDIte,he,qv408,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_223,qmeq_229,qmeq_357]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm409 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(1,-3),(2,-1),(2,0)},{(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),(-1,2),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-4),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,-1),(5,0),(5,1),(6,-1),(6,0),(6,1)},12⟩)
def qmeq_409 : qr 409 = qm409 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 409 = qv409 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 409 < 6 by decide,↓reduceDIte,he,qv409,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_110,qmeq_133,qmeq_136,qmeq_384]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm410 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,1),(-2,0),(-2,1),(-1,0),(-1,1)},{(-6,2),(-6,4),(-5,2),(-5,3),(-5,4),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4),(4,2)},14⟩)
def qmeq_410 : qr 410 = qm410 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 410 = qv410 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 410 < 6 by decide,↓reduceDIte,he,qv410,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_405]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm411 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,0),(2,0)},{(-3,-1),(-2,-1),(-2,0),(-1,-1),(-1,0),(0,-3),(0,-2),(0,-1),(0,0),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,-1),(5,0),(5,1),(5,2),(5,3),(6,-1),(6,0),(6,1),(6,2),(6,3),(7,1),(7,3)},14⟩)
def qmeq_411 : qr 411 = qm411 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 411 = qv411 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 411 < 6 by decide,↓reduceDIte,he,qv411,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_173,qmeq_246,qmeq_252,qmeq_263,qmeq_300,qmeq_379]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm412 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-2,-1),(-1,-1),(-1,0),(-1,1)},{(-6,1),(-5,1),(-5,2),(-5,3),(-4,-1),(-4,1),(-4,2),(-4,3),(-3,-1),(-3,1),(-3,2),(-3,3),(-2,-1),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,1),(3,2),(3,3),(4,1),(4,3)},13⟩)
def qmeq_412 : qr 412 = qm412 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 412 = qv412 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 412 < 6 by decide,↓reduceDIte,he,qv412,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_403]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm413 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(-1,-1),(-1,1),(0,1),(0,2)},{(-5,2),(-5,4),(-4,2),(-4,3),(-4,4),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-1,-2),(-1,-1),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4),(4,2),(4,3),(4,4),(5,2)},13⟩)
def qmeq_413 : qr 413 = qm413 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 413 = qv413 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 413 < 6 by decide,↓reduceDIte,he,qv413,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_3,qmeq_403]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm414 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(-1,1),(0,-1),(0,1)},{(-5,0),(-5,2),(-4,0),(-4,1),(-4,2),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,3),(-1,4),(-1,5),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-4),(1,-3),(1,-2),(1,0),(1,1),(1,2),(2,-2),(2,0),(2,1),(2,2),(3,-2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)},11⟩)
def qmeq_414 : qr 414 = qm414 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 414 = qv414 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 414 < 6 by decide,↓reduceDIte,he,qv414,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_185,qmeq_199,qmeq_374]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm415 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-3),(-2,-3),(-2,0),(-1,-3),(0,-3)},{(-5,1),(-4,0),(-4,1),(-3,-3),(-3,0),(-3,1),(-2,-3),(-2,0),(-2,1),(-2,2),(-1,-4),(-1,-3),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-4),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1)},12⟩)
def qmeq_415 : qr 415 = qm415 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 415 = qv415 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 415 < 6 by decide,↓reduceDIte,he,qv415,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_164,qmeq_177,qmeq_205,qmeq_371,qmeq_384]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm416 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-1,0)},{(-5,-1),(-5,0),(-5,1),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,0),(3,1),(4,1)},16⟩)
def qmeq_416 : qr 416 = qm416 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 416 = qv416 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 416 < 6 by decide,↓reduceDIte,he,qv416,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_176,qmeq_197,qmeq_220,qmeq_245,qmeq_295,qmeq_385]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm417 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-3),(-2,-2),(-1,-3),(0,-3),(0,-1),(1,-3)},{(-5,-1),(-5,0),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-3,2),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-1,-4),(-1,-3),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-4),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1)},13⟩)
def qmeq_417 : qr 417 = qm417 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 417 = qv417 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 417 < 6 by decide,↓reduceDIte,he,qv417,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_11,qmeq_270,qmeq_409]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm418 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-4),(-1,-3),(-1,-1),(0,-1)},{(-5,0),(-5,2),(-4,-1),(-4,0),(-4,1),(-4,2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-1,-4),(-1,-3),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)},14⟩)
def qmeq_418 : qr 418 = qm418 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 418 = qv418 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 418 < 6 by decide,↓reduceDIte,he,qv418,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_62,qmeq_68,qmeq_147,qmeq_413]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm419 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-3),(-2,-3),(-2,-2),(-1,-3),(0,-3)},{(-5,1),(-4,-4),(-4,0),(-4,1),(-3,-4),(-3,-3),(-3,-1),(-3,0),(-3,1),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-1,-4),(-1,-3),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1)},13⟩)
def qmeq_419 : qr 419 = qm419 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 419 = qv419 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 419 < 6 by decide,↓reduceDIte,he,qv419,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_164,qmeq_243,qmeq_253,qmeq_377,qmeq_402]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm420 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(0,-3),(0,-2),(1,-3),(2,-3)},{(-3,1),(-2,-4),(-2,0),(-2,1),(-1,-4),(-1,-3),(-1,0),(-1,1),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-4),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,-4),(5,-1),(5,0),(5,1),(6,-1),(6,0),(6,1)},13⟩)
def qmeq_420 : qr 420 = qm420 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 420 = qv420 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 420 < 6 by decide,↓reduceDIte,he,qv420,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_29,qmeq_415]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm421 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(-1,-1),(-1,0),(1,0)},{(-6,1),(-5,-1),(-5,0),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-2),(-1,-1),(-1,0),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,2),(2,3),(2,4),(3,-3),(3,-2),(3,-1),(4,-3),(4,-2),(4,-1),(5,-3),(5,-1)},12⟩)
def qmeq_421 : qr 421 = qm421 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 421 = qv421 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 421 < 6 by decide,↓reduceDIte,he,qv421,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_24,qmeq_25,qmeq_241,qmeq_397]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm422 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(-1,0),(-1,1),(-1,2)},{(-4,-1),(-3,-1),(-2,-2),(-2,-1),(-2,1),(-2,2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-1),(0,0),(0,2),(0,3),(0,4),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(4,0),(4,1),(4,2),(4,3),(4,4),(5,1),(5,2),(5,3),(5,4),(6,1),(6,2),(6,3),(6,4)},14⟩)
def qmeq_422 : qr 422 = qm422 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 422 = qv422 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 422 < 6 by decide,↓reduceDIte,he,qv422,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_45,qmeq_106,qmeq_419]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm423 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(-1,0),(0,-2)},{(-5,-1),(-5,1),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-1),(4,1)},12⟩)
def qmeq_423 : qr 423 = qm423 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 423 = qv423 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 423 < 6 by decide,↓reduceDIte,he,qv423,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_226,qmeq_378,qmeq_386]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm424 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(2,-1)},{(-5,-2),(-5,-1),(-5,0),(-5,1),(-4,-2),(-4,-1),(-4,0),(-4,1),(-3,-2),(-3,-1),(-3,0),(-3,1),(-2,-2),(-2,-1),(-2,0),(-2,1),(-1,-2),(-1,-1),(-1,0),(-1,2),(-1,3),(-1,4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-1),(2,0),(3,-1),(3,0),(4,-2),(4,-1),(4,0),(4,1),(5,-2),(5,-1),(5,0),(5,1),(6,-2),(6,-1),(6,0),(6,1),(7,-2),(7,-1),(7,0),(7,1)},10⟩)
def qmeq_424 : qr 424 = qm424 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 424 = qv424 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 424 < 6 by decide,↓reduceDIte,he,qv424,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_216,qmeq_394]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm425 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(-1,0),(0,-2)},{(-5,-1),(-5,1),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-1),(4,1)},12⟩)
def qmeq_425 : qr 425 = qm425 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 425 = qv425 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 425 < 6 by decide,↓reduceDIte,he,qv425,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_226,qmeq_378,qmeq_386]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm426 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(0,-2),(0,-1)},{(-5,-1),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-5),(1,-4),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,0),(3,1),(3,2),(4,-1),(4,0),(4,1),(4,2),(5,-1),(5,0)},12⟩)
def qmeq_426 : qr 426 = qm426 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 426 = qv426 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 426 < 6 by decide,↓reduceDIte,he,qv426,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_252,qmeq_291,qmeq_300,qmeq_319,qmeq_328,qmeq_397]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm427 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(-1,0),(-1,1),(-1,2)},{(-4,-1),(-3,-1),(-2,-2),(-2,-1),(-2,1),(-2,3),(-2,4),(-2,5),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(4,0),(4,1),(4,2),(4,3),(4,4),(5,1),(5,2),(5,3),(5,4),(6,1),(6,2),(6,3),(6,4)},14⟩)
def qmeq_427 : qr 427 = qm427 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 427 = qv427 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 427 < 6 by decide,↓reduceDIte,he,qv427,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_45,qmeq_106,qmeq_420]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm428 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-2),(-1,0),(0,-3),(0,-2)},{(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-1),(4,0),(4,1),(5,-1),(5,1)},17⟩)
def qmeq_428 : qr 428 = qm428 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 428 = qv428 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 428 < 6 by decide,↓reduceDIte,he,qv428,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_26,qmeq_244,qmeq_329,qmeq_416]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm429 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,2),(1,-1),(1,0),(2,0),(3,0)},{(-2,0),(-1,0),(-1,1),(0,0),(0,1),(0,2),(0,3),(1,-1),(1,0),(2,-1),(2,0),(3,-1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)},6⟩)
def qmeq_429 : qr 429 = qm429 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 429 = qv429 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 429 < 6 by decide,↓reduceDIte,he,qv429,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_28,qmeq_128]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm430 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-2),(-2,-1),(-2,0),(-1,-2),(0,-2)},{(-7,-1),(-7,1),(-6,-1),(-6,0),(-6,1),(-5,-1),(-5,0),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-2,-2),(-2,-1),(-2,0),(-1,-6),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,2),(-1,3),(-1,4),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-5),(1,-4),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-3),(2,-1),(2,0),(2,1),(3,-3),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1)},10⟩)
def qmeq_430 : qr 430 = qm430 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 430 = qv430 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 430 < 6 by decide,↓reduceDIte,he,qv430,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_277,qmeq_336,qmeq_338,qmeq_375]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm431 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-4),(-1,-3),(-1,-2),(0,-3),(1,-3),(2,-3)},{(-3,1),(-2,-1),(-2,0),(-2,1),(-2,2),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(0,-3),(0,-1),(0,0),(0,1),(0,2),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(6,-2),(6,-1),(6,0),(6,1)},13⟩)
def qmeq_431 : qr 431 = qm431 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 431 = qv431 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 431 < 6 by decide,↓reduceDIte,he,qv431,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_73,qmeq_302,qmeq_398,qmeq_415]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm432 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(0,-3),(0,-2),(1,-3),(1,-2)},{(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-1,-4),(-1,-3),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,-1),(5,0),(5,1),(6,-1),(6,1)},18⟩)
def qmeq_432 : qr 432 = qm432 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 432 = qv432 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 432 < 6 by decide,↓reduceDIte,he,qv432,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_42,qmeq_274,qmeq_428]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm433 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-4),(0,-3),(0,-2),(0,-1)},{(-3,-3),(-2,-3),(-1,-4),(-1,-3),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-3),(1,-2),(1,0),(1,1),(1,2),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,-2),(5,-1),(5,0),(5,1),(5,2),(6,-1),(6,0),(6,1),(6,2),(7,-1),(7,0),(7,1),(7,2)},15⟩)
def qmeq_433 : qr 433 = qm433 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 433 = qv433 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 433 < 6 by decide,↓reduceDIte,he,qv433,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_63,qmeq_422,qmeq_427]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm434 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-1,-3),(-1,-2),(-1,0),(0,-2)},{(-5,1),(-5,3),(-4,0),(-4,1),(-4,2),(-4,3),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,0),(3,1),(3,2),(3,3),(4,-1),(4,0),(4,1),(4,2),(4,3),(5,1)},15⟩)
def qmeq_434 : qr 434 = qm434 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 434 = qv434 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 434 < 6 by decide,↓reduceDIte,he,qv434,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_116,qmeq_176,qmeq_263,qmeq_295,qmeq_418]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm435 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-2),(0,-1),(1,-1),(2,-1),(3,-1)},{(-2,3),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-1),(1,1),(1,2),(1,3),(1,4),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(7,0),(7,1),(7,2),(7,3)},14⟩)
def qmeq_435 : qr 435 = qm435 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 435 = qv435 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 435 < 6 by decide,↓reduceDIte,he,qv435,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_431]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm436 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(1,-3),(1,-2)},{(-4,-1),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,-1),(5,0),(5,1),(6,-1),(6,1)},18⟩)
def qmeq_436 : qr 436 = qm436 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 436 = qv436 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 436 < 6 by decide,↓reduceDIte,he,qv436,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_51,qmeq_60,qmeq_274,qmeq_428]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm437 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1)},{(-3,-3),(-2,-3),(-1,-5),(-1,-4),(-1,-3),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-3),(1,-2),(1,0),(1,1),(1,2),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,-2),(5,-1),(5,0),(5,1),(5,2),(6,-1),(6,0),(6,1),(6,2),(7,-1),(7,0),(7,1),(7,2)},15⟩)
def qmeq_437 : qr 437 = qm437 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 437 = qv437 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 437 < 6 by decide,↓reduceDIte,he,qv437,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_63,qmeq_422,qmeq_427]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm438 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-1),(0,-1),(1,-1),(1,0)},{(-3,-1),(-3,1),(-3,2),(-3,3),(-2,-1),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-1,-2),(-1,-1),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(5,1),(5,2),(5,3),(6,1),(6,3)},19⟩)
def qmeq_438 : qr 438 = qm438 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 438 = qv438 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 438 < 6 by decide,↓reduceDIte,he,qv438,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_432]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm439 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-1,-4),(-1,-3),(-1,-2),(-1,0)},{(-5,1),(-5,3),(-4,0),(-4,1),(-4,2),(-4,3),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-1,-4),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,0),(3,1),(3,2),(3,3),(4,-1),(4,0),(4,1),(4,2),(4,3),(5,1)},15⟩)
def qmeq_439 : qr 439 = qm439 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 439 = qv439 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 439 < 6 by decide,↓reduceDIte,he,qv439,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_149,qmeq_176,qmeq_263,qmeq_295,qmeq_418]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm440 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(-1,0),(1,0)},{(-4,4),(-3,-1),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-1,0),(-1,2),(-1,3),(-1,4),(-1,5),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,1),(5,2),(5,3),(5,4)},15⟩)
def qmeq_440 : qr 440 = qm440 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 440 = qv440 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 440 < 6 by decide,↓reduceDIte,he,qv440,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_435]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm441 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,1),(1,1),(2,1),(3,1)},{(-2,5),(-1,0),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(7,2),(7,3),(7,4),(7,5)},15⟩)
def qmeq_441 : qr 441 = qm441 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 441 = qv441 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 441 < 6 by decide,↓reduceDIte,he,qv441,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_435]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm442 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-4),(0,-3),(0,-2),(0,-1)},{(-3,-2),(-2,-2),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(5,-1),(5,0),(5,1),(5,2),(5,3),(6,0),(6,1),(6,2),(6,3),(7,0),(7,1),(7,2),(7,3)},16⟩)
def qmeq_442 : qr 442 = qm442 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 442 = qv442 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 442 < 6 by decide,↓reduceDIte,he,qv442,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_63,qmeq_201,qmeq_433]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm443 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-2,-1),(-1,-1),(0,-1)},{(-4,-1),(-4,1),(-4,2),(-4,3),(-3,-1),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-2,-2),(-2,-1),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(4,1),(4,2),(4,3),(5,1),(5,3)},20⟩)
def qmeq_443 : qr 443 = qm443 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 443 = qv443 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 443 < 6 by decide,↓reduceDIte,he,qv443,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_438]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm444 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-2),(-1,-2),(0,-2),(0,-1)},{(-5,-3),(-5,-1),(-5,0),(-5,1),(-5,2),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-2,-2),(-2,0),(-2,1),(-2,2),(-1,-2),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-5),(1,-4),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,0),(4,1),(4,2),(5,0),(5,2)},14⟩)
def qmeq_444 : qr 444 = qm444 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 444 = qv444 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 444 < 6 by decide,↓reduceDIte,he,qv444,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_142,qmeq_160,qmeq_194,qmeq_236,qmeq_353,qmeq_412]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm445 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,0),(1,1),(2,0),(2,1)},{(-2,0),(-2,2),(-2,3),(-2,4),(-1,0),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(0,-1),(0,0),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(6,2),(6,3),(6,4),(7,2),(7,4)},19⟩)
def qmeq_445 : qr 445 = qm445 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 445 = qv445 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 445 < 6 by decide,↓reduceDIte,he,qv445,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_9,qmeq_432]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm446 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(1,0),(2,0),(3,0),(3,1)},{(-1,-1),(-1,0),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,-1),(1,0),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(7,2),(7,3),(7,4),(8,2),(8,4)},20⟩)
def qmeq_446 : qr 446 = qm446 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 446 = qv446 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 446 < 6 by decide,↓reduceDIte,he,qv446,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_438]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm447 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-2,-1),(-1,-1),(-1,0),(0,-1)},{(-6,1),(-6,3),(-5,1),(-5,2),(-5,3),(-4,-1),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-3,-1),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-2,-1),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(3,1),(3,2),(3,3),(4,1),(4,3)},19⟩)
def qmeq_447 : qr 447 = qm447 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 447 = qv447 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 447 < 6 by decide,↓reduceDIte,he,qv447,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_436]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm448 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-1),(-1,0),(0,-1)},{(-5,1),(-5,3),(-4,-1),(-4,1),(-4,2),(-4,3),(-3,-1),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-2,-1),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(4,1),(4,2),(4,3),(5,1),(5,3)},19⟩)
def qmeq_448 : qr 448 = qm448 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 448 = qv448 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 448 < 6 by decide,↓reduceDIte,he,qv448,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_9,qmeq_436]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm449 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-2),(-1,0),(0,-4),(0,-3),(0,-2)},{(-4,1),(-4,3),(-3,0),(-3,1),(-3,2),(-3,3),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-1),(4,0),(4,1),(4,2),(4,3),(5,-1),(5,0),(5,1),(5,2),(5,3),(6,1)},16⟩)
def qmeq_449 : qr 449 = qm449 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 449 = qv449 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 449 < 6 by decide,↓reduceDIte,he,qv449,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_26,qmeq_244,qmeq_307,qmeq_439]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm450 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(1,0),(3,0)},{(-2,4),(-1,-1),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(7,1),(7,2),(7,3),(7,4)},16⟩)
def qmeq_450 : qr 450 = qm450 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 450 = qv450 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 450 < 6 by decide,↓reduceDIte,he,qv450,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_440]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm451 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(1,-4),(1,-3),(1,-2)},{(-3,1),(-3,3),(-2,0),(-2,1),(-2,2),(-2,3),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,-1),(5,0),(5,1),(5,2),(5,3),(6,-1),(6,0),(6,1),(6,2),(6,3),(7,1)},17⟩)
def qmeq_451 : qr 451 = qm451 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 451 = qv451 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 451 < 6 by decide,↓reduceDIte,he,qv451,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_1,qmeq_449]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm452 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,1),(-1,2),(0,1),(0,2),(1,2)},{(-4,5),(-4,7),(-3,4),(-3,5),(-3,6),(-3,7),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(4,3),(4,4),(4,5),(4,6),(4,7),(5,3),(5,4),(5,5),(5,6),(5,7),(6,5)},18⟩)
def qmeq_452 : qr 452 = qm452 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 452 = qv452 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 452 < 6 by decide,↓reduceDIte,he,qv452,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_24,qmeq_25,qmeq_451]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm453 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(-1,0),(0,-2)},{(-6,-1),(-5,-1),(-5,0),(-5,1),(-4,-3),(-4,-1),(-4,0),(-4,1),(-3,-3),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,-7),(-2,-6),(-2,-5),(-2,-4),(-2,-3),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-6),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,2),(-1,3),(-1,4),(0,-7),(0,-6),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1)},12⟩)
def qmeq_453 : qr 453 = qm453 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 453 = qv453 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 453 < 6 by decide,↓reduceDIte,he,qv453,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_226,qmeq_359,qmeq_386,qmeq_389,qmeq_414]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm454 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-1),(-1,0),(0,-1),(1,-1)},{(-5,1),(-5,3),(-4,1),(-4,2),(-4,3),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-2,-1),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(4,1),(4,2),(4,3),(5,1),(5,3)},19⟩)
def qmeq_454 : qr 454 = qm454 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 454 = qv454 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 454 < 6 by decide,↓reduceDIte,he,qv454,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_58,qmeq_436]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm455 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-3,0),(-3,1),(-2,1),(-1,1)},{(-5,2),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-3,-1),(-3,0),(-3,1),(-2,1),(-1,0),(-1,1),(0,0),(0,1),(1,0),(2,0)},5⟩)
def qmeq_455 : qr 455 = qm455 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 455 = qv455 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 455 < 6 by decide,↓reduceDIte,he,qv455,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_20,qmeq_39,qmeq_118]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm456 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0)},{(-4,1),(-4,3),(-3,0),(-3,1),(-3,2),(-3,3),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-1),(-1,0),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,1)},12⟩)
def qmeq_456 : qr 456 = qm456 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 456 = qv456 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 456 < 6 by decide,↓reduceDIte,he,qv456,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_63,qmeq_64,qmeq_308]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm457 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-1),(0,-1),(1,-1),(2,-1)},{(-4,1),(-4,3),(-3,1),(-3,2),(-3,3),(-2,-2),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(5,1),(5,2),(5,3),(6,1),(6,3)},20⟩)
def qmeq_457 : qr 457 = qm457 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 457 = qv457 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 457 < 6 by decide,↓reduceDIte,he,qv457,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_28,qmeq_454]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm458 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-3),(-3,-2),(-3,-1),(-2,-3),(-2,0),(-1,-3),(0,-3)},{(-5,4),(-4,-1),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,-3),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2),(4,3),(4,4)},17⟩)
def qmeq_458 : qr 458 = qm458 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 458 = qv458 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 458 < 6 by decide,↓reduceDIte,he,qv458,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_130,qmeq_177,qmeq_450]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm459 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(0,-2),(0,-1),(1,-1),(2,-1)},{(-4,1),(-4,3),(-3,-1),(-3,1),(-3,2),(-3,3),(-2,-1),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,-2),(3,-1),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(4,-2),(4,-1),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(5,-2),(5,1),(5,2),(5,3),(6,1),(6,3)},20⟩)
def qmeq_459 : qr 459 = qm459 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 459 = qv459 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 459 < 6 by decide,↓reduceDIte,he,qv459,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_65,qmeq_97,qmeq_448]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm460 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-1,0)},{(-5,1),(-4,0),(-4,1),(-3,0),(-3,1),(-2,0),(-2,1),(-2,2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1)},11⟩)
def qmeq_460 : qr 460 = qm460 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 460 = qv460 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 460 < 6 by decide,↓reduceDIte,he,qv460,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_173,qmeq_183,qmeq_220,qmeq_246,qmeq_263,qmeq_282,qmeq_295]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm461 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-4),(-1,-3),(-1,-2),(-1,-1),(0,-3),(1,-3),(2,-3)},{(-3,4),(-2,-1),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-3),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(6,1),(6,2),(6,3),(6,4)},18⟩)
def qmeq_461 : qr 461 = qm461 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 461 = qv461 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 461 < 6 by decide,↓reduceDIte,he,qv461,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_458]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm462 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(-1,-1),(-1,0)},{(-5,3),(-5,5),(-4,2),(-4,3),(-4,4),(-4,5),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,-1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1),(4,2),(4,3),(4,4),(4,5),(5,3)},19⟩)
def qmeq_462 : qr 462 = qm462 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 462 = qv462 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 462 < 6 by decide,↓reduceDIte,he,qv462,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_86,qmeq_328,qmeq_452]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm463 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-2),(-2,-1),(-1,-3),(-1,-1),(0,-1),(1,-1)},{(-5,1),(-5,3),(-4,1),(-4,2),(-4,3),(-3,-1),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-2,-2),(-2,-1),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-1,-3),(-1,-2),(-1,-1),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,-2),(2,-1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(5,0),(5,1),(5,3)},20⟩)
def qmeq_463 : qr 463 = qm463 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 463 = qv463 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 463 < 6 by decide,↓reduceDIte,he,qv463,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_76,qmeq_170,qmeq_447]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm464 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(1,-2),(2,-2),(3,-2)},{(-2,5),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(7,2),(7,3),(7,4),(7,5)},19⟩)
def qmeq_464 : qr 464 = qm464 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 464 = qv464 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 464 < 6 by decide,↓reduceDIte,he,qv464,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_63,qmeq_224,qmeq_306,qmeq_315,qmeq_358,qmeq_461]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm465 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1)},{(-3,0),(-2,0),(-1,-4),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1)},10⟩)
def qmeq_465 : qr 465 = qm465 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 465 = qv465 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 465 < 6 by decide,↓reduceDIte,he,qv465,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_64,qmeq_285]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm466 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-2),(-2,-1),(-2,0),(-2,1),(-1,-2)},{(-7,-1),(-7,0),(-7,1),(-6,-1),(-6,0),(-6,1),(-6,2),(-5,-1),(-5,0),(-5,1),(-5,2),(-4,-1),(-4,0),(-4,1),(-4,2),(-3,-1),(-3,0),(-3,1),(-3,3),(-3,4),(-3,5),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-1,-2),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(4,-1),(4,0),(4,1),(4,2),(5,-1),(5,0),(5,1),(5,2)},14⟩)
def qmeq_466 : qr 466 = qm466 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 466 = qv466 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 466 < 6 by decide,↓reduceDIte,he,qv466,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_324,qmeq_325,qmeq_360,qmeq_395,qmeq_417]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm467 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,1),(0,2),(0,3)},{(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-1,-2),(-1,-1),(-1,0),(-1,1),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-1),(1,0),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(8,0),(8,1),(8,2),(9,0),(9,2)},21⟩)
def qmeq_467 : qr 467 = qm467 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 467 = qv467 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 467 < 6 by decide,↓reduceDIte,he,qv467,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_64,qmeq_314,qmeq_443]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm468 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,1),(0,2),(1,1),(2,1),(3,1)},{(-2,8),(-1,0),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(4,10),(4,11),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(5,11),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(7,5),(7,6),(7,7),(7,8)},20⟩)
def qmeq_468 : qr 468 = qm468 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 468 = qv468 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 468 < 6 by decide,↓reduceDIte,he,qv468,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_464]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm469 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,1),(0,2),(0,3)},{(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-2),(1,-1),(1,0),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(8,0),(8,1),(8,2),(9,0),(9,2)},21⟩)
def qmeq_469 : qr 469 = qm469 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 469 = qv469 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 469 < 6 by decide,↓reduceDIte,he,qv469,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_314,qmeq_443]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm470 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-1),(1,-1),(2,-1),(3,-1)},{(-2,6),(-1,-2),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,-1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(7,3),(7,4),(7,5),(7,6)},21⟩)
def qmeq_470 : qr 470 = qm470 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 470 = qv470 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 470 < 6 by decide,↓reduceDIte,he,qv470,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_468]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm471 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0),(-1,1),(-1,2),(-1,3)},{(-6,1),(-6,2),(-6,3),(-5,1),(-5,2),(-5,3),(-5,4),(-4,1),(-4,2),(-4,3),(-4,4),(-3,1),(-3,2),(-3,3),(-3,4),(-2,1),(-2,2),(-2,3),(-2,5),(-2,6),(-2,7),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(0,-1),(0,0),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,1),(5,2),(5,3),(5,4),(6,1),(6,2),(6,3),(6,4)},15⟩)
def qmeq_471 : qr 471 = qm471 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 471 = qv471 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 471 < 6 by decide,↓reduceDIte,he,qv471,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_466]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm472 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(1,-3)},{(-5,-2),(-5,-1),(-5,0),(-4,-2),(-4,-1),(-4,0),(-4,1),(-3,-2),(-3,-1),(-3,0),(-3,1),(-2,-2),(-2,-1),(-2,0),(-2,1),(-1,-2),(-1,-1),(-1,0),(-1,2),(-1,3),(-1,4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-4),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-6),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-6),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(4,-6),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(6,-2),(6,-1),(6,0),(6,1),(7,-2),(7,-1),(7,0),(7,1)},15⟩)
def qmeq_472 : qr 472 = qm472 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 472 = qv472 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 472 < 6 by decide,↓reduceDIte,he,qv472,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_466]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm473 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0),(-1,1),(0,1)},{(-6,2),(-6,4),(-5,2),(-5,3),(-5,4),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-3,0),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,-1),(1,0),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,-1),(2,0),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(3,0),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(4,2),(4,3),(4,4),(5,2),(5,4)},20⟩)
def qmeq_473 : qr 473 = qm473 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 473 = qv473 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 473 < 6 by decide,↓reduceDIte,he,qv473,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_121,qmeq_436,qmeq_445]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm474 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(1,-2),(1,0),(2,0),(3,0)},{(-3,2),(-3,4),(-2,2),(-2,3),(-2,4),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,-2),(1,-1),(1,0),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(4,-1),(4,0),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(7,1),(7,2),(7,4)},21⟩)
def qmeq_474 : qr 474 = qm474 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 474 = qv474 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 474 < 6 by decide,↓reduceDIte,he,qv474,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_70,qmeq_83,qmeq_463]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm475 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-2),(-3,0),(-2,0),(-1,0)},{(-6,2),(-6,4),(-5,2),(-5,3),(-5,4),(-4,-1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-4,8),(-4,9),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-1),(4,1),(4,2),(4,4)},21⟩)
def qmeq_475 : qr 475 = qm475 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 475 = qv475 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 475 < 6 by decide,↓reduceDIte,he,qv475,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_63,qmeq_261,qmeq_269,qmeq_457]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm476 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-1),(0,-1),(1,0)},{(-5,1),(-5,3),(-4,1),(-4,2),(-4,3),(-3,-1),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-2,-1),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,-2),(2,-1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(3,-2),(3,-1),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(4,-1),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(5,1),(5,2),(5,3),(6,1),(6,3)},21⟩)
def qmeq_476 : qr 476 = qm476 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 476 = qv476 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 476 < 6 by decide,↓reduceDIte,he,qv476,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_473]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm477 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1)},{(-5,-3),(-5,-2),(-5,-1),(-4,-4),(-4,-3),(-4,-2),(-4,-1),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-1,-7),(-1,-6),(-1,-5),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-6),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-7),(1,-6),(1,-5),(1,-4),(1,-3),(1,-2),(1,0),(1,1),(1,2),(2,-6),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-6),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(4,-6),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(6,-4),(6,-3),(6,-2),(6,-1),(7,-4),(7,-3),(7,-2),(7,-1)},16⟩)
def qmeq_477 : qr 477 = qm477 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 477 = qv477 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 477 < 6 by decide,↓reduceDIte,he,qv477,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_154,qmeq_471]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm478 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-2),(1,-1),(1,0),(2,0)},{(-1,0),(-1,1),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-3),(1,-2),(1,-1),(1,0),(2,-2),(2,-1),(2,0),(3,-1),(3,0),(3,1),(3,2),(3,3),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1)},8⟩)
def qmeq_478 : qr 478 = qm478 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 478 = qv478 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 478 < 6 by decide,↓reduceDIte,he,qv478,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_25,qmeq_165,qmeq_190]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm479 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0)},{(-8,2),(-8,4),(-7,2),(-7,3),(-7,4),(-6,2),(-6,3),(-6,4),(-6,5),(-6,6),(-6,7),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(4,2),(4,3),(4,4),(5,2),(5,4)},21⟩)
def qmeq_479 : qr 479 = qm479 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 479 = qv479 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 479 < 6 by decide,↓reduceDIte,he,qv479,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_443]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm480 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(0,-3),(0,-2),(0,-1),(1,1)},{(-1,-3),(-1,-2),(-1,1),(-1,2),(-1,3),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3)},7⟩)
def qmeq_480 : qr 480 = qm480 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 480 = qv480 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 480 < 6 by decide,↓reduceDIte,he,qv480,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_108]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm481 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-2),(-2,0),(-2,1),(-1,0)},{(-5,0),(-4,-1),(-4,0),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-2,0),(-2,1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,1),(3,2),(4,2)},11⟩)
def qmeq_481 : qr 481 = qm481 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 481 = qv481 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 481 < 6 by decide,↓reduceDIte,he,qv481,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_169,qmeq_206,qmeq_207,qmeq_303,qmeq_309,qmeq_429]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm482 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-2),(-1,-1),(-1,0),(1,-3)},{(-3,-1),(-2,-2),(-2,-1),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(2,-2),(2,-1),(2,0),(3,-1)},7⟩)
def qmeq_482 : qr 482 = qm482 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 482 = qv482 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 482 < 6 by decide,↓reduceDIte,he,qv482,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_218]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm483 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-3),(-2,-2),(-2,-1),(0,-2),(0,-1)},{(-7,-1),(-6,-2),(-6,-1),(-5,-2),(-5,-1),(-4,-2),(-4,-1),(-3,-2),(-3,-1),(-2,-3),(-2,-2),(-2,-1),(-2,1),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-5),(1,-4),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(8,-3),(8,-2),(8,-1),(9,-3),(9,-1)},22⟩)
def qmeq_483 : qr 483 = qm483 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 483 = qv483 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 483 < 6 by decide,↓reduceDIte,he,qv483,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_173,qmeq_192,qmeq_292,qmeq_319,qmeq_475]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm484 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-2,1),(-1,0)},{(-5,1),(-4,-1),(-4,1),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-2,0),(-2,1),(-2,2),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,-1),(2,0),(2,1),(3,-1),(3,1)},12⟩)
def qmeq_484 : qr 484 = qm484 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 484 = qv484 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 484 < 6 by decide,↓reduceDIte,he,qv484,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_25,qmeq_107,qmeq_163,qmeq_349]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm485 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0),(-1,1),(0,-3),(0,-2)},{(-4,1),(-3,-1),(-3,1),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-1,0),(-1,1),(-1,2),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,-1),(3,0),(3,1),(4,-1),(4,1)},13⟩)
def qmeq_485 : qr 485 = qm485 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 485 = qv485 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 485 < 6 by decide,↓reduceDIte,he,qv485,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_2,qmeq_484]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm486 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-1),(1,-4),(1,-3)},{(-3,0),(-2,-2),(-2,0),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-2),(4,-1),(4,0),(5,-2),(5,0)},14⟩)
def qmeq_486 : qr 486 = qm486 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 486 = qv486 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 486 < 6 by decide,↓reduceDIte,he,qv486,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_2,qmeq_485]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm487 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-2),(-1,0),(-1,1),(0,-3),(0,-2)},{(-4,0),(-3,-1),(-3,0),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-1,0),(-1,1),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-1),(4,1),(4,2),(5,2)},12⟩)
def qmeq_487 : qr 487 = qm487 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 487 = qv487 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 487 < 6 by decide,↓reduceDIte,he,qv487,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_2,qmeq_481]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm488 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(-1,-1),(-1,0),(1,0)},{(-3,1),(-3,2),(-3,3),(-3,4),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1)},9⟩)
def qmeq_488 : qr 488 = qm488 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 488 = qv488 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 488 < 6 by decide,↓reduceDIte,he,qv488,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_0,qmeq_247]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm489 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-2),(-2,0),(-1,-2),(-1,0)},{(-5,-1),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-5),(-2,-4),(-2,-3),(-2,-2),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,1)},9⟩)
def qmeq_489 : qr 489 = qm489 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 489 = qv489 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 489 < 6 by decide,↓reduceDIte,he,qv489,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_172,qmeq_197,qmeq_356]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf0 : Finset qCell := ([(-5,-2),(-5,-1),(-5,0),(-4,-2),(-4,-1),(-4,0),(-4,1),(-3,-2),(-3,-1),(-3,0),(-3,1),(-2,-2),(-2,-1),(-2,0),(-2,1),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,2),(-1,3),(-1,4),(0,-3),(0,-2)] : List qCell).toFinset
def qf1 : Finset qCell := ([(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-4),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-6),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-6),(3,-5)] : List qCell).toFinset
def qf2 : Finset qCell := ([(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(4,-6),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1)] : List qCell).toFinset
def qf3 : Finset qCell := ([(5,2),(5,3),(5,4),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(7,-5),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(8,-4),(8,-2),(8,-1)] : List qCell).toFinset
def qf4 : Finset qCell := ([(8,0),(8,1),(8,2),(9,-1),(9,0),(9,1),(9,2),(10,-1),(10,0),(10,1),(10,2)] : List qCell).toFinset
def qm490 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1)},(qf0 ∪ qf1 ∪ qf2 ∪ qf3 ∪ qf4),22⟩)
def qmeq_490 : qr 490 = qm490 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 490 = qv490 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 490 < 6 by decide,↓reduceDIte,he,qv490,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_64,qmeq_111,qmeq_470,qmeq_471]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm491 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0),(0,-3),(0,-2),(0,-1)},{(-3,0),(-2,0),(-1,0),(-1,1),(0,-3),(0,-2),(0,-1),(0,0),(1,-2),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1)},9⟩)
def qmeq_491 : qr 491 = qm491 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 491 = qv491 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 491 < 6 by decide,↓reduceDIte,he,qv491,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_273]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm492 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,0),(1,2),(1,3),(2,-1),(2,0)},{(-3,-1),(-3,1),(-2,-1),(-2,0),(-2,1),(-2,2),(-1,-1),(-1,0),(-1,1),(-1,2),(0,-1),(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,-1),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(6,1),(6,3),(6,4),(7,4)},13⟩)
def qmeq_492 : qr 492 = qm492 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 492 = qv492 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 492 < 6 by decide,↓reduceDIte,he,qv492,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_62,qmeq_107,qmeq_487]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm493 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-2),(-2,-1),(-2,0),(-1,0)},{(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-2,-2),(-2,-1),(-2,0),(-1,0),(-1,1),(-1,2),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,1)},8⟩)
def qmeq_493 : qr 493 = qm493 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 493 = qv493 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 493 < 6 by decide,↓reduceDIte,he,qv493,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_221,qmeq_225,qmeq_236,qmeq_455]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm494 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0),(-1,1)},{(-6,2),(-5,2),(-4,-1),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-1,0),(-1,1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,1)},11⟩)
def qmeq_494 : qr 494 = qm494 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 494 = qv494 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 494 < 6 by decide,↓reduceDIte,he,qv494,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_162,qmeq_268,qmeq_297]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm495 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(-1,-1),(-1,0)},{(-5,-1),(-5,0),(-5,1),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-2,-1),(-2,0),(-2,2),(-2,3),(-2,4),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1)},13⟩)
def qmeq_495 : qr 495 = qm495 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 495 = qv495 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 495 < 6 by decide,↓reduceDIte,he,qv495,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_25,qmeq_167,qmeq_456]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm496 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,0),(2,0),(2,1)},{(-3,-1),(-3,1),(-3,2),(-2,-1),(-2,0),(-2,1),(-2,2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1),(6,-1),(6,0),(6,1),(7,1)},12⟩)
def qmeq_496 : qr 496 = qm496 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 496 = qv496 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 496 < 6 by decide,↓reduceDIte,he,qv496,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_25,qmeq_107,qmeq_163,qmeq_494]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm497 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-1),(1,0),(2,-1),(2,0)},{(-3,1),(-3,3),(-2,0),(-2,1),(-2,2),(-2,3),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(4,-1),(4,0),(4,1),(4,2),(4,3),(5,0),(5,1),(5,2),(5,3),(6,1),(6,2),(6,3),(7,1)},15⟩)
def qmeq_497 : qr 497 = qm497 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 497 = qv497 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 497 < 6 by decide,↓reduceDIte,he,qv497,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_36,qmeq_167,qmeq_410]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm498 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,1),(-1,-2),(-1,-1),(-1,0),(0,1)},{(-5,-1),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,0),(-2,1),(-1,-2),(-1,-1),(-1,0),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,1)},9⟩)
def qmeq_498 : qr 498 = qm498 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 498 = qv498 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 498 < 6 by decide,↓reduceDIte,he,qv498,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_14,qmeq_298]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm499 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(-1,-1),(-1,0)},{(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1),(6,1)},9⟩)
def qmeq_499 : qr 499 = qm499 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 499 = qv499 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 499 < 6 by decide,↓reduceDIte,he,qv499,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_25,qmeq_478,qmeq_493]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm500 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(-1,0),(-1,1),(-1,3),(0,-1)},{(-4,1),(-3,0),(-3,1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-1),(0,0),(0,1),(0,3),(0,4),(0,5),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,0),(3,1),(4,-1),(4,1)},12⟩)
def qmeq_500 : qr 500 = qm500 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 500 = qv500 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 500 < 6 by decide,↓reduceDIte,he,qv500,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_1,qmeq_351]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm501 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-3,1),(-3,2),(-2,0),(-1,0)},{(-4,-1),(-4,1),(-4,3),(-4,4),(-4,5),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,0),(-2,2),(-2,3),(-2,4),(-1,-1),(-1,0),(-1,1),(-1,3),(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5)},10⟩)
def qmeq_501 : qr 501 = qm501 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 501 = qv501 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 501 < 6 by decide,↓reduceDIte,he,qv501,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_316]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm502 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-2),(-2,0),(-1,-2),(-1,0),(0,-2)},{(-5,-1),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-5),(-3,-4),(-3,-3),(-3,-1),(-3,0),(-3,1),(-3,2),(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(-1,3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-1),(2,0),(2,1),(3,-1),(3,1)},8⟩)
def qmeq_502 : qr 502 = qm502 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 502 = qv502 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 502 < 6 by decide,↓reduceDIte,he,qv502,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_173,qmeq_192,qmeq_215,qmeq_232,qmeq_271]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm503 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(1,-2)},{(-1,-5),(-1,-4),(-1,-3),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-2),(1,0),(1,1),(1,2),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,-2),(5,-1),(5,0),(5,1),(5,2),(6,-1),(6,0),(6,1),(6,2),(7,-1),(7,0),(7,1),(7,2)},14⟩)
def qmeq_503 : qr 503 = qm503 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 503 = qv503 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 503 < 6 by decide,↓reduceDIte,he,qv503,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_63,qmeq_419,qmeq_420]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm504 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-2),(1,-1),(1,0),(1,1)},{(-4,-1),(-4,1),(-4,2),(-3,-1),(-3,0),(-3,1),(-3,2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(2,5),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1),(6,1)},13⟩)
def qmeq_504 : qr 504 = qm504 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 504 = qv504 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 504 < 6 by decide,↓reduceDIte,he,qv504,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_159,qmeq_310,qmeq_351,qmeq_381,qmeq_496]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm505 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-2),(0,-1)},{(-2,0),(-2,1),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-3),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1),(6,-1),(6,0),(6,1),(7,1)},11⟩)
def qmeq_505 : qr 505 = qm505 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 505 = qv505 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 505 < 6 by decide,↓reduceDIte,he,qv505,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_173,qmeq_183,qmeq_282,qmeq_499]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm506 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-2),(-2,0),(-1,-3),(-1,-2),(-1,0)},{(-5,-1),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-3,2),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(3,-2),(3,-1),(3,1),(4,-2)},11⟩)
def qmeq_506 : qr 506 = qm506 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 506 = qv506 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 506 < 6 by decide,↓reduceDIte,he,qv506,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_99,qmeq_173,qmeq_200,qmeq_318]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm507 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-3),(-2,-2),(-1,0),(-1,1),(0,-2)},{(-4,0),(-3,-1),(-3,0),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-1,0),(-1,1),(-1,2),(-1,3),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-1),(4,1),(4,2),(5,2)},12⟩)
def qmeq_507 : qr 507 = qm507 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 507 = qv507 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 507 < 6 by decide,↓reduceDIte,he,qv507,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_33,qmeq_151,qmeq_481]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm508 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-1),(-3,0),(-2,-1),(-1,-2),(-1,-1),(0,-1)},{(-5,2),(-4,1),(-4,2),(-4,3),(-4,4),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)},13⟩)
def qmeq_508 : qr 508 = qm508 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 508 = qv508 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 508 < 6 by decide,↓reduceDIte,he,qv508,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_393]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm509 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(-1,-1),(-1,0),(1,0)},{(-6,1),(-5,-1),(-5,0),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-2),(-1,-1),(-1,0),(0,-1),(0,0),(1,-2),(1,-1),(1,0),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1)},8⟩)
def qmeq_509 : qr 509 = qm509 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 509 = qv509 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 509 < 6 by decide,↓reduceDIte,he,qv509,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_68,qmeq_241,qmeq_252,qmeq_455]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm510 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-1),(1,-1),(2,-2),(2,-1),(3,-1)},{(-2,2),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,-1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(6,0),(6,1),(6,2)},14⟩)
def qmeq_510 : qr 510 = qm510 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 510 = qv510 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 510 < 6 by decide,↓reduceDIte,he,qv510,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_508]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm511 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-2),(-2,-2),(-1,-2),(-1,-1),(-1,0),(0,2)},{(-6,-1),(-5,-1),(-5,0),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-2,-2),(-2,-1),(-2,0),(-1,-2),(-1,-1),(-1,0),(-1,3),(-1,4),(-1,5),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-2),(1,-1),(1,0),(1,1),(1,3),(1,4),(1,5),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,1)},10⟩)
def qmeq_511 : qr 511 = qm511 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 511 = qv511 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 511 < 6 by decide,↓reduceDIte,he,qv511,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_15,qmeq_331,qmeq_380]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm512 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(-1,0),(-1,2),(-1,3)},{(-4,2),(-3,-1),(-3,1),(-3,2),(-2,-1),(-2,0),(-2,1),(-2,2),(-1,0),(-1,2),(-1,3),(-1,4),(-1,5),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,-1),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(4,1),(4,3),(4,4),(5,4)},13⟩)
def qmeq_512 : qr 512 = qm512 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 512 = qv512 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 512 < 6 by decide,↓reduceDIte,he,qv512,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_62,qmeq_107,qmeq_507]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm513 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-1),(1,-1),(2,-1),(3,-1)},{(-2,2),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,-1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(6,0),(6,1),(6,2)},14⟩)
def qmeq_513 : qr 513 = qm513 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 513 = qv513 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 513 < 6 by decide,↓reduceDIte,he,qv513,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_396]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm514 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,-1),(-2,0),(-1,-1),(-1,0)},{(-8,2),(-8,4),(-7,2),(-7,3),(-7,4),(-6,2),(-6,3),(-6,4),(-6,5),(-6,6),(-6,7),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)},21⟩)
def qmeq_514 : qr 514 = qm514 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 514 = qv514 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 514 < 6 by decide,↓reduceDIte,he,qv514,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_57,qmeq_443,qmeq_510]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm515 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-4,-1),(-3,-1),(-3,0),(-1,0)},{(-4,-2),(-4,-1),(-4,1),(-4,2),(-4,3),(-4,4),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3),(3,4)},14⟩)
def qmeq_515 : qr 515 = qm515 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 515 = qv515 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 515 < 6 by decide,↓reduceDIte,he,qv515,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_2,qmeq_512]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm516 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-2),(-1,0),(0,-3),(0,-2)},{(-6,-2),(-5,-2),(-5,-1),(-5,1),(-4,-4),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(1,2),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1)},12⟩)
def qmeq_516 : qr 516 = qm516 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 516 = qv516 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 516 < 6 by decide,↓reduceDIte,he,qv516,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_10,qmeq_244,qmeq_329,qmeq_506]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm517 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-1),(0,-3),(0,-1)},{(-5,-2),(-5,0),(-5,1),(-4,-2),(-4,-1),(-4,0),(-4,1),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-1,-4),(-1,-3),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-2),(2,-1),(2,0),(3,-2),(3,-1),(3,0),(4,-2),(4,-1),(4,0),(5,0)},13⟩)
def qmeq_517 : qr 517 = qm517 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 517 = qv517 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 517 < 6 by decide,↓reduceDIte,he,qv517,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_140,qmeq_193,qmeq_496]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm518 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-1),(1,0),(2,-1),(2,0)},{(-5,2),(-5,4),(-4,2),(-4,3),(-4,4),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-2,0),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(4,0),(4,1),(4,2),(4,3),(4,4),(5,-1),(5,0),(5,1),(5,2),(5,3),(6,1),(6,2),(6,3)},22⟩)
def qmeq_518 : qr 518 = qm518 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 518 = qv518 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 518 < 6 by decide,↓reduceDIte,he,qv518,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_9,qmeq_514]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm519 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-1,-3),(-1,-2),(-1,-1)},{(-6,-1),(-5,-2),(-5,-1),(-5,0),(-5,1),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-2),(3,-1),(3,0),(3,1),(4,-2),(4,-1),(4,0),(5,0)},12⟩)
def qmeq_519 : qr 519 = qm519 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 519 = qv519 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 519 < 6 by decide,↓reduceDIte,he,qv519,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_38,qmeq_311,qmeq_408,qmeq_498]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm520 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-3),(-1,0),(1,-2),(1,0)},{(-5,-1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-2),(-1,-1),(-1,0),(0,-5),(0,-4),(0,-3),(0,-1),(0,0),(0,1),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(2,-5),(2,-4),(2,-3),(2,-1),(2,0),(2,1),(2,2),(3,-1),(3,0),(3,1),(4,-1),(4,1)},8⟩)
def qmeq_520 : qr 520 = qm520 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 520 = qv520 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 520 < 6 by decide,↓reduceDIte,he,qv520,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_200,qmeq_215,qmeq_252,qmeq_254,qmeq_271]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm521 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-4),(-1,-3),(0,-3),(0,-1)},{(-6,1),(-5,-2),(-5,0),(-5,1),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-2,-4),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-3),(0,-2),(0,-1),(0,0),(1,-4),(1,-3),(1,-2),(1,-1),(2,-4),(2,-3),(2,-2),(2,-1),(3,-4),(3,-3),(3,-2),(3,-1),(4,-4),(4,-2)},14⟩)
def qmeq_521 : qr 521 = qm521 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 521 = qv521 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 521 < 6 by decide,↓reduceDIte,he,qv521,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_2,qmeq_492]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm522 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(0,-1),(0,1)},{(-5,-2),(-5,0),(-4,-2),(-4,-1),(-4,0),(-3,-2),(-3,-1),(-3,0),(-2,-2),(-2,-1),(-2,1),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,2),(1,3),(1,4),(2,-2),(2,-1),(2,0),(2,2),(3,-2),(3,-1),(3,0),(3,2),(4,-2),(4,-1),(4,0),(5,-2)},9⟩)
def qmeq_522 : qr 522 = qm522 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 522 = qv522 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 522 < 6 by decide,↓reduceDIte,he,qv522,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_176,qmeq_252,qmeq_338]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm523 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,4),(-2,0),(-2,1),(-2,2),(-1,0)},{(-7,1),(-7,3),(-6,1),(-6,2),(-6,3),(-5,1),(-5,2),(-5,3),(-4,0),(-4,1),(-4,2),(-4,3),(-4,5),(-4,6),(-4,7),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-2,0),(-2,1),(-2,2),(-2,5),(-2,6),(-2,7),(-1,0),(-1,1),(-1,2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,1),(3,2),(4,2)},11⟩)
def qmeq_523 : qr 523 = qm523 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 523 = qv523 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 523 < 6 by decide,↓reduceDIte,he,qv523,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_25,qmeq_107,qmeq_303,qmeq_511]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm524 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1)},{(-5,-2),(-5,0),(-5,1),(-4,-2),(-4,-1),(-4,0),(-4,1),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-2),(4,-1),(4,0),(4,1),(5,-2),(5,0),(5,1)},14⟩)
def qmeq_524 : qr 524 = qm524 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 524 = qv524 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 524 < 6 by decide,↓reduceDIte,he,qv524,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_180,qmeq_261,qmeq_504]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm525 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-2,1),(-2,2),(-1,0)},{(-7,1),(-7,3),(-6,1),(-6,2),(-6,3),(-5,1),(-5,2),(-5,3),(-4,1),(-4,2),(-4,3),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-2,0),(-2,1),(-2,2),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,4),(-1,5),(-1,6),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,1),(3,2),(3,3),(4,1),(4,2),(4,3),(5,1)},11⟩)
def qmeq_525 : qr 525 = qm525 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 525 = qv525 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 525 < 6 by decide,↓reduceDIte,he,qv525,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_25,qmeq_107,qmeq_303,qmeq_430]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm526 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(-1,0),(0,-2)},{(-6,1),(-6,2),(-5,-1),(-5,0),(-5,1),(-5,2),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-1,-7),(-1,-6),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-6),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,-6),(1,-5),(1,-4),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1),(5,-1)},17⟩)
def qmeq_526 : qr 526 = qm526 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 526 = qv526 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 526 < 6 by decide,↓reduceDIte,he,qv526,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_327,qmeq_359,qmeq_399,qmeq_416,qmeq_489]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm527 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-3),(1,-2),(1,-1)},{(-5,1),(-4,-2),(-4,-1),(-4,1),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-3),(1,-2),(1,-1),(1,0),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,-2),(5,-1),(5,0),(5,1),(6,-2),(6,-1),(6,0),(7,0)},13⟩)
def qmeq_527 : qr 527 = qm527 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 527 = qv527 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 527 < 6 by decide,↓reduceDIte,he,qv527,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_38,qmeq_387,qmeq_491,qmeq_519]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm528 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(-2,1),(0,1)},{(-7,0),(-7,2),(-6,0),(-6,1),(-6,2),(-5,0),(-5,1),(-5,2),(-4,0),(-4,1),(-4,2),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,-1),(-2,0),(-2,1),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,2),(1,3),(1,4),(1,5),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(4,-2),(4,-1),(4,0),(4,1),(4,3)},12⟩)
def qmeq_528 : qr 528 = qm528 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 528 = qv528 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 528 < 6 by decide,↓reduceDIte,he,qv528,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_226,qmeq_359,qmeq_386,qmeq_414,qmeq_502]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm529 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,0),(2,0),(3,0)},{(-2,-1),(-2,1),(-2,4),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(1,5),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(7,1),(7,2),(7,3),(7,4)},16⟩)
def qmeq_529 : qr 529 = qm529 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 529 = qv529 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 529 < 6 by decide,↓reduceDIte,he,qv529,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_63,qmeq_64,qmeq_441]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm530 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-1),(0,1),(2,-1),(2,1)},{(-4,-3),(-4,-1),(-4,0),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-1,-4),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1),(5,2),(6,0),(6,2)},13⟩)
def qmeq_530 : qr 530 = qm530 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 530 = qv530 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 530 < 6 by decide,↓reduceDIte,he,qv530,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_271,qmeq_283,qmeq_336,qmeq_456]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm531 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-2),(1,-2)},{(-5,-1),(-5,1),(-5,2),(-4,-1),(-4,0),(-4,1),(-4,2),(-3,-3),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-1,-7),(-1,-6),(-1,-5),(-1,-4),(-1,-3),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-7),(0,-6),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-7),(1,-6),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,-7),(2,-6),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,-1),(5,0),(5,1),(6,-1)},18⟩)
def qmeq_531 : qr 531 = qm531 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 531 = qv531 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 531 < 6 by decide,↓reduceDIte,he,qv531,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_336,qmeq_340,qmeq_394,qmeq_401,qmeq_423,qmeq_425,qmeq_453,qmeq_526]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm532 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(0,-3),(0,-2),(0,-1)},{(-5,0),(-4,-2),(-4,-1),(-4,0),(-3,-2),(-3,-1),(-3,0),(-2,-2),(-2,-1),(-2,0),(-1,-4),(-1,-3),(-1,-1),(-1,0),(-1,2),(-1,3),(-1,4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-2),(4,-1),(4,0),(4,1),(5,-2),(5,0),(5,1)},14⟩)
def qmeq_532 : qr 532 = qm532 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 532 = qv532 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 532 < 6 by decide,↓reduceDIte,he,qv532,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_504]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def ql533b0 : List qCell := [(-5,-1),(-4,-4),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-2,-6),(-2,-5),(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3)]
def ql533b1 : List qCell := [(-2,4),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-5),(1,-4),(1,-3),(1,-2),(1,0),(1,1),(1,2),(1,3),(2,-4),(2,-3)]
def ql533b2 : List qCell := [(2,-2),(2,0),(2,1),(3,-4),(3,-3),(3,-2),(3,0),(4,-4),(4,-3),(4,-2),(5,-2)]
def ql533 : List qCell := ql533b0 ++ ql533b1 ++ ql533b2
def qn533 : (ql533).Nodup := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qm533 : qR := ⟨{(0,-2),(0,-1)},⟨(ql533 : Multiset qCell), Multiset.coe_nodup.mpr qn533⟩,11⟩
def qmeq_533 : qr 533 = qm533 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 533 = qv533 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 533 < 6 by decide,↓reduceDIte,he,qv533,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_173,qmeq_217,qmeq_318,qmeq_319,qmeq_407]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm534 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(-2,2),(-1,-1),(-1,0),(-1,2)},{(-5,3),(-5,5),(-4,-1),(-4,2),(-4,3),(-4,4),(-4,5),(-3,-1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-2,-1),(-2,0),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-1,-1),(-1,0),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1),(4,2),(4,3),(4,4),(4,5),(5,3)},16⟩)
def qmeq_534 : qr 534 = qm534 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 534 = qv534 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 534 < 6 by decide,↓reduceDIte,he,qv534,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_12,qmeq_434]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm535 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-1),(0,-1)},{(-5,-2),(-5,0),(-5,1),(-5,2),(-5,3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-4),(1,-3),(1,-2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(4,0),(4,1),(4,2),(4,3),(5,0),(5,1),(5,3)},15⟩)
def qmeq_535 : qr 535 = qm535 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 535 = qv535 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 535 < 6 by decide,↓reduceDIte,he,qv535,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_25,qmeq_321,qmeq_426,qmeq_444]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm536 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-2),(-1,0),(0,-3),(0,-2)},{(-4,1),(-4,3),(-3,-3),(-3,0),(-3,1),(-3,2),(-3,3),(-2,-3),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-1),(4,0),(4,1),(4,2),(4,3),(5,-1),(5,0),(5,1),(5,2),(5,3),(6,1)},17⟩)
def qmeq_536 : qr 536 = qm536 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 536 = qv536 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 536 < 6 by decide,↓reduceDIte,he,qv536,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_26,qmeq_244,qmeq_307,qmeq_534]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm537 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,1),(-2,-1),(-2,1),(0,-1),(0,1)},{(-7,-2),(-7,0),(-6,-2),(-6,-1),(-6,0),(-5,-2),(-5,-1),(-5,0),(-4,-2),(-4,-1),(-4,0),(-3,-2),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,2),(-1,3),(-1,4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(5,0)},11⟩)
def qmeq_537 : qr 537 = qm537 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 537 = qv537 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 537 < 6 by decide,↓reduceDIte,he,qv537,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_176,qmeq_271,qmeq_330,qmeq_373]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm538 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,0),(2,0),(3,0)},{(-2,-1),(-2,1),(-2,7),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(4,10),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(7,4),(7,5),(7,6),(7,7)},22⟩)
def qmeq_538 : qr 538 = qm538 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 538 = qv538 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 538 < 6 by decide,↓reduceDIte,he,qv538,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_63,qmeq_64,qmeq_470]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm539 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(1,-3),(1,-2)},{(-5,-2),(-4,-4),(-4,-2),(-4,-1),(-4,1),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,-1),(5,0),(5,1),(6,-1),(6,1)},18⟩)
def qmeq_539 : qr 539 = qm539 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 539 = qv539 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 539 < 6 by decide,↓reduceDIte,he,qv539,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_51,qmeq_428,qmeq_488,qmeq_516]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm540 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(1,-3),(1,-2)},{(-3,-3),(-3,1),(-3,3),(-2,-3),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-4),(-1,-3),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,-1),(5,0),(5,1),(5,2),(5,3),(6,-1),(6,0),(6,1),(6,2),(6,3),(7,1)},18⟩)
def qmeq_540 : qr 540 = qm540 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 540 = qv540 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 540 < 6 by decide,↓reduceDIte,he,qv540,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_51,qmeq_88,qmeq_334,qmeq_536]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm541 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-2),(-1,-2),(0,-2),(0,-1)},{(-5,0),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-1,-2),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-5),(1,-4),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,0),(4,1),(4,2),(5,0),(5,2)},14⟩)
def qmeq_541 : qr 541 = qm541 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 541 = qv541 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 541 < 6 by decide,↓reduceDIte,he,qv541,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_142,qmeq_160,qmeq_194,qmeq_236,qmeq_412,qmeq_501]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm542 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(1,-3)},{(-3,-1),(-2,-1),(-1,-2),(-1,-1),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-4),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(5,0),(5,1),(5,2),(5,3),(5,4),(6,1),(6,2),(6,3),(6,4),(7,1),(7,2),(7,3),(7,4)},17⟩)
def qmeq_542 : qr 542 = qm542 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 542 = qv542 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 542 < 6 by decide,↓reduceDIte,he,qv542,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_442]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm543 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-2,1),(-1,0)},{(-6,3),(-5,-1),(-5,3),(-4,-1),(-4,1),(-4,2),(-4,3),(-3,-2),(-3,-1),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-1,-1),(-1,0),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(3,-2),(3,-1),(3,1),(4,-2)},11⟩)
def qmeq_543 : qr 543 = qm543 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 543 = qv543 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 543 < 6 by decide,↓reduceDIte,he,qv543,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_107,qmeq_318,qmeq_493]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm544 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-1),(1,0),(2,-1),(2,0)},{(-3,1),(-2,0),(-2,1),(-1,0),(-1,1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(8,-2),(8,-1),(8,0),(8,1),(8,2),(8,3),(9,-2),(9,-1),(9,0),(9,1),(9,2),(10,-2),(10,0),(10,2)},18⟩)
def qmeq_544 : qr 544 = qm544 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 544 = qv544 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 544 < 6 by decide,↓reduceDIte,he,qv544,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_9,qmeq_263,qmeq_451]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm545 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(0,-2),(0,-1),(1,-2),(1,-1)},{(-4,1),(-4,3),(-3,-1),(-3,1),(-3,2),(-3,3),(-2,-1),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(5,0),(5,1),(5,2),(5,3),(6,1),(6,3)},20⟩)
def qmeq_545 : qr 545 = qm545 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 545 = qv545 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 545 < 6 by decide,↓reduceDIte,he,qv545,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_153,qmeq_256,qmeq_343,qmeq_448]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm546 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,0),(2,0),(3,-2),(3,0)},{(-2,-1),(-1,-1),(-1,0),(-1,2),(-1,3),(-1,4),(0,-3),(0,-2),(0,-1),(0,0),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,-3),(2,-2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(3,-2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(4,-2),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(7,2),(7,3),(7,4),(8,2),(8,4)},21⟩)
def qmeq_546 : qr 546 = qm546 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 546 = qv546 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 546 < 6 by decide,↓reduceDIte,he,qv546,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_64,qmeq_443,qmeq_482]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm547 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-1),(1,0),(2,0),(3,0)},{(-3,-1),(-3,1),(-3,2),(-3,3),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(7,2),(7,3),(7,4),(8,2),(8,4)},21⟩)
def qmeq_547 : qr 547 = qm547 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 547 = qv547 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 547 < 6 by decide,↓reduceDIte,he,qv547,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_131,qmeq_443,qmeq_510]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm548 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-1,-1),(0,-1)},{(-5,0),(-5,1),(-5,2),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-4),(1,-3),(1,-2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(4,0),(4,1),(4,2),(4,3),(5,0),(5,1),(5,3)},15⟩)
def qmeq_548 : qr 548 = qm548 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 548 = qv548 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 548 < 6 by decide,↓reduceDIte,he,qv548,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_25,qmeq_321,qmeq_426,qmeq_541]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm549 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-3),(-1,0),(1,0)},{(-5,1),(-4,-4),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,1),(5,2),(5,3),(5,4)},17⟩)
def qmeq_549 : qr 549 = qm549 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 549 = qv549 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 549 < 6 by decide,↓reduceDIte,he,qv549,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_252,qmeq_326,qmeq_330,qmeq_385,qmeq_529]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm550 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-1),(0,1),(2,1)},{(-5,0),(-5,1),(-5,2),(-5,3),(-4,-3),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-4),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(-1,4),(-1,5),(-1,6),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0),(5,1),(5,2),(5,3),(6,0),(6,1),(6,2),(6,3),(7,0),(7,1),(7,2),(7,3)},13⟩)
def qmeq_550 : qr 550 = qm550 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 550 = qv550 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 550 < 6 by decide,↓reduceDIte,he,qv550,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_172,qmeq_215,qmeq_424,qmeq_456]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm551 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,1),(0,2)},{(-6,3),(-5,1),(-5,2),(-5,3),(-4,1),(-4,2),(-4,3),(-4,4),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-1,-3),(-1,-2),(-1,-1),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(5,1),(5,2),(5,4),(6,4)},14⟩)
def qmeq_551 : qr 551 = qm551 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 551 = qv551 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 551 < 6 by decide,↓reduceDIte,he,qv551,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_172,qmeq_176,qmeq_300,qmeq_319,qmeq_527]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm552 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0)},{(-8,2),(-8,4),(-7,2),(-7,3),(-7,4),(-6,2),(-6,3),(-6,4),(-6,5),(-6,6),(-6,7),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-2,-5),(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,2),(1,3),(1,4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(4,-3),(4,-2),(4,-1),(4,1),(5,-1)},21⟩)
def qmeq_552 : qr 552 = qm552 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 552 = qv552 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 552 < 6 by decide,↓reduceDIte,he,qv552,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_64,qmeq_404,qmeq_443,qmeq_504]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf5 : Finset qCell := ([(-5,-2),(-5,-1),(-5,0),(-5,1),(-4,-2),(-4,-1),(-4,0),(-4,1),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-1,-2),(-1,-1),(-1,0)] : List qCell).toFinset
def qf6 : Finset qCell := ([(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-4),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-6),(2,-5),(2,-4),(2,-3)] : List qCell).toFinset
def qf7 : Finset qCell := ([(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,-6),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(4,-6),(4,-5),(4,-4)] : List qCell).toFinset
def qf8 : Finset qCell := ([(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3)] : List qCell).toFinset
def qf9 : Finset qCell := ([(6,4),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4)] : List qCell).toFinset
def qm553 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1)},(qf5 ∪ qf6 ∪ qf7 ∪ qf8 ∪ qf9),17⟩)
def qmeq_553 : qr 553 = qm553 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 553 = qv553 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 553 < 6 by decide,↓reduceDIte,he,qv553,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_63,qmeq_180,qmeq_261,qmeq_442,qmeq_471,qmeq_504]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm554 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-2),(0,-1),(1,-1),(1,1),(2,1),(3,1)},{(-3,3),(-3,5),(-2,0),(-2,2),(-2,3),(-2,4),(-2,5),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,-1),(1,0),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(4,0),(4,1),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(7,2),(7,3),(7,5)},22⟩)
def qmeq_554 : qr 554 = qm554 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 554 = qv554 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 554 < 6 by decide,↓reduceDIte,he,qv554,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_30,qmeq_96,qmeq_474]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf10 : Finset qCell := ([(-8,2),(-8,4),(-7,2),(-7,3),(-7,4),(-6,2),(-6,3),(-6,4),(-6,5),(-6,6),(-6,7),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-3,0)] : List qCell).toFinset
def qf11 : Finset qCell := ([(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-2,-5),(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-1,-5),(-1,-4),(-1,-3)] : List qCell).toFinset
def qf12 : Finset qCell := ([(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8)] : List qCell).toFinset
def qf13 : Finset qCell := ([(0,9),(1,-4),(1,-3),(1,-2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-1)] : List qCell).toFinset
def qf14 : Finset qCell := ([(4,1),(4,2),(4,3),(5,1)] : List qCell).toFinset
def qm555 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0)},(qf10 ∪ qf11 ∪ qf12 ∪ qf13 ∪ qf14),21⟩)
def qmeq_555 : qr 555 = qm555 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 555 = qv555 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 555 < 6 by decide,↓reduceDIte,he,qv555,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_55,qmeq_443,qmeq_471,qmeq_504,qmeq_513]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm556 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-3),(-2,-3),(-2,0),(-1,-4),(-1,-3),(0,-3)},{(-6,1),(-5,-4),(-5,-3),(-5,-2),(-5,-1),(-5,0),(-5,1),(-5,4),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-2,-3),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-1,-4),(-1,-3),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2),(4,3),(4,4)},18⟩)
def qmeq_556 : qr 556 = qm556 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 556 = qv556 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 556 < 6 by decide,↓reduceDIte,he,qv556,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_34,qmeq_549]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf15 : Finset qCell := ([(-6,-1),(-6,0),(-6,1),(-6,3),(-6,4),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4)] : List qCell).toFinset
def qf16 : Finset qCell := ([(-3,5),(-3,6),(-3,7),(-3,8),(-2,-5),(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2)] : List qCell).toFinset
def qf17 : Finset qCell := ([(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1)] : List qCell).toFinset
def qf18 : Finset qCell := ([(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(3,-4),(3,-3),(3,-2),(3,-1)] : List qCell).toFinset
def qf19 : Finset qCell := ([(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,-1),(5,0),(5,1),(5,3),(5,4)] : List qCell).toFinset
def qm557 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0)},(qf15 ∪ qf16 ∪ qf17 ∪ qf18 ∪ qf19),19⟩)
def qmeq_557 : qr 557 = qm557 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 557 = qv557 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 557 < 6 by decide,↓reduceDIte,he,qv557,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_406,qmeq_411,qmeq_460,qmeq_531]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf20 : Finset qCell := ([(-8,2),(-8,4),(-7,2),(-7,3),(-7,4),(-6,2),(-6,3),(-6,4),(-6,5),(-6,6),(-6,7),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-3,0)] : List qCell).toFinset
def qf21 : Finset qCell := ([(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3)] : List qCell).toFinset
def qf22 : Finset qCell := ([(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,-1)] : List qCell).toFinset
def qf23 : Finset qCell := ([(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6)] : List qCell).toFinset
def qf24 : Finset qCell := ([(4,7),(5,-1),(5,2),(5,3),(5,4),(6,2),(6,3),(6,4)] : List qCell).toFinset
def qm558 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0)},(qf20 ∪ qf21 ∪ qf22 ∪ qf23 ∪ qf24),21⟩)
def qmeq_558 : qr 558 = qm558 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 558 = qv558 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 558 < 6 by decide,↓reduceDIte,he,qv558,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_180,qmeq_442,qmeq_443,qmeq_513]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm559 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-4),(0,-3),(0,-2),(0,-1)},{(-3,-1),(-2,-1),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-3),(1,-2),(1,-1),(1,1),(1,2),(1,3),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(4,-6),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(5,-6),(5,-5),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(6,-6),(6,-5),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(7,-6),(7,-5),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(8,-4),(8,-3),(8,-2),(8,-1),(8,0),(8,2),(9,-4),(9,-3),(9,-2),(9,-1),(10,-4),(10,-3),(10,-2),(10,-1)},23⟩)
def qmeq_559 : qr 559 = qm559 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 559 = qv559 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 559 < 6 by decide,↓reduceDIte,he,qv559,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_7,qmeq_155,qmeq_228,qmeq_538]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf25 : Finset qCell := ([(-7,1),(-6,0),(-6,1),(-5,0),(-5,1),(-4,0),(-4,1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-2,3),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7)] : List qCell).toFinset
def qf26 : Finset qCell := ([(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,-3)] : List qCell).toFinset
def qf27 : Finset qCell := ([(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(4,-3),(4,-2),(4,-1),(4,0),(4,1)] : List qCell).toFinset
def qf28 : Finset qCell := ([(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(7,-1),(7,0),(7,1),(7,2),(7,3)] : List qCell).toFinset
def qf29 : Finset qCell := ([(7,4),(7,5),(8,-1),(8,0),(8,1),(9,-1),(9,1)] : List qCell).toFinset
def qm560 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(-2,1),(0,1)},(qf25 ∪ qf26 ∪ qf27 ∪ qf28 ∪ qf29),23⟩)
def qmeq_560 : qr 560 = qm560 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 560 = qv560 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 560 < 6 by decide,↓reduceDIte,he,qv560,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_356,qmeq_359,qmeq_416,qmeq_483,qmeq_517]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf30 : Finset qCell := ([(-7,2),(-7,4),(-6,-1),(-6,0),(-6,1),(-6,2),(-6,3),(-6,4),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6)] : List qCell).toFinset
def qf31 : Finset qCell := ([(-4,7),(-3,-2),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-2,-2),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(-1,3)] : List qCell).toFinset
def qf32 : Finset qCell := ([(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2)] : List qCell).toFinset
def qf33 : Finset qCell := ([(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,-1),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(4,1),(4,2)] : List qCell).toFinset
def qf34 : Finset qCell := ([(4,3),(4,4),(5,1),(5,2),(5,4)] : List qCell).toFinset
def qm561 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-2),(-2,0),(-1,0)},(qf30 ∪ qf31 ∪ qf32 ∪ qf33 ∪ qf34),22⟩)
def qmeq_561 : qr 561 = qm561 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 561 = qv561 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 561 < 6 by decide,↓reduceDIte,he,qv561,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_173,qmeq_176,qmeq_236,qmeq_263,qmeq_295,qmeq_535,qmeq_546]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qm562 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(0,-3),(0,-2),(0,-1)},{(-3,0),(-2,0),(-1,-4),(-1,-3),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-2),(1,-1),(1,0),(1,2),(1,3),(1,4),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(5,-5),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(6,-5),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(7,-5),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(8,-3),(8,-2),(8,-1),(8,0),(8,1),(8,3),(9,-3),(9,-2),(9,-1),(9,0),(10,-3),(10,-2),(10,-1),(10,0)},24⟩)
def qmeq_562 : qr 562 = qm562 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 562 = qv562 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 562 < 6 by decide,↓reduceDIte,he,qv562,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_6,qmeq_559]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf35 : Finset qCell := ([(-5,2),(-5,4),(-4,1),(-4,2),(-4,3),(-4,4),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8)] : List qCell).toFinset
def qf36 : Finset qCell := ([(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,-1),(1,0),(1,1),(1,2),(1,3)] : List qCell).toFinset
def qf37 : Finset qCell := ([(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)] : List qCell).toFinset
def qf38 : Finset qCell := ([(3,6),(3,7),(3,8),(3,9),(3,10),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(4,10),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7)] : List qCell).toFinset
def qf39 : Finset qCell := ([(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(7,2),(7,4)] : List qCell).toFinset
def qm563 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-1),(1,0),(2,-1),(2,0)},(qf35 ∪ qf36 ∪ qf37 ∪ qf38 ∪ qf39),23⟩)
def qmeq_563 : qr 563 = qm563 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 563 = qv563 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 563 < 6 by decide,↓reduceDIte,he,qv563,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_167,qmeq_330,qmeq_514,qmeq_538,qmeq_545]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf40 : Finset qCell := ([(-7,-1),(-7,0),(-7,1),(-6,-1),(-6,0),(-6,1),(-5,-1),(-5,0),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-2,-2),(-2,-1),(-2,0),(-2,2),(-1,-6),(-1,-5),(-1,-4),(-1,-3)] : List qCell).toFinset
def qf41 : Finset qCell := ([(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-6),(1,-5),(1,-4),(1,-3),(1,-2)] : List qCell).toFinset
def qf42 : Finset qCell := ([(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1)] : List qCell).toFinset
def qf43 : Finset qCell := ([(3,2),(3,3),(3,4),(3,5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(6,-2),(6,-1),(6,0)] : List qCell).toFinset
def qf44 : Finset qCell := ([(6,1),(6,2),(6,3),(6,4),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(8,-2),(8,-1),(8,0),(9,-2),(9,0)] : List qCell).toFinset
def qm564 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-2),(-2,-1),(-2,0)},(qf40 ∪ qf41 ∪ qf42 ∪ qf43 ∪ qf44),24⟩)
def qmeq_564 : qr 564 = qm564 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 564 = qv564 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 564 < 6 by decide,↓reduceDIte,he,qv564,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_336,qmeq_340,qmeq_401,qmeq_421,qmeq_423,qmeq_425,qmeq_509,qmeq_528,qmeq_560]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf45 : Finset qCell := ([(-5,2),(-5,4),(-4,2),(-4,3),(-4,4),(-3,-1),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-1,-1),(-1,0)] : List qCell).toFinset
def qf46 : Finset qCell := ([(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] : List qCell).toFinset
def qf47 : Finset qCell := ([(1,6),(1,7),(1,8),(1,9),(1,10),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7)] : List qCell).toFinset
def qf48 : Finset qCell := ([(3,8),(3,9),(3,10),(4,-1),(4,0),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(4,10),(5,-1),(5,0),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(6,-1),(6,2),(6,3)] : List qCell).toFinset
def qf49 : Finset qCell := ([(6,4),(6,5),(6,6),(6,7),(7,2),(7,4)] : List qCell).toFinset
def qm565 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-1),(1,0),(2,0),(3,0)},(qf45 ∪ qf46 ∪ qf47 ∪ qf48 ∪ qf49),23⟩)
def qmeq_565 : qr 565 = qm565 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 565 = qv565 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 565 < 6 by decide,↓reduceDIte,he,qv565,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_131,qmeq_144,qmeq_443,qmeq_459,qmeq_538]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf50 : Finset qCell := ([(-5,-2),(-5,-1),(-5,0),(-5,1),(-4,-2),(-4,-1),(-4,0),(-4,1),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-1,-2),(-1,-1),(-1,0)] : List qCell).toFinset
def qf51 : Finset qCell := ([(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-6),(2,-5),(2,-4),(2,-3),(2,-2)] : List qCell).toFinset
def qf52 : Finset qCell := ([(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,-6),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(4,-6),(4,-5),(4,-4),(4,-3)] : List qCell).toFinset
def qf53 : Finset qCell := ([(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4)] : List qCell).toFinset
def qf54 : Finset qCell := ([(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4)] : List qCell).toFinset
def qm566 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1),(1,-3)},(qf50 ∪ qf51 ∪ qf52 ∪ qf53 ∪ qf54),17⟩)
def qmeq_566 : qr 566 = qm566 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 566 = qv566 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 566 < 6 by decide,↓reduceDIte,he,qv566,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_180,qmeq_314,qmeq_442,qmeq_466,qmeq_504]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf55 : Finset qCell := ([(-5,-4),(-5,-2),(-5,2),(-5,4),(-4,-4),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7)] : List qCell).toFinset
def qf56 : Finset qCell := ([(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-1,-4),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(0,-4),(0,-3)] : List qCell).toFinset
def qf57 : Finset qCell := ([(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,-3),(1,-2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(2,-4),(2,-3),(2,-2)] : List qCell).toFinset
def qf58 : Finset qCell := ([(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(4,-1),(4,0)] : List qCell).toFinset
def qf59 : Finset qCell := ([(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(5,-1),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(6,1),(6,2),(6,3),(6,4),(7,1),(7,2),(7,4)] : List qCell).toFinset
def qm567 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-4),(0,-4),(0,-3),(0,-2),(1,0)},(qf55 ∪ qf56 ∪ qf57 ∪ qf58 ∪ qf59),23⟩)
def qmeq_567 : qr 567 = qm567 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 567 = qv567 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 567 < 6 by decide,↓reduceDIte,he,qv567,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_21,qmeq_500,qmeq_561]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf60 : Finset qCell := ([(-7,2),(-7,4),(-6,2),(-6,3),(-6,4),(-5,-1),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-4,8),(-3,-1),(-3,0)] : List qCell).toFinset
def qf61 : Finset qCell := ([(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-3,10),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-1,-1),(-1,0),(-1,1),(-1,2)] : List qCell).toFinset
def qf62 : Finset qCell := ([(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(1,0),(1,1),(1,2),(1,3),(1,4)] : List qCell).toFinset
def qf63 : Finset qCell := ([(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)] : List qCell).toFinset
def qf64 : Finset qCell := ([(3,6),(3,7),(3,8),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(5,1),(5,2),(5,3),(5,4),(6,2),(6,4)] : List qCell).toFinset
def qm568 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(-1,0),(1,0)},(qf60 ∪ qf61 ∪ qf62 ∪ qf63 ∪ qf64),24⟩)
def qmeq_568 : qr 568 = qm568 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 568 = qv568 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 568 < 6 by decide,↓reduceDIte,he,qv568,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_275,qmeq_330,qmeq_538,qmeq_547,qmeq_565]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf65 : Finset qCell := ([(-5,2),(-5,4),(-4,1),(-4,2),(-4,3),(-4,4),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8)] : List qCell).toFinset
def qf66 : Finset qCell := ([(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8)] : List qCell).toFinset
def qf67 : Finset qCell := ([(0,9),(0,10),(1,-4),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(2,-3),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)] : List qCell).toFinset
def qf68 : Finset qCell := ([(2,7),(2,8),(2,9),(2,10),(3,-3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7)] : List qCell).toFinset
def qf69 : Finset qCell := ([(4,8),(4,9),(4,10),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(6,-1),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(7,2),(7,3),(7,4),(8,2)] : List qCell).toFinset
def qf70 : Finset qCell := ([(8,4)] : List qCell).toFinset
def qm569 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(1,-4),(1,-3),(2,-3),(2,-1),(2,0),(3,-3)},(qf65 ∪ qf66 ∪ qf67 ∪ qf68 ∪ qf69 ∪ qf70),25⟩)
def qmeq_569 : qr 569 = qm569 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 569 = qv569 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 569 < 6 by decide,↓reduceDIte,he,qv569,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_34,qmeq_568]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf71 : Finset qCell := ([(-7,3),(-7,5),(-6,2),(-6,3),(-6,4),(-6,5),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-5,8),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-4,8),(-4,9)] : List qCell).toFinset
def qf72 : Finset qCell := ([(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-3,10),(-3,11),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9)] : List qCell).toFinset
def qf73 : Finset qCell := ([(-2,10),(-2,11),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(-1,11),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6)] : List qCell).toFinset
def qf74 : Finset qCell := ([(0,7),(0,8),(0,9),(0,10),(0,11),(1,-2),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7)] : List qCell).toFinset
def qf75 : Finset qCell := ([(2,8),(2,9),(2,10),(2,11),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(4,0),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(5,3),(5,4),(5,5)] : List qCell).toFinset
def qf76 : Finset qCell := ([(6,3),(6,5)] : List qCell).toFinset
def qm570 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-2),(-1,-3),(-1,-2),(0,-2),(0,1),(1,-2)},(qf71 ∪ qf72 ∪ qf73 ∪ qf74 ∪ qf75 ∪ qf76),26⟩)
def qmeq_570 : qr 570 = qm570 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 570 = qv570 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 570 < 6 by decide,↓reduceDIte,he,qv570,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_2,qmeq_569]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf77 : Finset qCell := ([(-7,2),(-7,4),(-6,1),(-6,2),(-6,3),(-6,4),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-4,8)] : List qCell).toFinset
def qf78 : Finset qCell := ([(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-3,10),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8)] : List qCell).toFinset
def qf79 : Finset qCell := ([(-2,9),(-2,10),(-1,-4),(-1,-3),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5)] : List qCell).toFinset
def qf80 : Finset qCell := ([(0,6),(0,7),(0,8),(0,9),(0,10),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(2,-3),(2,-2),(2,-1),(2,0),(2,1)] : List qCell).toFinset
def qf81 : Finset qCell := ([(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(4,-2),(4,-1),(4,1)] : List qCell).toFinset
def qf82 : Finset qCell := ([(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(5,2),(5,3),(5,4),(6,2),(6,4)] : List qCell).toFinset
def qm571 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-3),(-1,-4),(-1,-3),(0,-3),(1,-3)},(qf77 ∪ qf78 ∪ qf79 ∪ qf80 ∪ qf81 ∪ qf82),27⟩)
def qmeq_571 : qr 571 = qm571 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 571 = qv571 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 571 < 6 by decide,↓reduceDIte,he,qv571,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_293,qmeq_382,qmeq_556,qmeq_570]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf83 : Finset qCell := ([(-4,1),(-4,2),(-4,3),(-3,-1),(-3,1),(-3,2),(-3,3),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6)] : List qCell).toFinset
def qf84 : Finset qCell := ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)] : List qCell).toFinset
def qf85 : Finset qCell := ([(1,8),(1,9),(1,10),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1)] : List qCell).toFinset
def qf86 : Finset qCell := ([(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(5,-1),(5,1),(5,2),(5,3),(5,4)] : List qCell).toFinset
def qf87 : Finset qCell := ([(5,5),(5,6),(5,7),(5,8),(5,9),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(6,9),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(8,1),(8,3),(8,4),(8,6)] : List qCell).toFinset
def qm572 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,0),(2,0)},(qf83 ∪ qf84 ∪ qf85 ∪ qf86 ∪ qf87),25⟩)
def qmeq_572 : qr 572 = qm572 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 572 = qv572 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 572 < 6 by decide,↓reduceDIte,he,qv572,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_364,qmeq_385,qmeq_465,qmeq_499,qmeq_564]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf88 : Finset qCell := ([(-8,-3),(-8,-1),(-7,-3),(-7,-2),(-7,-1),(-7,0),(-7,1),(-6,-4),(-6,-3),(-6,-2),(-6,-1),(-6,0),(-6,1),(-6,2),(-6,3),(-5,-4),(-5,-3),(-5,-2),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-4,-6),(-4,-5)] : List qCell).toFinset
def qf89 : Finset qCell := ([(-4,-4),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-3,-7),(-3,-6),(-3,-5),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-2,-6),(-2,-5)] : List qCell).toFinset
def qf90 : Finset qCell := ([(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-1,-7),(-1,-6),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-3),(0,-2),(0,-1)] : List qCell).toFinset
def qf91 : Finset qCell := ([(0,0),(0,2),(1,-7),(1,-6),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-6),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-7),(3,-6)] : List qCell).toFinset
def qf92 : Finset qCell := ([(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-6),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(6,-4)] : List qCell).toFinset
def qf93 : Finset qCell := ([(6,-3),(6,-1),(6,0),(6,1),(7,1)] : List qCell).toFinset
def qm573 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-2),(0,-1)},(qf88 ∪ qf89 ∪ qf90 ∪ qf91 ∪ qf92 ∪ qf93),19⟩)
def qmeq_573 : qr 573 = qm573 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 573 = qv573 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 573 < 6 by decide,↓reduceDIte,he,qv573,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_407,qmeq_499,qmeq_527,qmeq_531]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf94 : Finset qCell := ([(-7,2),(-7,3),(-7,4),(-6,1),(-6,2),(-6,3),(-6,4),(-6,5),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-3,0)] : List qCell).toFinset
def qf95 : Finset qCell := ([(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-3,10),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-1,-1),(-1,0),(-1,1),(-1,2)] : List qCell).toFinset
def qf96 : Finset qCell := ([(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(1,-2),(1,-1),(1,0),(1,1),(1,2)] : List qCell).toFinset
def qf97 : Finset qCell := ([(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(3,-4),(3,-3),(3,-2),(3,-1),(3,0)] : List qCell).toFinset
def qf98 : Finset qCell := ([(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1)] : List qCell).toFinset
def qf99 : Finset qCell := ([(5,2),(5,3),(5,4),(5,5),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(7,-2),(7,-1),(7,0),(7,1),(7,2),(8,-2),(8,0),(8,2)] : List qCell).toFinset
def qm574 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(-1,0),(0,-1)},(qf94 ∪ qf95 ∪ qf96 ∪ qf97 ∪ qf98 ∪ qf99),24⟩)
def qmeq_574 : qr 574 = qm574 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 574 = qv574 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 574 < 6 by decide,↓reduceDIte,he,qv574,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_355,qmeq_390,qmeq_462,qmeq_495,qmeq_497,qmeq_518,qmeq_539,qmeq_540,qmeq_544,qmeq_563]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf100 : Finset qCell := ([(-7,1),(-7,2),(-7,3),(-7,4),(-6,1),(-6,2),(-6,3),(-6,4),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-3,-2)] : List qCell).toFinset
def qf101 : Finset qCell := ([(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-3),(0,-2)] : List qCell).toFinset
def qf102 : Finset qCell := ([(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-4),(3,-3)] : List qCell).toFinset
def qf103 : Finset qCell := ([(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(5,-5),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3)] : List qCell).toFinset
def qf104 : Finset qCell := ([(6,-5),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(7,-5),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(8,-3),(8,-2),(8,-1),(8,0),(8,1),(8,3)] : List qCell).toFinset
def qf105 : Finset qCell := ([(9,-3),(9,-2),(9,-1),(9,0),(10,-3),(10,-2),(10,-1),(10,0)] : List qCell).toFinset
def qm575 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1)},(qf100 ∪ qf101 ∪ qf102 ∪ qf103 ∪ qf104 ∪ qf105),24⟩)
def qmeq_575 : qr 575 = qm575 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 575 = qv575 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 575 < 6 by decide,↓reduceDIte,he,qv575,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_180,qmeq_314,qmeq_442,qmeq_504,qmeq_559]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf106 : Finset qCell := ([(-9,-2),(-9,0),(-9,2),(-8,-2),(-8,-1),(-8,0),(-8,1),(-8,2),(-7,-2),(-7,-1),(-7,0),(-7,1),(-7,2),(-7,3),(-7,4),(-6,-4),(-6,-3),(-6,-2),(-6,-1),(-6,0),(-6,1),(-6,2),(-6,3),(-6,4),(-6,5)] : List qCell).toFinset
def qf107 : Finset qCell := ([(-5,-3),(-5,-2),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-4,-4),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-4,8),(-3,-3)] : List qCell).toFinset
def qf108 : Finset qCell := ([(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-1,-1)] : List qCell).toFinset
def qf109 : Finset qCell := ([(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(1,0),(1,1)] : List qCell).toFinset
def qf110 : Finset qCell := ([(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(3,-1),(3,0),(3,1),(3,2),(3,3)] : List qCell).toFinset
def qf111 : Finset qCell := ([(3,4),(3,5),(3,6),(3,7),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(5,1),(5,2),(5,3),(5,4),(5,5),(6,2),(6,3),(6,4)] : List qCell).toFinset
def qm576 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(-1,0),(0,-1)},(qf106 ∪ qf107 ∪ qf108 ∪ qf109 ∪ qf110 ∪ qf111),24⟩)
def qmeq_576 : qr 576 = qm576 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 576 = qv576 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 576 < 6 by decide,↓reduceDIte,he,qv576,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_355,qmeq_390,qmeq_462,qmeq_495,qmeq_497,qmeq_518,qmeq_539,qmeq_540,qmeq_544,qmeq_563]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf112 : Finset qCell := ([(-9,-2),(-9,0),(-8,-2),(-8,-1),(-8,0),(-7,-6),(-7,-5),(-7,-4),(-7,-3),(-7,-2),(-7,-1),(-7,0),(-6,-6),(-6,-5),(-6,-4),(-6,-3),(-6,-2),(-6,-1),(-6,0),(-5,-6),(-5,-5),(-5,-4),(-5,-3),(-5,-2),(-5,-1)] : List qCell).toFinset
def qf113 : Finset qCell := ([(-5,0),(-4,-8),(-4,-7),(-4,-6),(-4,-5),(-4,-4),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-3,-7),(-3,-6),(-3,-5),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-2,-8),(-2,-7),(-2,-6),(-2,-5),(-2,-4)] : List qCell).toFinset
def qf114 : Finset qCell := ([(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(1,2),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1)] : List qCell).toFinset
def qf115 : Finset qCell := ([(2,2),(2,3),(2,4),(2,5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(5,-3),(5,-2)] : List qCell).toFinset
def qf116 : Finset qCell := ([(5,-1),(5,0),(5,1),(5,2),(5,3),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(8,-3),(8,-2),(8,-1),(9,-3),(9,-1)] : List qCell).toFinset
def qm577 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(0,-1)},(qf112 ∪ qf113 ∪ qf114 ∪ qf115 ∪ qf116),21⟩)
def qmeq_577 : qr 577 = qm577 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 577 = qv577 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 577 < 6 by decide,↓reduceDIte,he,qv577,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_64,qmeq_443]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf117 : Finset qCell := ([(-8,-1),(-8,1),(-8,3),(-7,-1),(-7,0),(-7,1),(-7,2),(-7,3),(-6,-1),(-6,0),(-6,1),(-6,2),(-6,3),(-6,4),(-6,5),(-5,-3),(-5,-2),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6)] : List qCell).toFinset
def qf118 : Finset qCell := ([(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-4,8),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-2,-2)] : List qCell).toFinset
def qf119 : Finset qCell := ([(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(0,-3)] : List qCell).toFinset
def qf120 : Finset qCell := ([(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10)] : List qCell).toFinset
def qf121 : Finset qCell := ([(1,11),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(4,0),(4,1)] : List qCell).toFinset
def qf122 : Finset qCell := ([(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(6,2),(6,3),(6,4),(6,5),(6,6),(7,3),(7,4),(7,5)] : List qCell).toFinset
def qm578 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(1,0),(1,1)},(qf117 ∪ qf118 ∪ qf119 ∪ qf120 ∪ qf121 ∪ qf122),25⟩)
def qmeq_578 : qr 578 = qm578 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 578 = qv578 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 578 < 6 by decide,↓reduceDIte,he,qv578,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_2,qmeq_574]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf123 : Finset qCell := ([(-6,3),(-6,4),(-6,5),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-4,8),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-2,1)] : List qCell).toFinset
def qf124 : Finset qCell := ([(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-2,11),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(-1,11),(0,-3),(0,-2),(0,-1),(0,0)] : List qCell).toFinset
def qf125 : Finset qCell := ([(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(2,-1),(2,0)] : List qCell).toFinset
def qf126 : Finset qCell := ([(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(4,-3),(4,-2)] : List qCell).toFinset
def qf127 : Finset qCell := ([(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(6,-3),(6,-2),(6,-1)] : List qCell).toFinset
def qf128 : Finset qCell := ([(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(8,-1),(8,0),(8,1),(8,2),(8,3),(9,-1),(9,1),(9,3)] : List qCell).toFinset
def qm579 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-2),(1,0),(1,1)},(qf123 ∪ qf124 ∪ qf125 ∪ qf126 ∪ qf127 ∪ qf128),25⟩)
def qmeq_579 : qr 579 = qm579 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 579 = qv579 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 579 < 6 by decide,↓reduceDIte,he,qv579,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_2,qmeq_576]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf129 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-7,2),(-7,3),(-7,4),(-6,1),(-6,2),(-6,3),(-6,4),(-6,5),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-3,0)] : List qCell).toFinset)
def qf130 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-3,10),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-1,-4),(-1,-3),(-1,-2),(-1,-1)] : List qCell).toFinset)
def qf131 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10)] : List qCell).toFinset)
def qf132 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9)] : List qCell).toFinset)
def qf133 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(5,-4)] : List qCell).toFinset)
def qf134 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(7,-2),(7,-1),(7,0),(7,1),(7,2),(8,-2),(8,0),(8,2)] : List qCell).toFinset)
def qm580 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-4),(-1,-3),(0,-3),(0,-1)},(qf129 ∪ qf130 ∪ qf131 ∪ qf132 ∪ qf133 ∪ qf134),26⟩)
def qmeq_580 : qr 580 = qm580 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 580 = qv580 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 580 < 6 by decide,↓reduceDIte,he,qv580,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_2,qmeq_579]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf135 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-6,2),(-6,3),(-6,4),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-2,0)] : List qCell).toFinset)
def qf136 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(0,-3),(0,-2),(0,-1),(0,0)] : List qCell).toFinset)
def qf137 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10)] : List qCell).toFinset)
def qf138 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9)] : List qCell).toFinset)
def qf139 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(6,-4)] : List qCell).toFinset)
def qf140 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(8,-2),(8,-1),(8,0),(8,1),(8,2),(9,-2),(9,0),(9,2)] : List qCell).toFinset)
def qm581 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-1),(1,-4),(1,-3)},(qf135 ∪ qf136 ∪ qf137 ∪ qf138 ∪ qf139 ∪ qf140),26⟩)
def qmeq_581 : qr 581 = qm581 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 581 = qv581 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 581 < 6 by decide,↓reduceDIte,he,qv581,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_2,qmeq_578]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf141 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-6,1),(-6,2),(-6,4),(-5,1),(-5,2),(-5,3),(-5,4),(-4,-3),(-4,-1),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5)] : List qCell).toFinset)
def qf142 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-3,6),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6)] : List qCell).toFinset)
def qf143 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-1,7),(-1,8),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] : List qCell).toFinset)
def qf144 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(1,6),(1,7),(2,-4),(2,-3),(2,-2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(3,-9),(3,-8),(3,-7),(3,-6),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2)] : List qCell).toFinset)
def qf145 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(3,3),(3,4),(3,5),(3,6),(3,7),(4,-8),(4,-7),(4,-6),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(5,-9),(5,-8),(5,-7),(5,-6)] : List qCell).toFinset)
def qf146 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(5,-5),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(6,-7),(6,-6),(6,-5),(6,-4),(6,-3),(6,-2),(6,-1),(6,2),(6,4),(7,-7),(7,-6),(7,-5),(7,-4),(7,-3),(7,-2)] : List qCell).toFinset)
def qf147 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(7,-1),(8,-7),(8,-6),(8,-5),(8,-4),(8,-3),(8,-2),(8,-1),(9,-3),(9,-2),(9,-1),(10,-3),(10,-1)] : List qCell).toFinset)
def qm582 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(1,-4),(1,-3),(1,-2),(2,-4)},(qf141 ∪ qf142 ∪ qf143 ∪ qf144 ∪ qf145 ∪ qf146 ∪ qf147),24⟩)
def qmeq_582 : qr 582 = qm582 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 582 = qv582 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 582 < 6 by decide,↓reduceDIte,he,qv582,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_40,qmeq_446,qmeq_480,qmeq_523,qmeq_567]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf148 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-8,5),(-8,6),(-8,8),(-7,5),(-7,6),(-7,7),(-7,8),(-6,1),(-6,3),(-6,5),(-6,6),(-6,7),(-6,8),(-6,9),(-6,10),(-6,11),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-5,8),(-5,9)] : List qCell).toFinset)
def qf149 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-5,10),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-4,8),(-4,9),(-4,10),(-4,11),(-4,12),(-4,13),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-3,10)] : List qCell).toFinset)
def qf150 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-3,11),(-3,12),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-2,11),(-2,12),(-2,13),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9)] : List qCell).toFinset)
def qf151 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-1,10),(-1,11),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2)] : List qCell).toFinset)
def qf152 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11)] : List qCell).toFinset)
def qf153 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,6),(4,8),(5,-3),(5,-2)] : List qCell).toFinset)
def qf154 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(5,-1),(5,0),(5,1),(5,2),(5,3),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(7,1),(7,2),(7,3),(8,1),(8,3)] : List qCell).toFinset)
def qm583 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0),(-1,1),(-1,2)},(qf148 ∪ qf149 ∪ qf150 ∪ qf151 ∪ qf152 ∪ qf153 ∪ qf154),25⟩)
def qmeq_583 : qr 583 = qm583 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 583 = qv583 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 583 < 6 by decide,↓reduceDIte,he,qv583,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_25,qmeq_221,qmeq_525,qmeq_582]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def ql584b0 : List qCell := [(-9,-1),(-9,1),(-8,-1),(-8,0),(-8,1),(-7,-5),(-7,-4),(-7,-3),(-7,-2),(-7,-1),(-7,0),(-7,1),(-7,3),(-6,-5),(-6,-4),(-6,-3),(-6,-2),(-6,-1),(-6,0),(-6,1),(-6,2),(-6,3),(-5,-5),(-5,-4),(-5,-3)]
def ql584b1 : List qCell := [(-5,-2),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-4,-7),(-4,-6),(-4,-5),(-4,-4),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-3,-6),(-3,-5),(-3,-4),(-3,-3),(-3,-2),(-3,-1)]
def ql584b2 : List qCell := [(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,-7),(-2,-6),(-2,-5),(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1)]
def ql584b3 : List qCell := [(-1,2),(-1,3),(-1,4),(-1,5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2)]
def ql584b4 : List qCell := [(2,3),(2,4),(2,5),(2,6),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(5,-2),(5,-1)]
def ql584b5 : List qCell := [(5,0),(5,1),(5,2),(5,3),(5,4),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(8,-2),(8,-1),(8,0),(9,-2),(9,0)]
def ql584 : List qCell := ql584b0 ++ ql584b1 ++ ql584b2 ++ ql584b3 ++ ql584b4 ++ ql584b5
def qn584 : (ql584).Nodup := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qm584 : qR := ⟨{(0,-2),(0,-1)},⟨(ql584 : Multiset qCell), Multiset.coe_nodup.mpr qn584⟩,22⟩
def qmeq_584 : qr 584 = qm584 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 584 = qv584 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 584 < 6 by decide,↓reduceDIte,he,qv584,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_173,qmeq_236,qmeq_263,qmeq_295,qmeq_548,qmeq_577]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf161 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-9,-1),(-9,1),(-8,-1),(-8,0),(-8,1),(-7,-5),(-7,-4),(-7,-3),(-7,-2),(-7,-1),(-7,0),(-7,1),(-6,-5),(-6,-4),(-6,-3),(-6,-2),(-6,-1),(-6,0),(-6,1),(-5,-5),(-5,-4),(-5,-3),(-5,-2),(-5,-1),(-5,0)] : List qCell).toFinset)
def qf162 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-5,1),(-4,-7),(-4,-6),(-4,-5),(-4,-4),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2),(-3,-7),(-3,-6),(-3,-5),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-2,-7),(-2,-6),(-2,-5),(-2,-4)] : List qCell).toFinset)
def qf163 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-1,-7),(-1,-6),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1)] : List qCell).toFinset)
def qf164 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(1,0),(1,1),(1,2),(1,3),(2,-7),(2,-6),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,-6),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0)] : List qCell).toFinset)
def qf165 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(3,1),(3,2),(3,3),(3,4),(3,5),(4,-7),(4,-6),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(5,-5),(5,-4),(5,-3),(5,-2),(5,-1),(5,0)] : List qCell).toFinset)
def qf166 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(5,1),(5,2),(5,3),(5,4),(6,-5),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(7,-5),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(8,-2)] : List qCell).toFinset)
def qf167 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(8,-1),(8,0),(8,1),(9,-2),(9,-1),(9,0),(9,1)] : List qCell).toFinset)
def qm585 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-2),(0,-1)},(qf161 ∪ qf162 ∪ qf163 ∪ qf164 ∪ qf165 ∪ qf166 ∪ qf167),22⟩)
def qmeq_585 : qr 585 = qm585 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 585 = qv585 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 585 < 6 by decide,↓reduceDIte,he,qv585,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_183,qmeq_236,qmeq_300,qmeq_479,qmeq_527,qmeq_577]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def ql586b0 : List qCell := [(-7,3),(-7,4),(-7,6),(-6,1),(-6,3),(-6,4),(-6,5),(-6,6),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-5,8),(-5,9),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4)]
def ql586b1 : List qCell := [(-4,5),(-4,6),(-4,7),(-4,8),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-3,10),(-3,11),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5)]
def ql586b2 : List qCell := [(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(-1,11),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4)]
def ql586b3 : List qCell := [(0,5),(0,6),(0,7),(0,8),(0,9),(1,-6),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(2,-7),(2,-6),(2,-5),(2,-4)]
def ql586b4 : List qCell := [(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(3,-6),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)]
def ql586b5 : List qCell := [(3,6),(3,7),(3,8),(3,9),(4,-7),(4,-6),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(5,-5),(5,-4),(5,-3),(5,-2),(5,-1),(5,0)]
def ql586b6 : List qCell := [(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(6,-5),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(7,-5),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1)]
def ql586b7 : List qCell := [(7,2),(7,3),(7,4),(7,5),(8,-2),(8,-1),(8,0),(8,1),(8,2),(8,3),(8,4),(9,-2),(9,-1),(9,0),(9,1),(9,2),(9,3),(9,4),(10,-2),(10,-1),(10,0),(11,-2),(11,0)]
def ql586 : List qCell := ql586b0 ++ ql586b1 ++ ql586b2 ++ ql586b3 ++ ql586b4 ++ ql586b5 ++ ql586b6 ++ ql586b7
def qn586 : (ql586).Nodup := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qm586 : qR := ⟨{(0,-2),(0,-1)},⟨(ql586 : Multiset qCell), Multiset.coe_nodup.mpr qn586⟩,26⟩
def qmeq_586 : qr 586 = qm586 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 586 = qv586 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 586 < 6 by decide,↓reduceDIte,he,qv586,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_379,qmeq_385,qmeq_465,qmeq_467,qmeq_469,qmeq_524,qmeq_527,qmeq_552,qmeq_553,qmeq_555,qmeq_558,qmeq_564,qmeq_583]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def ql587b0 : List qCell := [(-7,-2),(-7,-1),(-7,0),(-7,1),(-6,-2),(-6,-1),(-6,0),(-6,1),(-5,-4),(-5,-3),(-5,-2),(-5,-1),(-5,0),(-5,1),(-4,-6),(-4,-5),(-4,-4),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-3,-6)]
def ql587b1 : List qCell := [(-3,-5),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-2,-6),(-2,-5),(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-1,-5),(-1,-4),(-1,-3),(-1,-1),(-1,0)]
def ql587b2 : List qCell := [(-1,1),(-1,2),(-1,3),(-1,4),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-7),(2,-6),(2,-5),(2,-4)]
def ql587b3 : List qCell := [(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,-6),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,-7),(4,-6),(4,-5)]
def ql587b4 : List qCell := [(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(5,-5),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(6,-5),(6,-4),(6,-3),(6,-2)]
def ql587b5 : List qCell := [(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(7,-5),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(8,-2),(8,-1),(8,0),(8,1),(9,-2),(9,-1),(9,0),(9,1)]
def ql587 : List qCell := ql587b0 ++ ql587b1 ++ ql587b2 ++ ql587b3 ++ ql587b4 ++ ql587b5
def qn587 : (ql587).Nodup := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qm587 : qR := ⟨{(0,-2),(0,-1)},⟨(ql587 : Multiset qCell), Multiset.coe_nodup.mpr qn587⟩,22⟩
def qmeq_587 : qr 587 = qm587 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 587 = qv587 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 587 < 6 by decide,↓reduceDIte,he,qv587,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_252,qmeq_300,qmeq_319,qmeq_467,qmeq_477,qmeq_479]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf182 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-7,4),(-7,5),(-7,7),(-6,2),(-6,4),(-6,5),(-6,6),(-6,7),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-5,8),(-5,9),(-5,10),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5)] : List qCell).toFinset)
def qf183 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-4,6),(-4,7),(-4,8),(-4,9),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-3,10),(-3,11),(-3,12),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6)] : List qCell).toFinset)
def qf184 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-2,7),(-2,8),(-2,9),(-2,10),(-2,11),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(-1,11),(-1,12),(0,-1),(0,0),(0,1)] : List qCell).toFinset)
def qf185 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10)] : List qCell).toFinset)
def qf186 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(2,-6),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2)] : List qCell).toFinset)
def qf187 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(4,-6),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(5,-4),(5,-3)] : List qCell).toFinset)
def qf188 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(7,-4),(7,-3),(7,-2)] : List qCell).toFinset)
def qf189 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(8,-1),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(9,-1),(9,0),(9,1),(9,2),(9,3),(9,4),(9,5),(10,-1),(10,0),(10,1)] : List qCell).toFinset)
def qf190 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(11,-1),(11,1)] : List qCell).toFinset)
def qm588 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-4),(-1,-3),(-1,-2),(0,-1)},(qf182 ∪ qf183 ∪ qf184 ∪ qf185 ∪ qf186 ∪ qf187 ∪ qf188 ∪ qf189 ∪ qf190),27⟩)
def qmeq_588 : qr 588 = qm588 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 588 = qv588 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 588 < 6 by decide,↓reduceDIte,he,qv588,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_3,qmeq_586]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf191 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-7,5),(-7,6),(-7,8),(-6,3),(-6,5),(-6,6),(-6,7),(-6,8),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-5,8),(-5,9),(-5,10),(-5,11),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6)] : List qCell).toFinset)
def qf192 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-4,7),(-4,8),(-4,9),(-4,10),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-3,10),(-3,11),(-3,12),(-3,13),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7)] : List qCell).toFinset)
def qf193 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-2,8),(-2,9),(-2,10),(-2,11),(-2,12),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(-1,11),(-1,12),(-1,13),(0,-1),(0,0)] : List qCell).toFinset)
def qf194 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9)] : List qCell).toFinset)
def qf195 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(1,10),(1,11),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1)] : List qCell).toFinset)
def qf196 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9)] : List qCell).toFinset)
def qf197 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(7,-3)] : List qCell).toFinset)
def qf198 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(9,0),(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(10,0)] : List qCell).toFinset)
def qf199 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(10,1),(10,2),(11,0),(11,2)] : List qCell).toFinset)
def qm589 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-4),(-1,-3),(-1,-2),(-1,-1)},(qf191 ∪ qf192 ∪ qf193 ∪ qf194 ∪ qf195 ∪ qf196 ∪ qf197 ∪ qf198 ∪ qf199),28⟩)
def qmeq_589 : qr 589 = qm589 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 589 = qv589 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 589 < 6 by decide,↓reduceDIte,he,qv589,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_4,qmeq_588]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def ql590b0 : List qCell := [(-9,1),(-9,3),(-8,1),(-8,2),(-8,3),(-7,-3),(-7,-2),(-7,-1),(-7,0),(-7,1),(-7,2),(-7,3),(-6,-3),(-6,-2),(-6,-1),(-6,0),(-6,1),(-6,2),(-6,3),(-5,-3),(-5,-2),(-5,-1),(-5,0),(-5,1),(-5,2)]
def ql590b1 : List qCell := [(-5,3),(-4,-5),(-4,-4),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,-5),(-2,-4),(-2,-3),(-2,-2),(-2,-1)]
def ql590b2 : List qCell := [(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,5),(-1,6),(-1,7),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,-3)]
def ql590b3 : List qCell := [(1,-2),(1,-1),(1,0),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(3,-3),(3,-2),(3,-1),(3,0)]
def ql590b4 : List qCell := [(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4)]
def ql590b5 : List qCell := [(5,5),(5,6),(5,7),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(8,-1),(8,0),(8,1)]
def ql590b6 : List qCell := [(8,2),(8,3),(8,4),(8,5),(9,0),(9,2),(9,3),(9,4),(9,5),(10,2),(10,3),(10,4),(10,5)]
def ql590 : List qCell := ql590b0 ++ ql590b1 ++ ql590b2 ++ ql590b3 ++ ql590b4 ++ ql590b5 ++ ql590b6
def qn590 : (ql590).Nodup := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qm590 : qR := ⟨{(0,1),(0,2)},⟨(ql590 : Multiset qCell), Multiset.coe_nodup.mpr qn590⟩,23⟩
def qmeq_590 : qr 590 = qm590 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 590 = qv590 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 590 < 6 by decide,↓reduceDIte,he,qv590,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_173,qmeq_217,qmeq_295,qmeq_490,qmeq_577]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def ql591b0 : List qCell := [(-10,-1),(-10,0),(-10,1),(-10,2),(-9,-1),(-9,0),(-9,1),(-9,2),(-8,-4),(-8,-2),(-8,-1),(-8,0),(-8,1),(-8,2),(-7,-5),(-7,-4),(-7,-3),(-7,-2),(-7,-1),(-7,0),(-7,1),(-7,2),(-7,3),(-7,4),(-6,-4)]
def ql591b1 : List qCell := [(-6,-3),(-6,-2),(-6,-1),(-6,0),(-6,1),(-6,2),(-6,3),(-6,4),(-5,-4),(-5,-3),(-5,-2),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-4,-5),(-4,-4),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2)]
def ql591b2 : List qCell := [(-4,3),(-4,4),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-1,-5),(-1,-4),(-1,-3)]
def ql591b3 : List qCell := [(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-5),(1,-4),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3)]
def ql591b4 : List qCell := [(1,4),(1,5),(1,6),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,-5),(4,-4)]
def ql591b5 : List qCell := [(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3)]
def ql591b6 : List qCell := [(6,4),(7,-5),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(8,-4),(8,-2),(8,-1),(8,0),(8,1),(8,2),(9,-1),(9,0),(9,1),(9,2),(10,-1),(10,0),(10,1),(10,2)]
def ql591 : List qCell := ql591b0 ++ ql591b1 ++ ql591b2 ++ ql591b3 ++ ql591b4 ++ ql591b5 ++ ql591b6
def qn591 : (ql591).Nodup := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qm591 : qR := ⟨{(0,-2),(0,-1)},⟨(ql591 : Multiset qCell), Multiset.coe_nodup.mpr qn591⟩,23⟩
def qmeq_591 : qr 591 = qm591 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 591 = qv591 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 591 < 6 by decide,↓reduceDIte,he,qv591,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_197,qmeq_524,qmeq_529,qmeq_538]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf214 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-7,5),(-7,6),(-7,8),(-6,3),(-6,5),(-6,6),(-6,7),(-6,8),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-5,8),(-5,9),(-5,10),(-5,11),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6)] : List qCell).toFinset)
def qf215 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-4,7),(-4,8),(-4,9),(-4,10),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-3,10),(-3,11),(-3,12),(-3,13),(-2,-6),(-2,-5),(-2,-4),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4)] : List qCell).toFinset)
def qf216 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-2,11),(-2,12),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(-1,11)] : List qCell).toFinset)
def qf217 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-1,12),(-1,13),(0,-6),(0,-5),(0,-4),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2)] : List qCell).toFinset)
def qf218 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10)] : List qCell).toFinset)
def qf219 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(2,11),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2)] : List qCell).toFinset)
def qf220 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2)] : List qCell).toFinset)
def qf221 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(9,0)] : List qCell).toFinset)
def qf222 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(10,0),(10,1),(10,2),(11,0),(11,2)] : List qCell).toFinset)
def qm592 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-2),(-1,-1)},(qf214 ∪ qf215 ∪ qf216 ∪ qf217 ∪ qf218 ∪ qf219 ∪ qf220 ∪ qf221 ∪ qf222),28⟩)
def qmeq_592 : qr 592 = qm592 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 592 = qv592 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 592 < 6 by decide,↓reduceDIte,he,qv592,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_108,qmeq_588]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf223 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-7,4),(-7,5),(-7,7),(-6,2),(-6,4),(-6,5),(-6,6),(-6,7),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-5,8),(-5,9),(-5,10),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5)] : List qCell).toFinset)
def qf224 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-4,6),(-4,7),(-4,8),(-4,9),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-3,10),(-3,11),(-3,12),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6)] : List qCell).toFinset)
def qf225 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-2,7),(-2,8),(-2,9),(-2,10),(-2,11),(-1,-4),(-1,-3),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(-1,11),(-1,12),(0,-3),(0,-2),(0,-1),(0,0),(0,1)] : List qCell).toFinset)
def qf226 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10)] : List qCell).toFinset)
def qf227 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(2,-6),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2)] : List qCell).toFinset)
def qf228 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(4,-6),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(5,-4),(5,-3)] : List qCell).toFinset)
def qf229 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(7,-4),(7,-3),(7,-2)] : List qCell).toFinset)
def qf230 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(8,-1),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(9,-1),(9,0),(9,1),(9,2),(9,3),(9,4),(9,5),(10,-1),(10,0),(10,1)] : List qCell).toFinset)
def qf231 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(11,-1),(11,1)] : List qCell).toFinset)
def qm593 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-4),(-1,-3),(0,-3),(0,-1)},(qf223 ∪ qf224 ∪ qf225 ∪ qf226 ∪ qf227 ∪ qf228 ∪ qf229 ∪ qf230 ∪ qf231),27⟩)
def qmeq_593 : qr 593 = qm593 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 593 = qv593 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 593 < 6 by decide,↓reduceDIte,he,qv593,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_2,qmeq_586]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf232 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-7,5),(-7,6),(-7,8),(-6,3),(-6,5),(-6,6),(-6,7),(-6,8),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-5,8),(-5,9),(-5,10),(-5,11),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6)] : List qCell).toFinset)
def qf233 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-4,7),(-4,8),(-4,9),(-4,10),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-3,10),(-3,11),(-3,12),(-3,13),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7)] : List qCell).toFinset)
def qf234 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-2,8),(-2,9),(-2,10),(-2,11),(-2,12),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(-1,11),(-1,12),(-1,13),(0,-2),(0,-1)] : List qCell).toFinset)
def qf235 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(1,-6),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)] : List qCell).toFinset)
def qf236 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(1,7),(1,8),(1,9),(1,10),(1,11),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(3,-6),(3,-5),(3,-4)] : List qCell).toFinset)
def qf237 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4)] : List qCell).toFinset)
def qf238 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(4,5),(4,6),(4,7),(4,8),(4,9),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2)] : List qCell).toFinset)
def qf239 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(8,-3),(8,-1),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5)] : List qCell).toFinset)
def qf240 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(8,6),(9,0),(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(10,0),(10,1),(10,2),(11,0),(11,2)] : List qCell).toFinset)
def qm594 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-2),(-1,-1)},(qf232 ∪ qf233 ∪ qf234 ∪ qf235 ∪ qf236 ∪ qf237 ∪ qf238 ∪ qf239 ∪ qf240),28⟩)
def qmeq_594 : qr 594 = qm594 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 594 = qv594 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 594 < 6 by decide,↓reduceDIte,he,qv594,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_30,qmeq_476,qmeq_588]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf241 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-6,-1),(-6,0),(-6,1),(-6,2),(-6,3),(-6,4),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-3,-3),(-3,-2),(-3,-1),(-3,0)] : List qCell).toFinset)
def qf242 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-2,11),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1)] : List qCell).toFinset)
def qf243 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(-1,11),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7)] : List qCell).toFinset)
def qf244 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(0,8),(0,9),(0,10),(0,11),(1,-6),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(2,-6),(2,-5),(2,-4)] : List qCell).toFinset)
def qf245 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6)] : List qCell).toFinset)
def qf246 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(3,7),(3,8),(3,9),(4,-7),(4,-6),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(5,-7),(5,-6),(5,-5),(5,-4),(5,-3)] : List qCell).toFinset)
def qf247 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(6,-6),(6,-5),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6)] : List qCell).toFinset)
def qf248 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(6,7),(7,-7),(7,-6),(7,-5),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(8,-5),(8,-4),(8,-3),(8,-2),(8,-1),(8,0),(8,1),(8,2),(8,3),(8,4)] : List qCell).toFinset)
def qf249 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(9,-5),(9,-4),(9,-3),(9,-2),(9,-1),(9,0),(9,1),(9,2),(9,3),(10,-5),(10,-3),(10,-2),(10,-1),(10,0),(10,1),(10,2),(10,3),(11,-3),(11,-2),(11,-1),(12,-3),(12,-1)] : List qCell).toFinset)
def qm595 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0)},(qf241 ∪ qf242 ∪ qf243 ∪ qf244 ∪ qf245 ∪ qf246 ∪ qf247 ∪ qf248 ∪ qf249),27⟩)
def qmeq_595 : qr 595 = qm595 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 595 = qv595 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 595 < 6 by decide,↓reduceDIte,he,qv595,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_406,qmeq_411,qmeq_460,qmeq_551,qmeq_572,qmeq_586]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf250 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-6,7),(-6,8),(-6,10),(-5,5),(-5,7),(-5,8),(-5,9),(-5,10),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-4,8),(-4,9),(-4,10),(-4,11),(-4,12),(-4,13),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8)] : List qCell).toFinset)
def qf251 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-3,9),(-3,10),(-3,11),(-3,12),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-2,11),(-2,12),(-2,13),(-2,14),(-2,15),(-1,-4),(-1,-3),(-1,-2),(-1,0),(-1,2),(-1,3),(-1,4),(-1,5)] : List qCell).toFinset)
def qf252 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(-1,11),(-1,12),(-1,13),(-1,14),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11)] : List qCell).toFinset)
def qf253 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(0,12),(0,13),(0,14),(0,15),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(1,12),(1,13),(2,-5),(2,-4)] : List qCell).toFinset)
def qf254 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(2,12),(2,13),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2)] : List qCell).toFinset)
def qf255 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(3,12),(3,13),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8)] : List qCell).toFinset)
def qf256 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(4,9),(4,10),(4,11),(4,12),(4,13),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(5,11),(6,-3),(6,-2),(6,-1),(6,0),(6,1)] : List qCell).toFinset)
def qf257 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(6,9),(6,10),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(7,8),(7,9),(7,10),(8,-1),(8,0)] : List qCell).toFinset)
def qf258 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(8,7),(8,8),(8,9),(9,2),(9,3),(9,4),(9,5),(9,6),(9,7),(9,8),(10,2),(10,3),(10,4),(10,5),(10,6),(10,7),(10,8),(11,2),(11,3)] : List qCell).toFinset)
def qf259 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(11,4),(12,2),(12,4)] : List qCell).toFinset)
def qm596 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-1),(0,1)},(qf250 ∪ qf251 ∪ qf252 ∪ qf253 ∪ qf254 ∪ qf255 ∪ qf256 ∪ qf257 ∪ qf258 ∪ qf259),29⟩)
def qmeq_596 : qr 596 = qm596 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 596 = qv596 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 596 < 6 by decide,↓reduceDIte,he,qv596,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_330,qmeq_385,qmeq_529,qmeq_592]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf260 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-4,-1),(-4,1),(-4,2),(-4,4),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-1,-2),(-1,-1),(-1,0),(-1,2),(-1,3)] : List qCell).toFinset)
def qf261 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9)] : List qCell).toFinset)
def qf262 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(2,12),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6)] : List qCell).toFinset)
def qf263 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(3,7),(3,8),(3,9),(3,10),(3,11),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(4,10),(4,11),(4,12),(5,-5),(5,-4),(5,-3)] : List qCell).toFinset)
def qf264 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7)] : List qCell).toFinset)
def qf265 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(6,8),(6,9),(6,10),(7,-6),(7,-5),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(7,8),(7,9),(7,10),(8,-6),(8,-5),(8,-4),(8,-3),(8,-2)] : List qCell).toFinset)
def qf266 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(8,-1),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(8,7),(8,8),(8,9),(8,10),(9,-5),(9,-4),(9,-3),(9,-2),(9,-1),(9,0),(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(9,7)] : List qCell).toFinset)
def qf267 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(9,8),(10,-6),(10,-5),(10,-4),(10,-3),(10,-2),(10,-1),(10,0),(10,1),(10,2),(10,3),(10,4),(10,5),(10,6),(10,7),(11,-4),(11,-3),(11,-2),(11,-1),(11,0),(11,1),(11,2),(11,3),(11,4),(11,5)] : List qCell).toFinset)
def qf268 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(12,-4),(12,-3),(12,-2),(12,-1),(12,0),(12,1),(12,2),(12,3),(12,4),(13,-4),(13,-2),(13,-1),(13,0),(13,1),(13,2),(13,3),(13,4),(14,-2),(14,-1),(14,0),(15,-2),(15,0)] : List qCell).toFinset)
def qm597 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-1),(-1,0),(1,0)},(qf260 ∪ qf261 ∪ qf262 ∪ qf263 ∪ qf264 ∪ qf265 ∪ qf266 ∪ qf267 ∪ qf268),29⟩)
def qmeq_597 : qr 597 = qm597 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 597 = qv597 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 597 < 6 by decide,↓reduceDIte,he,qv597,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_24,qmeq_199,qmeq_221,qmeq_594]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf269 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-6,7),(-6,8),(-6,10),(-5,5),(-5,7),(-5,8),(-5,9),(-5,10),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-4,8),(-4,9),(-4,10),(-4,11),(-4,12),(-4,13),(-3,-2),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6)] : List qCell).toFinset)
def qf270 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-3,7),(-3,8),(-3,9),(-3,10),(-3,11),(-3,12),(-2,-2),(-2,-1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-2,11),(-2,12),(-2,13),(-2,14),(-2,15),(-1,-4),(-1,-3),(-1,-2)] : List qCell).toFinset)
def qf271 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-1,-1),(-1,0),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(-1,11),(-1,12),(-1,13),(-1,14),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6)] : List qCell).toFinset)
def qf272 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(0,15),(1,-4),(1,-3),(1,-2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(1,12)] : List qCell).toFinset)
def qf273 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(1,13),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(2,12),(2,13),(3,-4),(3,-3),(3,-2),(3,-1),(3,0)] : List qCell).toFinset)
def qf274 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(3,12),(3,13),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6)] : List qCell).toFinset)
def qf275 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(4,7),(4,8),(4,9),(4,10),(4,11),(4,12),(4,13),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(5,11),(6,-3),(6,-2),(6,-1)] : List qCell).toFinset)
def qf276 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(6,9),(6,10),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(7,8),(7,9),(7,10)] : List qCell).toFinset)
def qf277 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(8,-1),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(8,7),(8,8),(8,9),(9,-1),(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(9,7),(9,8),(10,2),(10,3),(10,4),(10,5),(10,6)] : List qCell).toFinset)
def qf278 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(10,7),(10,8),(11,2),(11,3),(11,4),(12,2),(12,4)] : List qCell).toFinset)
def qm598 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-2),(-2,-2),(-2,-1),(0,-1),(0,1)},(qf269 ∪ qf270 ∪ qf271 ∪ qf272 ∪ qf273 ∪ qf274 ∪ qf275 ∪ qf276 ∪ qf277 ∪ qf278),29⟩)
def qmeq_598 : qr 598 = qm598 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 598 = qv598 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 598 < 6 by decide,↓reduceDIte,he,qv598,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_254,qmeq_456,qmeq_465,qmeq_554,qmeq_594]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf279 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-11,-1),(-11,1),(-10,-1),(-10,0),(-10,1),(-9,-1),(-9,0),(-9,1),(-9,2),(-9,3),(-9,4),(-9,5),(-8,-2),(-8,-1),(-8,0),(-8,1),(-8,2),(-8,3),(-8,4),(-8,5),(-7,-4),(-7,-3),(-7,-2),(-7,-1),(-7,0)] : List qCell).toFinset)
def qf280 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-7,1),(-7,2),(-7,3),(-7,4),(-7,5),(-7,6),(-6,-4),(-6,-3),(-6,-2),(-6,-1),(-6,0),(-6,1),(-6,2),(-6,3),(-6,4),(-6,5),(-6,6),(-6,7),(-5,-4),(-5,-3),(-5,-2),(-5,-1),(-5,0),(-5,1),(-5,2)] : List qCell).toFinset)
def qf281 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-4,-6),(-4,-5),(-4,-4),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-4,8),(-3,-5),(-3,-4),(-3,-3),(-3,-2),(-3,-1)] : List qCell).toFinset)
def qf282 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-3,10),(-2,-6),(-2,-5),(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7)] : List qCell).toFinset)
def qf283 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-2,8),(-2,9),(-2,10),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(0,-3),(0,-1),(0,0),(0,1),(0,2),(0,3)] : List qCell).toFinset)
def qf284 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(1,12),(2,-4)] : List qCell).toFinset)
def qf285 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7)] : List qCell).toFinset)
def qf286 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(3,8),(3,9),(3,10),(3,11),(3,12),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2)] : List qCell).toFinset)
def qf287 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(7,-2),(7,-1),(7,0),(7,1),(7,2)] : List qCell).toFinset)
def qf288 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(7,3),(7,4),(7,5),(7,7),(8,-2),(8,-1),(8,0),(8,1),(8,2),(9,-2),(9,0),(9,2)] : List qCell).toFinset)
def qm599 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-3),(0,-1),(1,-4),(1,-3)},(qf279 ∪ qf280 ∪ qf281 ∪ qf282 ∪ qf283 ∪ qf284 ∪ qf285 ∪ qf286 ∪ qf287 ∪ qf288),27⟩)
def qmeq_599 : qr 599 = qm599 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 599 = qv599 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 599 < 6 by decide,↓reduceDIte,he,qv599,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_485,qmeq_492,qmeq_512,qmeq_578,qmeq_579,qmeq_586]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf289 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-5,-1),(-5,1),(-5,2),(-5,4),(-4,-5),(-4,-3),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-3,-5),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7)] : List qCell).toFinset)
def qf290 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-3,8),(-3,9),(-2,-8),(-2,-7),(-2,-6),(-2,-5),(-2,-4),(-2,-3),(-2,-2),(-2,0),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-1,-8),(-1,-7),(-1,-6),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,0)] : List qCell).toFinset)
def qf291 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(0,-8),(0,-7),(0,-6),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7)] : List qCell).toFinset)
def qf292 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(1,-12),(1,-11),(1,-10),(1,-9),(1,-8),(1,-7),(1,-6),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,-11),(2,-10),(2,-9),(2,-8),(2,-7)] : List qCell).toFinset)
def qf293 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(2,-6),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(3,-12),(3,-11),(3,-10),(3,-9),(3,-8),(3,-7),(3,-6),(3,-5),(3,-4),(3,-3),(3,-2)] : List qCell).toFinset)
def qf294 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(4,-10),(4,-9),(4,-8),(4,-7),(4,-6),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5)] : List qCell).toFinset)
def qf295 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(5,-10),(5,-9),(5,-8),(5,-7),(5,-6),(5,-5),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(6,-10),(6,-9),(6,-8),(6,-7),(6,-6),(6,-5),(6,-4),(6,-3),(6,-2),(6,-1)] : List qCell).toFinset)
def qf296 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(7,-10),(7,-9),(7,-8),(7,-7),(7,-6),(7,-5),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(8,-8)] : List qCell).toFinset)
def qf297 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(8,-7),(8,-6),(8,-5),(8,-4),(8,-3),(8,-2),(8,-1),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(9,-7),(9,-6),(9,-5),(9,-4),(9,-3),(9,-2),(9,-1),(9,0),(9,1),(9,2),(9,3),(9,4)] : List qCell).toFinset)
def qf298 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(9,5),(9,6),(10,-5),(10,-4),(10,-3),(10,-2),(10,-1),(10,0),(10,1),(10,2),(10,3),(10,4),(11,-4),(11,-3),(11,-2),(11,-1),(11,0),(11,1),(11,2),(11,3),(11,4),(12,-4),(12,-3),(12,-2),(12,-1)] : List qCell).toFinset)
def qf299 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(12,0),(12,1),(12,2),(12,4),(13,0),(13,1),(13,2),(14,0),(14,2)] : List qCell).toFinset)
def qm600 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-1,0),(-1,1)},(qf289 ∪ qf290 ∪ qf291 ∪ qf292 ∪ qf293 ∪ qf294 ∪ qf295 ∪ qf296 ∪ qf297 ∪ qf298 ∪ qf299),29⟩)
def qmeq_600 : qr 600 = qm600 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 600 = qv600 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 600 < 6 by decide,↓reduceDIte,he,qv600,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_146,qmeq_278,qmeq_403,qmeq_448,qmeq_592]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def ql601b0 : List qCell := [(-9,-3),(-9,-1),(-8,-3),(-8,-2),(-8,-1),(-7,-5),(-7,-4),(-7,-3),(-7,-2),(-7,-1),(-7,0),(-7,1),(-7,2),(-7,3),(-6,-5),(-6,-4),(-6,-3),(-6,-2),(-6,-1),(-6,0),(-6,1),(-6,2),(-6,3),(-6,6),(-6,7)]
def ql601b1 : List qCell := [(-6,9),(-5,-5),(-5,-4),(-5,-3),(-5,-2),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-5,6),(-5,7),(-5,8),(-5,9),(-4,-7),(-4,-6),(-4,-5),(-4,-4),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2)]
def ql601b2 : List qCell := [(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-4,8),(-4,9),(-4,10),(-4,11),(-4,12),(-3,-7),(-3,-6),(-3,-5),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7)]
def ql601b3 : List qCell := [(-3,8),(-3,9),(-3,10),(-3,11),(-2,-7),(-2,-6),(-2,-5),(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-2,11),(-2,12),(-2,13)]
def ql601b4 : List qCell := [(-2,14),(-1,-5),(-1,-4),(-1,-3),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(-1,11),(-1,12),(-1,13),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0)]
def ql601b5 : List qCell := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(1,-6),(1,-5),(1,-4),(1,-3),(1,-2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)]
def ql601b6 : List qCell := [(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(1,12),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(2,12)]
def ql601b7 : List qCell := [(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(3,12),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1)]
def ql601b8 : List qCell := [(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(4,10),(4,11),(4,12),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9)]
def ql601b9 : List qCell := [(5,10),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(6,9),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(7,8),(7,9)]
def ql601b10 : List qCell := [(8,-2),(8,-1),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(8,7),(8,8),(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(9,7),(10,1),(10,2),(10,3),(10,4),(10,5),(10,6),(10,7)]
def ql601b11 : List qCell := [(11,1),(11,2),(11,3),(12,1),(12,3)]
def ql601 : List qCell := ql601b0 ++ ql601b1 ++ ql601b2 ++ ql601b3 ++ ql601b4 ++ ql601b5 ++ ql601b6 ++ ql601b7 ++ ql601b8 ++ ql601b9 ++ ql601b10 ++ ql601b11
def qn601 : (ql601).Nodup := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qm601 : qR := ⟨{(0,-2),(0,-1)},⟨(ql601 : Multiset qCell), Multiset.coe_nodup.mpr qn601⟩,29⟩
def qmeq_601 : qr 601 = qm601 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 601 = qv601 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 601 < 6 by decide,↓reduceDIte,he,qv601,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_236,qmeq_437,qmeq_469,qmeq_553,qmeq_592]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def ql602b0 : List qCell := [(-9,-1),(-9,1),(-8,-1),(-8,0),(-8,1),(-7,-3),(-7,-2),(-7,-1),(-7,0),(-7,1),(-7,2),(-7,3),(-7,4),(-7,5),(-6,-3),(-6,-2),(-6,-1),(-6,0),(-6,1),(-6,2),(-6,3),(-6,4),(-6,5),(-6,8),(-6,9)]
def ql602b1 : List qCell := [(-6,11),(-5,-3),(-5,-2),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,8),(-5,9),(-5,10),(-5,11),(-4,-5),(-4,-4),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4)]
def ql602b2 : List qCell := [(-4,5),(-4,6),(-4,7),(-4,8),(-4,9),(-4,10),(-4,11),(-4,12),(-4,13),(-4,14),(-3,-5),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9)]
def ql602b3 : List qCell := [(-3,10),(-3,11),(-3,12),(-3,13),(-2,-5),(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-2,11),(-2,12),(-2,13),(-2,14),(-2,15)]
def ql602b4 : List qCell := [(-2,16),(-1,-3),(-1,-2),(-1,-1),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(-1,11),(-1,12),(-1,13),(-1,14),(-1,15),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2)]
def ql602b5 : List qCell := [(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(0,15),(0,16),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)]
def ql602b6 : List qCell := [(1,8),(1,9),(1,10),(1,11),(1,12),(1,13),(1,14),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(2,12),(2,13),(2,14)]
def ql602b7 : List qCell := [(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(3,12),(3,13),(3,14),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3)]
def ql602b8 : List qCell := [(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(4,10),(4,11),(4,12),(4,13),(4,14),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(5,11)]
def ql602b9 : List qCell := [(5,12),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(6,9),(6,10),(6,11),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(7,8),(7,9),(7,10),(7,11)]
def ql602b10 : List qCell := [(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(8,7),(8,8),(8,9),(8,10),(9,3),(9,4),(9,5),(9,6),(9,7),(9,8),(9,9),(10,3),(10,4),(10,5),(10,6),(10,7),(10,8),(10,9)]
def ql602b11 : List qCell := [(11,3),(11,4),(11,5),(12,3),(12,5)]
def ql602 : List qCell := ql602b0 ++ ql602b1 ++ ql602b2 ++ ql602b3 ++ ql602b4 ++ ql602b5 ++ ql602b6 ++ ql602b7 ++ ql602b8 ++ ql602b9 ++ ql602b10 ++ ql602b11
def qn602 : (ql602).Nodup := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qm602 : qR := ⟨{(0,1),(0,2)},⟨(ql602 : Multiset qCell), Multiset.coe_nodup.mpr qn602⟩,29⟩
def qmeq_602 : qr 602 = qm602 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 602 = qv602 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 602 < 6 by decide,↓reduceDIte,he,qv602,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_236,qmeq_437,qmeq_467,qmeq_553,qmeq_592]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf324 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-6,-4),(-6,-3),(-6,-2),(-6,-1),(-6,1),(-6,2),(-6,3),(-6,4),(-5,-4),(-5,-3),(-5,-2),(-5,-1),(-5,1),(-5,2),(-5,3),(-5,4),(-4,-7),(-4,-6),(-4,-5),(-4,-4),(-4,-3),(-4,-2),(-4,-1),(-4,1),(-4,2)] : List qCell).toFinset)
def qf325 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-3,-8),(-3,-7),(-3,-6),(-3,-5),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-2,-8),(-2,-7),(-2,-6),(-2,-5),(-2,-4)] : List qCell).toFinset)
def qf326 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-1,-11),(-1,-10),(-1,-9),(-1,-8),(-1,-7),(-1,-6),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2)] : List qCell).toFinset)
def qf327 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(-1,11),(0,-10),(0,-9),(0,-8),(0,-7),(0,-6),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5)] : List qCell).toFinset)
def qf328 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(0,6),(0,7),(0,8),(0,9),(0,10),(1,-11),(1,-10),(1,-9),(1,-8),(1,-7),(1,-6),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8)] : List qCell).toFinset)
def qf329 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(1,9),(1,10),(1,11),(2,-9),(2,-8),(2,-7),(2,-6),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(3,-9),(3,-8),(3,-7)] : List qCell).toFinset)
def qf330 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(3,-6),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(4,-9),(4,-8),(4,-7),(4,-6),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1)] : List qCell).toFinset)
def qf331 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(5,-9),(5,-8),(5,-7),(5,-6),(5,-5),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5)] : List qCell).toFinset)
def qf332 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(5,6),(5,7),(5,8),(5,9),(6,-7),(6,-6),(6,-5),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(7,-7),(7,-6),(7,-5),(7,-4),(7,-3),(7,-2)] : List qCell).toFinset)
def qf333 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(8,-5),(8,-4),(8,-3),(8,-2),(8,-1),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(9,-5),(9,-4),(9,-3),(9,-2),(9,-1)] : List qCell).toFinset)
def qf334 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(9,0),(9,1),(9,2),(9,3),(9,4),(9,5),(10,-5),(10,-3),(10,-2),(10,-1),(10,0),(10,1),(10,2),(10,3),(10,5),(11,-3),(11,-2),(11,-1),(11,1),(11,2),(11,3),(12,-3),(12,-1),(12,1),(12,3)] : List qCell).toFinset)
def qm603 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,0)},(qf324 ∪ qf325 ∪ qf326 ∪ qf327 ∪ qf328 ∪ qf329 ∪ qf330 ∪ qf331 ∪ qf332 ∪ qf333 ∪ qf334),27⟩)
def qmeq_603 : qr 603 = qm603 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 603 = qv603 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 603 < 6 by decide,↓reduceDIte,he,qv603,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_505,qmeq_531,qmeq_533,qmeq_551,qmeq_573,qmeq_585,qmeq_586]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf335 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-7,-1),(-6,-1),(-6,0),(-6,1),(-6,6),(-6,7),(-6,9),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,4),(-5,6),(-5,7),(-5,8),(-5,9),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7)] : List qCell).toFinset)
def qf336 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-4,8),(-4,9),(-4,10),(-4,11),(-4,12),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-3,10),(-3,11),(-2,-2),(-2,-1),(-2,0),(-2,2),(-2,3),(-2,4),(-2,5)] : List qCell).toFinset)
def qf337 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-2,11),(-2,12),(-2,13),(-2,14),(-1,-7),(-1,-6),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9)] : List qCell).toFinset)
def qf338 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-1,10),(-1,11),(-1,12),(-1,13),(0,-6),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14)] : List qCell).toFinset)
def qf339 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(1,-6),(1,-5),(1,-4),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(1,12),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1)] : List qCell).toFinset)
def qf340 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(2,12),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9)] : List qCell).toFinset)
def qf341 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(3,10),(3,11),(3,12),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(4,10),(4,11),(4,12),(5,-4),(5,-3),(5,-2),(5,-1)] : List qCell).toFinset)
def qf342 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(6,-6),(6,-5),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7)] : List qCell).toFinset)
def qf343 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(6,8),(6,9),(6,10),(7,-6),(7,-5),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(7,8),(7,9),(7,10),(8,-5),(8,-4),(8,-3),(8,-2),(8,-1)] : List qCell).toFinset)
def qf344 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(8,7),(8,8),(9,-6),(9,-5),(9,-4),(9,-3),(9,-2),(9,-1),(9,0),(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(9,7),(10,-4),(10,-3)] : List qCell).toFinset)
def qf345 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(10,-2),(10,-1),(10,0),(10,1),(10,2),(10,3),(10,4),(10,5),(10,6),(10,7),(11,-4),(11,-3),(11,-2),(11,-1),(11,0),(11,1),(11,2),(11,3),(11,4),(12,-4),(12,-2),(12,-1),(12,0),(12,1),(12,2)] : List qCell).toFinset)
def qf346 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(12,3),(12,4),(13,-2),(13,-1),(13,0),(14,-2),(14,0)] : List qCell).toFinset)
def qm604 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,-1),(-2,0),(-1,-2),(0,-2)},(qf335 ∪ qf336 ∪ qf337 ∪ qf338 ∪ qf339 ∪ qf340 ∪ qf341 ∪ qf342 ∪ qf343 ∪ qf344 ∪ qf345 ∪ qf346),30⟩)
def qmeq_604 : qr 604 = qm604 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 604 = qv604 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 604 < 6 by decide,↓reduceDIte,he,qv604,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_350,qmeq_375,qmeq_597]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf347 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-7,-1),(-7,0),(-7,1),(-7,2),(-6,-1),(-6,0),(-6,1),(-6,2),(-6,3),(-6,4),(-6,6),(-6,7),(-6,9),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-5,6),(-5,7),(-5,8),(-5,9),(-4,-1),(-4,0)] : List qCell).toFinset)
def qf348 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-4,8),(-4,9),(-4,10),(-4,11),(-4,12),(-3,-3),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-3,10)] : List qCell).toFinset)
def qf349 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-3,11),(-2,-3),(-2,-2),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-2,11),(-2,12),(-2,13),(-2,14),(-1,-7),(-1,-6),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1)] : List qCell).toFinset)
def qf350 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(-1,11),(-1,12),(-1,13),(0,-6),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4)] : List qCell).toFinset)
def qf351 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(1,-7),(1,-6),(1,-5),(1,-4),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8)] : List qCell).toFinset)
def qf352 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(1,9),(1,10),(1,11),(1,12),(2,-6),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(2,12),(3,-5),(3,-4)] : List qCell).toFinset)
def qf353 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(3,12),(4,-6),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2)] : List qCell).toFinset)
def qf354 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(4,10),(4,11),(4,12),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10)] : List qCell).toFinset)
def qf355 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(6,-6),(6,-5),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(6,9),(6,10),(7,-6),(7,-5),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1)] : List qCell).toFinset)
def qf356 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(7,8),(7,9),(7,10),(8,-5),(8,-4),(8,-3),(8,-2),(8,-1),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(8,7),(8,8),(9,-6),(9,-5)] : List qCell).toFinset)
def qf357 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(9,-4),(9,-3),(9,-2),(9,-1),(9,0),(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(9,7),(10,-4),(10,-3),(10,-2),(10,-1),(10,0),(10,1),(10,2),(10,3),(10,4),(10,5),(10,6),(10,7),(11,-4)] : List qCell).toFinset)
def qf358 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(11,-3),(11,-2),(11,-1),(11,0),(11,1),(11,2),(11,3),(11,4),(12,-4),(12,-2),(12,-1),(12,0),(12,1),(12,2),(12,3),(12,4),(13,-2),(13,-1),(13,0),(14,-2),(14,0)] : List qCell).toFinset)
def qm605 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,-3),(-2,-3),(-2,-2),(-2,0),(0,-2)},(qf347 ∪ qf348 ∪ qf349 ∪ qf350 ∪ qf351 ∪ qf352 ∪ qf353 ∪ qf354 ∪ qf355 ∪ qf356 ∪ qf357 ∪ qf358),30⟩)
def qmeq_605 : qr 605 = qm605 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 605 = qv605 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 605 < 6 by decide,↓reduceDIte,he,qv605,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_383,qmeq_400,qmeq_520,qmeq_522,qmeq_530,qmeq_537,qmeq_550,qmeq_596,qmeq_598]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf359 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-5,-1),(-5,0),(-5,1),(-5,2),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,6),(-4,7),(-4,9),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,6),(-3,7),(-3,8),(-3,9),(-2,-1),(-2,0)] : List qCell).toFinset)
def qf360 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-2,11),(-2,12),(-1,-4),(-1,-3),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9)] : List qCell).toFinset)
def qf361 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-1,10),(-1,11),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(1,-7),(1,-6),(1,-5),(1,-4),(1,-3)] : List qCell).toFinset)
def qf362 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(1,12),(1,13),(2,-6),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2)] : List qCell).toFinset)
def qf363 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(2,12),(2,13),(2,14),(3,-7),(3,-6),(3,-5),(3,-4),(3,-3),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6)] : List qCell).toFinset)
def qf364 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(3,7),(3,8),(3,9),(3,10),(3,11),(3,12),(4,-6),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(4,10),(4,11),(4,12)] : List qCell).toFinset)
def qf365 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(5,-5),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(5,11),(5,12),(6,-6),(6,-5),(6,-4),(6,-3),(6,-2),(6,-1),(6,0)] : List qCell).toFinset)
def qf366 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(6,9),(6,10),(6,11),(6,12),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(7,8)] : List qCell).toFinset)
def qf367 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(7,9),(7,10),(8,-6),(8,-5),(8,-4),(8,-3),(8,-2),(8,-1),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(8,7),(8,8),(8,9),(8,10),(9,-6),(9,-5),(9,-4),(9,-3),(9,-2),(9,-1)] : List qCell).toFinset)
def qf368 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(9,0),(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(9,7),(9,8),(9,9),(9,10),(10,-5),(10,-4),(10,-3),(10,-2),(10,-1),(10,0),(10,1),(10,2),(10,3),(10,4),(10,5),(10,6),(10,7),(10,8)] : List qCell).toFinset)
def qf369 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(11,-6),(11,-5),(11,-4),(11,-3),(11,-2),(11,-1),(11,0),(11,1),(11,2),(11,3),(11,4),(11,5),(11,6),(11,7),(12,-4),(12,-3),(12,-2),(12,-1),(12,0),(12,1),(12,2),(12,3),(12,4),(12,5),(12,6)] : List qCell).toFinset)
def qf370 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(12,7),(13,-4),(13,-3),(13,-2),(13,-1),(13,0),(13,1),(13,2),(13,3),(13,4),(14,-4),(14,-2),(14,-1),(14,0),(14,1),(14,2),(14,3),(14,4),(15,-2),(15,-1),(15,0),(16,-2),(16,0)] : List qCell).toFinset)
def qm606 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(0,-3),(0,-2),(2,-2)},(qf359 ∪ qf360 ∪ qf361 ∪ qf362 ∪ qf363 ∪ qf364 ∪ qf365 ∪ qf366 ∪ qf367 ∪ qf368 ∪ qf369 ∪ qf370),31⟩)
def qmeq_606 : qr 606 = qm606 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 606 = qv606 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 606 < 6 by decide,↓reduceDIte,he,qv606,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_119,qmeq_123,qmeq_274,qmeq_605]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf371 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-7,-1),(-7,0),(-7,1),(-7,2),(-6,-1),(-6,0),(-6,1),(-6,2),(-6,6),(-6,7),(-6,9),(-5,-2),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,4),(-5,6),(-5,7),(-5,8),(-5,9),(-4,-5),(-4,-4),(-4,-3),(-4,-2)] : List qCell).toFinset)
def qf372 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-4,8),(-4,9),(-4,10),(-4,11),(-4,12),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6)] : List qCell).toFinset)
def qf373 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-3,7),(-3,8),(-3,9),(-3,10),(-3,11),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-2,11),(-2,12),(-2,13),(-2,14),(-1,-2),(-1,0)] : List qCell).toFinset)
def qf374 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(-1,11),(-1,12),(-1,13),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8)] : List qCell).toFinset)
def qf375 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(1,-4),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(1,12),(2,-6),(2,-5),(2,-4)] : List qCell).toFinset)
def qf376 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(2,12),(3,-6),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2)] : List qCell).toFinset)
def qf377 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(3,12),(4,-7),(4,-6),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7)] : List qCell).toFinset)
def qf378 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(4,8),(4,9),(4,10),(4,11),(4,12),(5,-8),(5,-7),(5,-6),(5,-5),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(6,-7)] : List qCell).toFinset)
def qf379 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(6,-6),(6,-5),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(6,9),(7,-8),(7,-7),(7,-6),(7,-5),(7,-4),(7,-3),(7,-2),(7,-1),(7,0)] : List qCell).toFinset)
def qf380 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(7,8),(7,9),(8,-6),(8,-5),(8,-4),(8,-3),(8,-2),(8,-1),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(8,7),(8,8),(9,-6)] : List qCell).toFinset)
def qf381 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(9,-5),(9,-4),(9,-3),(9,-2),(9,-1),(9,0),(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(9,7),(10,-6),(10,-5),(10,-4),(10,-3),(10,-2),(10,-1),(10,0),(10,1),(10,2),(10,3),(10,4),(10,5)] : List qCell).toFinset)
def qf382 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(10,6),(10,7),(11,-5),(11,-4),(11,-3),(11,-2),(11,-1),(11,0),(11,1),(11,2),(11,3),(12,-4),(12,-3),(12,-2),(12,-1),(12,0),(12,1),(12,3),(13,-4),(13,-3),(13,-2),(13,-1),(13,0),(13,1)] : List qCell).toFinset)
def qm607 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-2),(0,-3),(0,-2),(0,-1)},(qf371 ∪ qf372 ∪ qf373 ∪ qf374 ∪ qf375 ∪ qf376 ∪ qf377 ∪ qf378 ∪ qf379 ∪ qf380 ∪ qf381 ∪ qf382),29⟩)
def qmeq_607 : qr 607 = qm607 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 607 = qv607 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 607 < 6 by decide,↓reduceDIte,he,qv607,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_314,qmeq_419,qmeq_420,qmeq_571,qmeq_589]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf383 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-9,-1),(-9,1),(-9,3),(-8,-1),(-8,0),(-8,1),(-8,2),(-8,3),(-7,-1),(-7,0),(-7,1),(-7,2),(-7,3),(-7,4),(-7,5),(-7,6),(-7,8),(-6,-3),(-6,-2),(-6,-1),(-6,0),(-6,1),(-6,2),(-6,3),(-6,4)] : List qCell).toFinset)
def qf384 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-6,5),(-6,6),(-6,7),(-6,8),(-5,-2),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-5,8),(-5,9),(-5,10),(-5,11),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3)] : List qCell).toFinset)
def qf385 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-4,4),(-4,5),(-4,6),(-4,7),(-4,8),(-4,9),(-4,10),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-3,10),(-3,11),(-3,12),(-3,13),(-2,-3),(-2,-1)] : List qCell).toFinset)
def qf386 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-2,11),(-2,12),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8)] : List qCell).toFinset)
def qf387 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-1,9),(-1,10),(-1,11),(-1,12),(-1,13),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(1,-7),(1,-6),(1,-5)] : List qCell).toFinset)
def qf388 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(1,12),(1,13),(2,-7),(2,-6),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1)] : List qCell).toFinset)
def qf389 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(2,12),(2,13),(2,14),(3,-7),(3,-6),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2)] : List qCell).toFinset)
def qf390 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(3,12),(4,-7),(4,-6),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7)] : List qCell).toFinset)
def qf391 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(4,8),(4,9),(4,10),(4,11),(4,12),(5,-6),(5,-5),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(5,11),(5,12),(6,-6)] : List qCell).toFinset)
def qf392 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(6,-5),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(6,9),(6,10),(6,11),(6,12),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2)] : List qCell).toFinset)
def qf393 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(7,3),(7,4),(7,5),(7,6),(7,7),(7,8),(7,9),(7,10),(8,-6),(8,-5),(8,-4),(8,-3),(8,-2),(8,-1),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(8,7),(8,8),(8,9),(8,10)] : List qCell).toFinset)
def qf394 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(9,-6),(9,-5),(9,-4),(9,-3),(9,-2),(9,-1),(9,0),(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(9,7),(9,8),(9,9),(9,10),(10,-5),(10,-4),(10,-3),(10,-2),(10,-1),(10,0),(10,1),(10,2)] : List qCell).toFinset)
def qf395 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(10,3),(10,4),(10,5),(10,6),(10,7),(10,8),(11,-6),(11,-5),(11,-4),(11,-3),(11,-2),(11,-1),(11,0),(11,1),(11,2),(11,3),(11,4),(11,5),(11,6),(11,7),(12,-4),(12,-3),(12,-2),(12,-1),(12,0)] : List qCell).toFinset)
def qf396 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(12,1),(12,2),(12,3),(12,4),(12,5),(12,6),(12,7),(13,-4),(13,-3),(13,-2),(13,-1),(13,0),(13,1),(13,2),(13,3),(13,4),(14,-4),(14,-2),(14,-1),(14,0),(14,1),(14,2),(14,3),(14,4),(15,-2)] : List qCell).toFinset)
def qf397 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(15,-1),(15,0),(16,-2),(16,0)] : List qCell).toFinset)
def qm608 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-1,-3),(-1,-2),(0,-2)},(qf383 ∪ qf384 ∪ qf385 ∪ qf386 ∪ qf387 ∪ qf388 ∪ qf389 ∪ qf390 ∪ qf391 ∪ qf392 ∪ qf393 ∪ qf394 ∪ qf395 ∪ qf396 ∪ qf397),32⟩)
def qmeq_608 : qr 608 = qm608 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 608 = qv608 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 608 < 6 by decide,↓reduceDIte,he,qv608,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_486,qmeq_515,qmeq_521,qmeq_580,qmeq_581,qmeq_593,qmeq_599,qmeq_606]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf398 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-10,-2),(-10,-1),(-10,0),(-10,1),(-9,-2),(-9,-1),(-9,0),(-9,1),(-8,-2),(-8,-1),(-8,0),(-8,1),(-8,2),(-8,4),(-7,-4),(-7,-3),(-7,-2),(-7,-1),(-7,0),(-7,1),(-7,2),(-7,3),(-7,4),(-7,5),(-6,-4)] : List qCell).toFinset)
def qf399 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-6,-3),(-6,-2),(-6,-1),(-6,0),(-6,1),(-6,2),(-6,3),(-6,4),(-5,-4),(-5,-3),(-5,-2),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-4,-4),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3)] : List qCell).toFinset)
def qf400 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-4,4),(-4,6),(-4,7),(-4,9),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4)] : List qCell).toFinset)
def qf401 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-2,11),(-2,12),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(-1,11),(0,-2),(0,-1),(0,0),(0,1)] : List qCell).toFinset)
def qf402 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(1,-7),(1,-6),(1,-5),(1,-4),(1,-3),(1,-2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] : List qCell).toFinset)
def qf403 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(1,12),(1,13),(2,-6),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10)] : List qCell).toFinset)
def qf404 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(2,11),(2,12),(2,13),(2,14),(3,-6),(3,-5),(3,-4),(3,-3),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(3,12),(4,-5),(4,-4),(4,-3)] : List qCell).toFinset)
def qf405 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(4,10),(4,11),(4,12),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5)] : List qCell).toFinset)
def qf406 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(5,6),(5,7),(5,8),(5,9),(5,10),(5,11),(5,12),(6,-5),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(6,9),(6,10),(6,11),(6,12)] : List qCell).toFinset)
def qf407 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(7,8),(7,9),(7,10),(8,-6),(8,-5),(8,-4),(8,-3),(8,-2),(8,-1),(8,0),(8,1),(8,2),(8,3)] : List qCell).toFinset)
def qf408 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(8,4),(8,5),(8,6),(8,7),(8,8),(8,9),(8,10),(9,-6),(9,-5),(9,-4),(9,-3),(9,-2),(9,-1),(9,0),(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(9,7),(9,8),(9,9),(9,10),(10,-5)] : List qCell).toFinset)
def qf409 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(10,-4),(10,-3),(10,-2),(10,-1),(10,0),(10,1),(10,2),(10,3),(10,4),(10,5),(10,6),(10,7),(10,8),(11,-6),(11,-5),(11,-4),(11,-3),(11,-2),(11,-1),(11,0),(11,1),(11,2),(11,3),(11,4),(11,5)] : List qCell).toFinset)
def qf410 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(11,6),(11,7),(12,-4),(12,-3),(12,-2),(12,-1),(12,0),(12,1),(12,2),(12,3),(12,4),(12,5),(12,6),(12,7),(13,-4),(13,-3),(13,-2),(13,-1),(13,0),(13,1),(13,2),(13,3),(13,4),(14,-4),(14,-2)] : List qCell).toFinset)
def qf411 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(14,-1),(14,0),(14,1),(14,2),(14,3),(14,4),(15,-2),(15,-1),(15,0),(16,-2),(16,0)] : List qCell).toFinset)
def qm609 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(0,-2),(0,-1),(1,-2),(2,-2)},(qf398 ∪ qf399 ∪ qf400 ∪ qf401 ∪ qf402 ∪ qf403 ∪ qf404 ∪ qf405 ∪ qf406 ∪ qf407 ∪ qf408 ∪ qf409 ∪ qf410 ∪ qf411),31⟩)
def qmeq_609 : qr 609 = qm609 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 609 = qv609 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 609 < 6 by decide,↓reduceDIte,he,qv609,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_107,qmeq_221,qmeq_286,qmeq_532,qmeq_542,qmeq_562,qmeq_575,qmeq_604]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf412 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-12,0),(-12,1),(-12,2),(-12,3),(-11,0),(-11,1),(-11,2),(-11,3),(-10,0),(-10,1),(-10,2),(-10,3),(-10,4),(-10,6),(-9,-2),(-9,-1),(-9,0),(-9,1),(-9,2),(-9,3),(-9,4),(-9,5),(-9,6),(-9,7),(-8,-2)] : List qCell).toFinset)
def qf413 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-8,-1),(-8,0),(-8,1),(-8,2),(-8,3),(-8,4),(-8,5),(-8,6),(-7,-2),(-7,-1),(-7,0),(-7,1),(-7,2),(-7,3),(-7,4),(-7,5),(-7,6),(-6,-2),(-6,-1),(-6,0),(-6,1),(-6,2),(-6,3),(-6,4),(-6,5)] : List qCell).toFinset)
def qf414 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-6,6),(-6,8),(-6,9),(-6,11),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-5,8),(-5,9),(-5,10),(-5,11),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6)] : List qCell).toFinset)
def qf415 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-4,7),(-4,8),(-4,9),(-4,10),(-4,11),(-4,12),(-4,13),(-4,14),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-3,10),(-3,11),(-3,12),(-3,13),(-2,0),(-2,1),(-2,2),(-2,3)] : List qCell).toFinset)
def qf416 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-2,11),(-2,12),(-2,13),(-2,14),(-2,15),(-2,16),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7)] : List qCell).toFinset)
def qf417 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-1,8),(-1,9),(-1,10),(-1,11),(-1,12),(-1,13),(-1,14),(-1,15),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11)] : List qCell).toFinset)
def qf418 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(0,12),(0,13),(0,14),(0,15),(0,16),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(1,12),(1,13),(1,14)] : List qCell).toFinset)
def qf419 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(2,12),(2,13),(2,14),(3,-3),(3,-2),(3,-1),(3,0),(3,1)] : List qCell).toFinset)
def qf420 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(3,12),(3,13),(3,14),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8)] : List qCell).toFinset)
def qf421 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(4,9),(4,10),(4,11),(4,12),(4,13),(4,14),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(5,11),(5,12),(6,-4),(6,-3),(6,-2)] : List qCell).toFinset)
def qf422 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(6,9),(6,10),(6,11),(6,12),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6)] : List qCell).toFinset)
def qf423 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(7,7),(7,8),(7,9),(7,10),(7,11),(7,12),(8,-3),(8,-2),(8,-1),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(8,7),(8,8),(8,9),(8,10),(9,-4),(9,-3),(9,-2),(9,-1),(9,0)] : List qCell).toFinset)
def qf424 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(9,7),(9,8),(9,9),(10,-2),(10,-1),(10,0),(10,1),(10,2),(10,3),(10,4),(10,5),(10,6),(10,7),(10,8),(10,9),(11,-2),(11,-1),(11,0),(11,1)] : List qCell).toFinset)
def qf425 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(11,2),(11,3),(11,4),(11,5),(11,6),(12,-2),(12,0),(12,1),(12,2),(12,3),(12,4),(12,5),(12,6),(13,0),(13,1),(13,2),(14,0),(14,2)] : List qCell).toFinset)
def qm610 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-2,1),(-1,0)},(qf412 ∪ qf413 ∪ qf414 ∪ qf415 ∪ qf416 ∪ qf417 ∪ qf418 ∪ qf419 ∪ qf420 ∪ qf421 ∪ qf422 ∪ qf423 ∪ qf424 ∪ qf425),32⟩)
def qmeq_610 : qr 610 = qm610 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 610 = qv610 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 610 < 6 by decide,↓reduceDIte,he,qv610,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_107,qmeq_221,qmeq_286,qmeq_472,qmeq_532,qmeq_542,qmeq_566,qmeq_609]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def ql611b0 : List qCell := [(-16,0),(-16,2),(-15,0),(-15,1),(-15,2),(-14,-4),(-14,-3),(-14,-2),(-14,-1),(-14,0),(-14,1),(-14,2),(-14,4),(-13,-4),(-13,-3),(-13,-2),(-13,-1),(-13,0),(-13,1),(-13,2),(-13,3),(-13,4),(-12,-5),(-12,-4),(-12,-3)]
def ql611b1 : List qCell := [(-12,-2),(-12,-1),(-12,0),(-12,1),(-12,2),(-12,3),(-12,4),(-11,-7),(-11,-6),(-11,-5),(-11,-4),(-11,-3),(-11,-2),(-11,-1),(-11,0),(-11,1),(-11,2),(-11,3),(-11,4),(-11,5),(-11,6),(-10,-8),(-10,-7),(-10,-6),(-10,-5)]
def ql611b2 : List qCell := [(-10,-4),(-10,-3),(-10,-2),(-10,-1),(-10,0),(-10,1),(-10,2),(-10,3),(-10,4),(-10,5),(-9,-10),(-9,-9),(-9,-8),(-9,-7),(-9,-6),(-9,-5),(-9,-4),(-9,-3),(-9,-2),(-9,-1),(-9,0),(-9,1),(-9,2),(-9,3),(-9,4)]
def ql611b3 : List qCell := [(-9,5),(-9,6),(-8,-10),(-8,-9),(-8,-8),(-8,-7),(-8,-6),(-8,-5),(-8,-4),(-8,-3),(-8,-2),(-8,-1),(-8,0),(-8,1),(-8,2),(-8,3),(-8,4),(-8,5),(-8,6),(-7,-10),(-7,-9),(-7,-8),(-7,-7),(-7,-6),(-7,-5)]
def ql611b4 : List qCell := [(-7,-4),(-7,-3),(-7,-2),(-7,-1),(-7,0),(-7,1),(-7,2),(-7,3),(-7,4),(-6,-10),(-6,-9),(-6,-8),(-6,-7),(-6,-6),(-6,-5),(-6,-4),(-6,-3),(-6,-2),(-6,-1),(-6,0),(-6,1),(-6,2),(-6,3),(-6,4),(-6,5)]
def ql611b5 : List qCell := [(-5,-12),(-5,-11),(-5,-10),(-5,-9),(-5,-8),(-5,-7),(-5,-6),(-5,-5),(-5,-4),(-5,-3),(-5,-2),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-4,-11),(-4,-10),(-4,-9),(-4,-8),(-4,-7),(-4,-6),(-4,-5),(-4,-4)]
def ql611b6 : List qCell := [(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-3,-12),(-3,-11),(-3,-10),(-3,-9),(-3,-8),(-3,-7),(-3,-6),(-3,-5),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3)]
def ql611b7 : List qCell := [(-3,4),(-3,5),(-3,6),(-3,7),(-2,-9),(-2,-8),(-2,-7),(-2,-6),(-2,-5),(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-1,-8),(-1,-7),(-1,-6)]
def ql611b8 : List qCell := [(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(0,-9),(0,-8),(0,-7),(0,-6),(0,-5),(0,-4),(0,-3),(0,-2),(0,0),(0,1),(0,2)]
def ql611b9 : List qCell := [(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,-7),(1,-6),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10)]
def ql611b10 : List qCell := [(1,11),(1,12),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1)]
def ql611b11 : List qCell := [(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(3,12),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8)]
def ql611b12 : List qCell := [(4,9),(4,10),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(6,-6),(6,-5),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1)]
def ql611b13 : List qCell := [(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(6,9),(6,10),(7,-6),(7,-5),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(7,8),(7,9)]
def ql611b14 : List qCell := [(7,10),(8,-5),(8,-4),(8,-3),(8,-2),(8,-1),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(8,7),(8,8),(9,-6),(9,-5),(9,-4),(9,-3),(9,-2),(9,-1),(9,0),(9,1),(9,2),(9,3)]
def ql611b15 : List qCell := [(9,4),(9,5),(9,6),(9,7),(10,-4),(10,-3),(10,-2),(10,-1),(10,0),(10,1),(10,2),(10,3),(10,4),(10,5),(11,-4),(11,-3),(11,-2),(11,-1),(11,0),(11,1),(11,2),(11,3),(11,4),(12,-4),(12,-2)]
def ql611b16 : List qCell := [(12,-1),(12,0),(12,1),(12,2),(12,3),(12,4),(13,-2),(13,-1),(13,0),(14,-2),(14,0)]
def ql611 : List qCell := ql611b0 ++ ql611b1 ++ ql611b2 ++ ql611b3 ++ ql611b4 ++ ql611b5 ++ ql611b6 ++ ql611b7 ++ ql611b8 ++ ql611b9 ++ ql611b10 ++ ql611b11 ++ ql611b12 ++ ql611b13 ++ ql611b14 ++ ql611b15 ++ ql611b16
def qn611 : (ql611).Nodup := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qm611 : qR := ⟨{(-2,0),(-1,0)},⟨(ql611 : Multiset qCell), Multiset.coe_nodup.mpr qn611⟩,29⟩
def qmeq_611 : qr 611 = qm611 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 611 = qv611 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 611 < 6 by decide,↓reduceDIte,he,qv611,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_456,qmeq_594]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf443 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-17,0),(-17,2),(-16,0),(-16,1),(-16,2),(-15,-4),(-15,-3),(-15,-2),(-15,-1),(-15,0),(-15,1),(-15,2),(-15,4),(-14,-4),(-14,-3),(-14,-2),(-14,-1),(-14,0),(-14,1),(-14,2),(-14,3),(-14,4),(-13,-5),(-13,-4),(-13,-3)] : List qCell).toFinset)
def qf444 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-13,-2),(-13,-1),(-13,0),(-13,1),(-13,2),(-13,3),(-13,4),(-12,-7),(-12,-6),(-12,-5),(-12,-4),(-12,-3),(-12,-2),(-12,-1),(-12,0),(-12,1),(-12,2),(-12,3),(-12,4),(-12,5),(-12,6),(-11,-8),(-11,-7),(-11,-6),(-11,-5)] : List qCell).toFinset)
def qf445 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-11,-4),(-11,-3),(-11,-2),(-11,-1),(-11,0),(-11,1),(-11,2),(-11,3),(-11,4),(-11,5),(-10,-10),(-10,-9),(-10,-8),(-10,-7),(-10,-6),(-10,-5),(-10,-4),(-10,-3),(-10,-2),(-10,-1),(-10,0),(-10,1),(-10,2),(-10,3),(-10,4)] : List qCell).toFinset)
def qf446 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-10,5),(-10,6),(-9,-10),(-9,-9),(-9,-8),(-9,-7),(-9,-6),(-9,-5),(-9,-4),(-9,-3),(-9,-2),(-9,-1),(-9,0),(-9,1),(-9,2),(-9,3),(-9,4),(-9,5),(-9,6),(-8,-10),(-8,-9),(-8,-8),(-8,-7),(-8,-6),(-8,-5)] : List qCell).toFinset)
def qf447 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-8,-4),(-8,-3),(-8,-2),(-8,-1),(-8,0),(-8,1),(-8,2),(-8,3),(-8,4),(-7,-10),(-7,-9),(-7,-8),(-7,-7),(-7,-6),(-7,-5),(-7,-4),(-7,-3),(-7,-2),(-7,-1),(-7,0),(-7,1),(-7,2),(-7,3),(-7,4),(-7,5)] : List qCell).toFinset)
def qf448 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-6,-12),(-6,-11),(-6,-10),(-6,-9),(-6,-8),(-6,-7),(-6,-6),(-6,-5),(-6,-4),(-6,-3),(-6,-2),(-6,-1),(-6,0),(-6,1),(-6,2),(-6,3),(-6,4),(-5,-11),(-5,-10),(-5,-9),(-5,-8),(-5,-7),(-5,-6),(-5,-5),(-5,-4)] : List qCell).toFinset)
def qf449 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-5,-3),(-5,-2),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-4,-12),(-4,-11),(-4,-10),(-4,-9),(-4,-8),(-4,-7),(-4,-6),(-4,-5),(-4,-4),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,3),(-4,5),(-3,-8)] : List qCell).toFinset)
def qf450 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-3,-7),(-3,-6),(-3,-5),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,2),(-3,3),(-3,4),(-3,5),(-2,-8),(-2,-7),(-2,-6),(-2,-5),(-2,-4),(-2,-3),(-2,-2),(-2,0),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6)] : List qCell).toFinset)
def qf451 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-2,7),(-2,8),(-1,-8),(-1,-7),(-1,-6),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,0),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(0,-5),(0,-4),(0,-3),(0,-2),(0,0),(0,1),(0,2),(0,3)] : List qCell).toFinset)
def qf452 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(0,4),(0,5),(0,6),(0,7),(0,8),(1,-5),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(1,12),(2,-4),(2,-3),(2,-2),(2,-1)] : List qCell).toFinset)
def qf453 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8)] : List qCell).toFinset)
def qf454 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(3,9),(3,10),(3,11),(3,12),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(4,10),(5,-4),(5,-3),(5,-2),(5,-1),(5,0)] : List qCell).toFinset)
def qf455 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(6,-6),(6,-5),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8)] : List qCell).toFinset)
def qf456 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(6,9),(6,10),(7,-6),(7,-5),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(7,8),(7,9),(7,10),(8,-5),(8,-4),(8,-3),(8,-2),(8,-1),(8,0)] : List qCell).toFinset)
def qf457 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(8,7),(8,8),(9,-6),(9,-5),(9,-4),(9,-3),(9,-2),(9,-1),(9,0),(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(9,7),(10,-4),(10,-3),(10,-2)] : List qCell).toFinset)
def qf458 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(10,-1),(10,0),(10,1),(10,2),(10,3),(10,4),(10,5),(11,-4),(11,-3),(11,-2),(11,-1),(11,0),(11,1),(11,2),(11,3),(11,4),(12,-4),(12,-2),(12,-1),(12,0),(12,1),(12,2),(12,3),(12,4),(13,-2)] : List qCell).toFinset)
def qf459 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(13,-1),(13,0),(14,-2),(14,0)] : List qCell).toFinset)
def qm612 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-3,0),(-2,0),(-1,0)},(qf443 ∪ qf444 ∪ qf445 ∪ qf446 ∪ qf447 ∪ qf448 ∪ qf449 ∪ qf450 ∪ qf451 ∪ qf452 ∪ qf453 ∪ qf454 ∪ qf455 ∪ qf456 ∪ qf457 ∪ qf458 ∪ qf459),29⟩)
def qmeq_612 : qr 612 = qm612 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 612 = qv612 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 612 < 6 by decide,↓reduceDIte,he,qv612,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_589]
          run_tac qhb (← `(tactic| (apply qx <;> decide +kernel))))))
def qf460 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-17,-2),(-17,0),(-17,2),(-16,-2),(-16,-1),(-16,0),(-16,1),(-16,2),(-15,-4),(-15,-3),(-15,-2),(-15,-1),(-15,0),(-15,1),(-15,2),(-15,3),(-15,4),(-14,-4),(-14,-3),(-14,-2),(-14,-1),(-14,0),(-14,1),(-14,2),(-14,3)] : List qCell).toFinset)
def qf461 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-14,4),(-13,-5),(-13,-4),(-13,-3),(-13,-2),(-13,-1),(-13,0),(-13,1),(-13,2),(-13,3),(-13,4),(-13,5),(-12,-7),(-12,-6),(-12,-5),(-12,-4),(-12,-3),(-12,-2),(-12,-1),(-12,0),(-12,1),(-12,2),(-12,3),(-12,4),(-12,5)] : List qCell).toFinset)
def qf462 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-12,6),(-12,7),(-11,-8),(-11,-7),(-11,-6),(-11,-5),(-11,-4),(-11,-3),(-11,-2),(-11,-1),(-11,0),(-11,1),(-11,2),(-11,3),(-11,4),(-11,5),(-11,6),(-11,7),(-11,8),(-10,-10),(-10,-9),(-10,-8),(-10,-7),(-10,-6),(-10,-5)] : List qCell).toFinset)
def qf463 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-10,-4),(-10,-3),(-10,-2),(-10,-1),(-10,0),(-10,1),(-10,2),(-10,3),(-10,4),(-10,5),(-10,6),(-10,7),(-10,8),(-10,9),(-10,10),(-9,-10),(-9,-9),(-9,-8),(-9,-7),(-9,-6),(-9,-5),(-9,-4),(-9,-3),(-9,-2),(-9,-1)] : List qCell).toFinset)
def qf464 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-9,0),(-9,1),(-9,2),(-9,3),(-9,4),(-9,5),(-9,6),(-9,7),(-9,8),(-9,9),(-9,10),(-8,-10),(-8,-9),(-8,-8),(-8,-7),(-8,-6),(-8,-5),(-8,-4),(-8,-3),(-8,-2),(-8,-1),(-8,0),(-8,1),(-8,2),(-8,3)] : List qCell).toFinset)
def qf465 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-8,4),(-8,5),(-8,6),(-8,7),(-8,8),(-8,9),(-8,10),(-7,-10),(-7,-9),(-7,-8),(-7,-7),(-7,-6),(-7,-5),(-7,-4),(-7,-3),(-7,-2),(-7,-1),(-7,0),(-7,1),(-7,2),(-7,3),(-7,4),(-7,5),(-7,6),(-7,7)] : List qCell).toFinset)
def qf466 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-7,8),(-7,9),(-7,10),(-6,-12),(-6,-11),(-6,-10),(-6,-9),(-6,-8),(-6,-7),(-6,-6),(-6,-5),(-6,-4),(-6,-3),(-6,-2),(-6,-1),(-6,0),(-6,1),(-6,2),(-6,3),(-6,4),(-6,5),(-6,6),(-6,7),(-6,8),(-6,9)] : List qCell).toFinset)
def qf467 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-6,10),(-6,11),(-6,12),(-5,-12),(-5,-11),(-5,-10),(-5,-9),(-5,-8),(-5,-7),(-5,-6),(-5,-5),(-5,-4),(-5,-3),(-5,-2),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-5,8),(-5,9)] : List qCell).toFinset)
def qf468 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-5,10),(-5,11),(-4,-13),(-4,-12),(-4,-11),(-4,-10),(-4,-9),(-4,-8),(-4,-7),(-4,-6),(-4,-5),(-4,-4),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-4,8),(-4,9)] : List qCell).toFinset)
def qf469 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-4,10),(-4,11),(-4,12),(-3,-13),(-3,-12),(-3,-11),(-3,-10),(-3,-9),(-3,-8),(-3,-7),(-3,-6),(-3,-5),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8)] : List qCell).toFinset)
def qf470 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-2,-13),(-2,-12),(-2,-11),(-2,-10),(-2,-9),(-2,-8),(-2,-7),(-2,-6),(-2,-5),(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-1,-13),(-1,-12),(-1,-11),(-1,-10)] : List qCell).toFinset)
def qf471 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-1,-9),(-1,-8),(-1,-7),(-1,-6),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(0,-13),(0,-12),(0,-11),(0,-10),(0,-9),(0,-8),(0,-7),(0,-6)] : List qCell).toFinset)
def qf472 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,-13),(1,-12),(1,-11),(1,-10),(1,-9),(1,-8),(1,-7),(1,-6),(1,-5),(1,-4),(1,-3),(1,-2)] : List qCell).toFinset)
def qf473 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,-13),(2,-12),(2,-11),(2,-10),(2,-9),(2,-8),(2,-7),(2,-6),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1)] : List qCell).toFinset)
def qf474 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(2,12),(3,-12),(3,-11),(3,-10),(3,-9),(3,-8),(3,-7),(3,-6),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1)] : List qCell).toFinset)
def qf475 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(4,-12),(4,-11),(4,-10),(4,-9),(4,-8),(4,-7),(4,-6),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2)] : List qCell).toFinset)
def qf476 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(4,10),(4,11),(4,12),(5,-10),(5,-9),(5,-8),(5,-7),(5,-6),(5,-5),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4)] : List qCell).toFinset)
def qf477 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(6,-10),(6,-9),(6,-8),(6,-7),(6,-6),(6,-5),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8)] : List qCell).toFinset)
def qf478 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(6,9),(6,10),(7,-10),(7,-9),(7,-8),(7,-7),(7,-6),(7,-5),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(7,8),(7,9),(7,10),(8,-10),(8,-9)] : List qCell).toFinset)
def qf479 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(8,-8),(8,-7),(8,-6),(8,-5),(8,-4),(8,-3),(8,-2),(8,-1),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(8,7),(8,8),(8,9),(8,10),(9,-8),(9,-7),(9,-6),(9,-5),(9,-4),(9,-3)] : List qCell).toFinset)
def qf480 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(9,-2),(9,-1),(9,0),(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(9,7),(9,8),(10,-7),(10,-6),(10,-5),(10,-4),(10,-3),(10,-2),(10,-1),(10,0),(10,1),(10,2),(10,3),(10,4),(10,5),(10,6)] : List qCell).toFinset)
def qf481 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(10,7),(11,-5),(11,-4),(11,-3),(11,-2),(11,-1),(11,0),(11,1),(11,2),(11,3),(11,4),(11,5),(12,-4),(12,-3),(12,-2),(12,-1),(12,0),(12,1),(12,2),(12,3),(12,4),(13,-4),(13,-3),(13,-2),(13,-1)] : List qCell).toFinset)
def qf482 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(13,0),(13,1),(13,2),(13,3),(13,4),(14,-2),(14,-1),(14,0),(14,1),(14,2),(15,-2),(15,0),(15,2)] : List qCell).toFinset)
def qm613 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{(-2,0),(-1,0),(-1,1)},(qf460 ∪ qf461 ∪ qf462 ∪ qf463 ∪ qf464 ∪ qf465 ∪ qf466 ∪ qf467 ∪ qf468 ∪ qf469 ∪ qf470 ∪ qf471 ∪ qf472 ∪ qf473 ∪ qf474 ∪ qf475 ∪ qf476 ∪ qf477 ∪ qf478 ∪ qf479 ∪ qf480 ∪ qf481 ∪ qf482),30⟩)
def qcompactStep (a : qCell) (xs : List qCell) : List qCell :=
  match xs with
  | [] => [a]
  | b :: bs => if a = b then xs else a :: xs
def qcompact (xs : List qCell) : List qCell := xs.foldr qcompactStep []
def qcompactStep_mem (x a : qCell) (xs : List qCell) :
    x ∈ qcompactStep a xs ↔ x = a ∨ x ∈ xs := by
  set_option maxRecDepth 100000 in
    cases xs with
    | nil => simp [qcompactStep]
    | cons b bs =>
        by_cases h : a = b
        · subst b
          simp [qcompactStep,or_assoc,or_self_left]
        · simp [qcompactStep,h]
def qcompact_mem (x : qCell) (xs : List qCell) : x ∈ qcompact xs ↔ x ∈ xs := by
  set_option maxRecDepth 100000 in
    induction xs with
    | nil => rfl
    | cons a xs ih => simpa only [qcompact,List.foldr_cons,qcompactStep_mem,List.mem_cons] using or_congr Iff.rfl ih
def qcellLE (a b : qCell) : Bool := decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2))
def qmergeFuel (n : ℕ) : List qCell → List qCell → List qCell :=
  Nat.rec (fun xs ys => xs ++ ys) (fun _ rec xs ys => match xs,ys with
    | [],ys => ys
    | xs,[] => xs
    | a :: xs,b :: ys => if qcellLE a b then a :: rec xs (b :: ys) else b :: rec (a :: xs) ys) n
def qmergeFuel_mem (x : qCell) (n : ℕ) (xs ys : List qCell) :
    x ∈ qmergeFuel n xs ys ↔ x ∈ xs ∨ x ∈ ys := by
  set_option maxRecDepth 100000 in
    induction n generalizing xs ys with
    | zero => exact List.mem_append
    | succ n ih =>
        cases xs with
        | nil => simp [qmergeFuel]
        | cons a xs =>
            cases ys with
            | nil => simp [qmergeFuel]
            | cons b ys =>
                change x ∈ (if qcellLE a b then a :: qmergeFuel n xs (b :: ys) else b :: qmergeFuel n (a :: xs) ys) ↔ _
                split_ifs <;> simp only [List.mem_cons,ih] <;> tauto
def qmerge (xs ys : List qCell) : List qCell := qmergeFuel (xs.length + ys.length) xs ys
def qmerge_mem (x : qCell) (xs ys : List qCell) : x ∈ qmerge xs ys ↔ x ∈ xs ∨ x ∈ ys :=
  qmergeFuel_mem x _ _ _
def qsortFuel (n : ℕ) : List qCell → List qCell :=
  Nat.rec id (fun _ rec xs => match xs with
    | [] => []
    | [a] => [a]
    | a :: b :: xs =>
        qmerge (rec ((a :: b :: xs).take ((xs.length + 3) / 2)))
          (rec ((a :: b :: xs).drop ((xs.length + 3) / 2)))) n
def qsortFuel_mem (x : qCell) (n : ℕ) (xs : List qCell) :
    x ∈ qsortFuel n xs ↔ x ∈ xs := by
  set_option maxRecDepth 100000 in
    induction n generalizing xs with
    | zero => rfl
    | succ n ih =>
        cases xs with
        | nil => rfl
        | cons a xs =>
            cases xs with
            | nil => rfl
            | cons b xs =>
                change x ∈ qmerge (qsortFuel n ((a :: b :: xs).take ((xs.length + 3) / 2)))
                  (qsortFuel n ((a :: b :: xs).drop ((xs.length + 3) / 2))) ↔ _
                simp only [qmerge_mem,ih]
                rw [← List.mem_append,List.take_append_drop]
def qsort (xs : List qCell) : List qCell := qsortFuel xs.length xs
def qsort_mem (x : qCell) (xs : List qCell) : x ∈ qsort xs ↔ x ∈ xs :=
  qsortFuel_mem x xs.length xs
def qcanonical (xs : List qCell) : List qCell := qcompact (qsort xs)
def qcanonical_mem (x : qCell) (xs : List qCell) : x ∈ qcanonical xs ↔ x ∈ xs := by
  set_option maxRecDepth 100000 in
    simp only [qcanonical,qcompact_mem,qsort_mem]
def qcanonical_toFinset (xs : List qCell) : (qcanonical xs).toFinset = xs.toFinset := by
  set_option maxRecDepth 100000 in
    ext x
    simp only [List.mem_toFinset,qcanonical_mem]
def qrowH_list (xs : List qCell) (h : xs.Nodup) :
    (Finset.mk (xs : Multiset qCell) (Multiset.coe_nodup.mpr h) : Finset qCell) = xs.toFinset := by
  set_option maxRecDepth 100000 in
    exact List.toFinset_eq (Multiset.coe_nodup.mpr h)
def qlist_image (xs : List qCell) (f : qCell → qCell) :
    xs.toFinset.image f = (xs.map f).toFinset := by
  set_option maxRecDepth 100000 in
    ext x
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
def qlist_unionH (ds : List qR) (ls : List (List qCell))
    (h : ds.map qR.H = ls.map List.toFinset) :
    qunionH ds = ls.flatten.toFinset := by
  set_option maxRecDepth 100000 in
    unfold qunionH
    rw [h]
    clear h ds
    induction ls with
    | nil => simp
    | cons x xs ih => simpa only [List.map_cons,List.foldr_cons,List.flatten_cons,List.toFinset_append] using congrArg (x.toFinset ∪ ·) ih
def qlist_H_target (xs ys : List qCell) (h : qcanonical xs = ys) :
    xs.toFinset = ys.toFinset := by
  set_option maxRecDepth 100000 in
    rw [← qcanonical_toFinset xs,h]
def spUnionToFinset {s t : Finset qCell} {xs ys : List qCell}
    (hs : s = xs.toFinset) (ht : t = ys.toFinset) :
    s ∪ t = (xs ++ ys).toFinset := by
  set_option maxRecDepth 100000 in
    rw [hs,ht,List.toFinset_append]
def spPlacedH_list (t : qT) (d : qR) (xs : List qCell)
    (hd : d.H = xs.toFinset) :
    (qplaceRow t d).H = (xs.map (qplacement t.rotation t.shift)).toFinset := by
  set_option maxRecDepth 100000 in
    change d.H.image (qplacement t.rotation t.shift) = _
    rw [hd,qlist_image]
def spPlacedH_mem (t : qT) (d : qR) (xs : List qCell)
    (hd : d.H = xs.toFinset) (b : qCell) :
    b ∈ (qplaceRow t d).H ↔ b ∈ xs.map (qplacement t.rotation t.shift) := by
  set_option maxRecDepth 100000 in
    change b ∈ d.H.image (qplacement t.rotation t.shift) ↔ _
    rw [hd,qlist_image]
    exact List.mem_toFinset
def qfoldInter_le (ds : List qR) (S : Finset qCell) : (ds.map qR.H).foldr (· ∩ ·) S ⊆ S := by
  set_option maxRecDepth 100000 in
    induction ds with
    | nil => exact Finset.Subset.refl S
    | cons d ds ih => exact Finset.Subset.trans Finset.inter_subset_right ih
def qfoldInter_member (ds : List qR) (S : Finset qCell) (d : qR) (hd : d ∈ ds) :
    (ds.map qR.H).foldr (· ∩ ·) S ⊆ d.H := by
  set_option maxRecDepth 100000 in
    induction ds with
    | nil => cases hd
    | cons x xs ih =>
        simp only [List.mem_cons] at hd
        rcases hd with h | h
        · subst x
          exact Finset.inter_subset_left
        · exact Finset.Subset.trans Finset.inter_subset_right (ih h)
def qcommonH_le (d : qR) (ds : List qR) : d ∈ ds → qcommonH ds ⊆ d.H := by
  set_option maxRecDepth 100000 in
    intro hd
    cases ds with
    | nil => cases hd
    | cons e ds =>
        change (ds.map qR.H).foldr (· ∩ ·) e.H ⊆ d.H
        simp only [List.mem_cons] at hd
        rcases hd with h | h
        · subst e
          exact qfoldInter_le ds _
        · exact qfoldInter_member ds e.H d h
def qcommonH_le_at (ds : List qR) (i : ℕ) (d : qR) (h : ds[i]? = some d) : qcommonH ds ⊆ d.H := by
  set_option maxRecDepth 100000 in
    apply qcommonH_le d ds
    exact List.mem_of_getElem? h
def erase_union_eq_of_subset {α : Type*} [DecidableEq α]
    (s t u : Finset α) (o : α)
    (hs : s ⊆ insert o u) (ht : t ⊆ insert o u)
    (hu : u ⊆ s ∪ t) (ho : o ∉ u) :
    (s ∪ t).erase o = u := by
  set_option maxRecDepth 100000 in
    ext x
    constructor
    · intro hx
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hx
      have hbound := (Finset.mem_union.mp hmem).elim (fun h => hs h) (fun h => ht h)
      exact (Finset.mem_insert.mp hbound).resolve_left hne
    · intro hx
      have hne : x ≠ o := by
        intro he
        subst x
        exact ho hx
      exact Finset.mem_erase.mpr ⟨hne, hu hx⟩
def erase_union_eq_of_left_subset {α : Type*} [DecidableEq α]
    (s t u : Finset α) (o : α)
    (hs : s ⊆ insert o u) (ht : t ⊆ insert o u)
    (hu : u ⊆ s) (ho : o ∉ u) :
    (s ∪ t).erase o = u := by
  set_option maxRecDepth 100000 in
    apply erase_union_eq_of_subset s t u o hs ht
    · exact fun _ hx => Finset.mem_union_left t (hu hx)
    · exact ho
def spRawH503B0 : List qCell := [(-1,-5), (-1,-4), (-1,-3), (-1,-1), (-1,0), (-1,1), (-1,2), (-1,3), (0,-4), (0,-3), (0,-2), (0,-1), (0,0), (0,1), (0,2), (1,-2), (1,0), (1,1), (1,2), (2,-3), (2,-2), (2,-1), (2,0), (2,1), (2,2), (2,3), (2,4), (3,-4), (3,-3), (3,-2), (3,-1), (3,0), (3,1), (3,2), (3,3), (3,4), (4,-5), (4,-4), (4,-3), (4,-2), (4,-1), (4,0), (4,1), (4,2), (4,3), (4,4), (5,-2), (5,-1), (5,0), (5,1), (5,2), (6,-1), (6,0), (6,1), (6,2), (7,-1), (7,0), (7,1), (7,2)]
def spRawH503 : List qCell := spRawH503B0
def spRawH503_eq : qm503.H = spRawH503.toFinset := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      change (spRawH503B0.toFinset) = spRawH503.toFinset
      simp only [spRawH503,List.toFinset_append,Finset.union_assoc])))
def spRawH592B0 : List qCell := [(-7,5), (-7,6), (-7,8), (-6,3), (-6,5), (-6,6), (-6,7), (-6,8), (-5,1), (-5,2), (-5,3), (-5,4), (-5,5), (-5,6), (-5,7), (-5,8), (-5,9), (-5,10), (-5,11), (-4,1), (-4,2), (-4,3), (-4,4), (-4,5), (-4,6)]
def spRawH592B1 : List qCell := [(-4,7), (-4,8), (-4,9), (-4,10), (-3,1), (-3,2), (-3,3), (-3,4), (-3,5), (-3,6), (-3,7), (-3,8), (-3,9), (-3,10), (-3,11), (-3,12), (-3,13), (-2,-6), (-2,-5), (-2,-4), (-2,0), (-2,1), (-2,2), (-2,3), (-2,4)]
def spRawH592B2 : List qCell := [(-2,5), (-2,6), (-2,7), (-2,8), (-2,9), (-2,10), (-2,11), (-2,12), (-1,-5), (-1,-4), (-1,-3), (-1,-2), (-1,-1), (-1,0), (-1,1), (-1,2), (-1,3), (-1,4), (-1,5), (-1,6), (-1,7), (-1,8), (-1,9), (-1,10), (-1,11)]
def spRawH592B3 : List qCell := [(-1,12), (-1,13), (0,-6), (0,-5), (0,-4), (0,-1), (0,0), (0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (0,8), (0,9), (0,10), (0,11), (1,-4), (1,-3), (1,-2), (1,-1), (1,0), (1,1), (1,2)]
def spRawH592B4 : List qCell := [(1,3), (1,4), (1,5), (1,6), (1,7), (1,8), (1,9), (1,10), (1,11), (2,-5), (2,-4), (2,-3), (2,-2), (2,-1), (2,0), (2,1), (2,2), (2,3), (2,4), (2,5), (2,6), (2,7), (2,8), (2,9), (2,10)]
def spRawH592B5 : List qCell := [(2,11), (3,-4), (3,-3), (3,-2), (3,-1), (3,0), (3,1), (3,2), (3,3), (3,4), (3,5), (3,6), (3,7), (3,8), (3,9), (3,10), (3,11), (4,-5), (4,-4), (4,-3), (4,-2), (4,-1), (4,0), (4,1), (4,2)]
def spRawH592B6 : List qCell := [(4,3), (4,4), (4,5), (4,6), (4,7), (4,8), (4,9), (5,-3), (5,-2), (5,-1), (5,0), (5,1), (5,2), (5,3), (5,4), (5,5), (5,6), (5,7), (5,8), (6,-3), (6,-2), (6,-1), (6,0), (6,1), (6,2)]
def spRawH592B7 : List qCell := [(6,3), (6,4), (6,5), (6,6), (6,7), (6,8), (7,-3), (7,-2), (7,-1), (7,0), (7,1), (7,2), (7,3), (7,4), (7,5), (7,6), (7,7), (8,0), (8,1), (8,2), (8,3), (8,4), (8,5), (8,6), (9,0)]
def spRawH592B8 : List qCell := [(9,1), (9,2), (9,3), (9,4), (9,5), (9,6), (10,0), (10,1), (10,2), (11,0), (11,2)]
def spRawH592 : List qCell := spRawH592B0 ++ spRawH592B1 ++ spRawH592B2 ++ spRawH592B3 ++ spRawH592B4 ++ spRawH592B5 ++ spRawH592B6 ++ spRawH592B7 ++ spRawH592B8
def spRawH592_eq : qm592.H = spRawH592.toFinset := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      let l0 : List qCell := [(-7,5),(-7,6),(-7,8),(-6,3),(-6,5),(-6,6),(-6,7),(-6,8),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-5,8),(-5,9),(-5,10),(-5,11),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6)]
      have hc0 : qf214 = l0.toFinset := by rfl
      let l1 : List qCell := [(-4,7),(-4,8),(-4,9),(-4,10),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-3,10),(-3,11),(-3,12),(-3,13),(-2,-6),(-2,-5),(-2,-4),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4)]
      have hc1 : qf215 = l1.toFinset := by rfl
      let l2 : List qCell := [(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-2,11),(-2,12),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(-1,11)]
      have hc2 : qf216 = l2.toFinset := by rfl
      let l3 : List qCell := [(-1,12),(-1,13),(0,-6),(0,-5),(0,-4),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2)]
      have hc3 : qf217 = l3.toFinset := by rfl
      let l4 : List qCell := [(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10)]
      have hc4 : qf218 = l4.toFinset := by rfl
      let l5 : List qCell := [(2,11),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2)]
      have hc5 : qf219 = l5.toFinset := by rfl
      let l6 : List qCell := [(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2)]
      have hc6 : qf220 = l6.toFinset := by rfl
      let l7 : List qCell := [(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(9,0)]
      have hc7 : qf221 = l7.toFinset := by rfl
      let l8 : List qCell := [(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(10,0),(10,1),(10,2),(11,0),(11,2)]
      have hc8 : qf222 = l8.toFinset := by rfl
      have hu1 := spUnionToFinset hc0 hc1
      have hu2 := spUnionToFinset hu1 hc2
      have hu3 := spUnionToFinset hu2 hc3
      have hu4 := spUnionToFinset hu3 hc4
      have hu5 := spUnionToFinset hu4 hc5
      have hu6 := spUnionToFinset hu5 hc6
      have hu7 := spUnionToFinset hu6 hc7
      have hu8 := spUnionToFinset hu7 hc8
      have hl : (((((((((l0 ++ l1) ++ l2) ++ l3) ++ l4) ++ l5) ++ l6) ++ l7) ++ l8) : List qCell) = spRawH592 := by
        simp only [List.append_assoc]
        rfl
      change (qf214 ∪ qf215 ∪ qf216 ∪ qf217 ∪ qf218 ∪ qf219 ∪ qf220 ∪ qf221 ∪ qf222) = spRawH592.toFinset
      exact hu8.trans (congrArg List.toFinset hl))))
def spRawH607B0 : List qCell := [(-7,-1), (-7,0), (-7,1), (-7,2), (-6,-1), (-6,0), (-6,1), (-6,2), (-6,6), (-6,7), (-6,9), (-5,-2), (-5,-1), (-5,0), (-5,1), (-5,2), (-5,4), (-5,6), (-5,7), (-5,8), (-5,9), (-4,-5), (-4,-4), (-4,-3), (-4,-2)]
def spRawH607B1 : List qCell := [(-4,-1), (-4,0), (-4,1), (-4,2), (-4,3), (-4,4), (-4,5), (-4,6), (-4,7), (-4,8), (-4,9), (-4,10), (-4,11), (-4,12), (-3,-4), (-3,-3), (-3,-2), (-3,-1), (-3,0), (-3,1), (-3,2), (-3,3), (-3,4), (-3,5), (-3,6)]
def spRawH607B2 : List qCell := [(-3,7), (-3,8), (-3,9), (-3,10), (-3,11), (-2,-3), (-2,-2), (-2,-1), (-2,0), (-2,1), (-2,2), (-2,3), (-2,4), (-2,5), (-2,6), (-2,7), (-2,8), (-2,9), (-2,10), (-2,11), (-2,12), (-2,13), (-2,14), (-1,-2), (-1,0)]
def spRawH607B3 : List qCell := [(-1,1), (-1,2), (-1,3), (-1,4), (-1,5), (-1,6), (-1,7), (-1,8), (-1,9), (-1,10), (-1,11), (-1,12), (-1,13), (0,-3), (0,-2), (0,-1), (0,0), (0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (0,8)]
def spRawH607B4 : List qCell := [(0,9), (0,10), (0,11), (0,12), (0,13), (0,14), (1,-4), (1,-3), (1,-1), (1,0), (1,1), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (1,8), (1,9), (1,10), (1,11), (1,12), (2,-6), (2,-5), (2,-4)]
def spRawH607B5 : List qCell := [(2,-3), (2,-2), (2,-1), (2,0), (2,1), (2,2), (2,3), (2,4), (2,5), (2,6), (2,7), (2,8), (2,9), (2,10), (2,11), (2,12), (3,-6), (3,-5), (3,-4), (3,-3), (3,-2), (3,-1), (3,0), (3,1), (3,2)]
def spRawH607B6 : List qCell := [(3,3), (3,4), (3,5), (3,6), (3,7), (3,8), (3,9), (3,10), (3,11), (3,12), (4,-7), (4,-6), (4,-5), (4,-4), (4,-3), (4,-2), (4,-1), (4,0), (4,1), (4,2), (4,3), (4,4), (4,5), (4,6), (4,7)]
def spRawH607B7 : List qCell := [(4,8), (4,9), (4,10), (4,11), (4,12), (5,-8), (5,-7), (5,-6), (5,-5), (5,-4), (5,-3), (5,-2), (5,-1), (5,0), (5,1), (5,2), (5,3), (5,4), (5,5), (5,6), (5,7), (5,8), (5,9), (5,10), (6,-7)]
def spRawH607B8 : List qCell := [(6,-6), (6,-5), (6,-4), (6,-3), (6,-2), (6,-1), (6,0), (6,1), (6,2), (6,3), (6,4), (6,5), (6,6), (6,7), (6,8), (6,9), (7,-8), (7,-7), (7,-6), (7,-5), (7,-4), (7,-3), (7,-2), (7,-1), (7,0)]
def spRawH607B9 : List qCell := [(7,1), (7,2), (7,3), (7,4), (7,5), (7,6), (7,7), (7,8), (7,9), (8,-6), (8,-5), (8,-4), (8,-3), (8,-2), (8,-1), (8,0), (8,1), (8,2), (8,3), (8,4), (8,5), (8,6), (8,7), (8,8), (9,-6)]
def spRawH607B10 : List qCell := [(9,-5), (9,-4), (9,-3), (9,-2), (9,-1), (9,0), (9,1), (9,2), (9,3), (9,4), (9,5), (9,6), (9,7), (10,-6), (10,-5), (10,-4), (10,-3), (10,-2), (10,-1), (10,0), (10,1), (10,2), (10,3), (10,4), (10,5)]
def spRawH607B11 : List qCell := [(10,6), (10,7), (11,-5), (11,-4), (11,-3), (11,-2), (11,-1), (11,0), (11,1), (11,2), (11,3), (12,-4), (12,-3), (12,-2), (12,-1), (12,0), (12,1), (12,3), (13,-4), (13,-3), (13,-2), (13,-1), (13,0), (13,1)]
def spRawH607 : List qCell := spRawH607B0 ++ spRawH607B1 ++ spRawH607B2 ++ spRawH607B3 ++ spRawH607B4 ++ spRawH607B5 ++ spRawH607B6 ++ spRawH607B7 ++ spRawH607B8 ++ spRawH607B9 ++ spRawH607B10 ++ spRawH607B11
def spRawH607_eq : qm607.H = spRawH607.toFinset := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      let l0 : List qCell := [(-7,-1),(-7,0),(-7,1),(-7,2),(-6,-1),(-6,0),(-6,1),(-6,2),(-6,6),(-6,7),(-6,9),(-5,-2),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,4),(-5,6),(-5,7),(-5,8),(-5,9),(-4,-5),(-4,-4),(-4,-3),(-4,-2)]
      have hc0 : qf371 = l0.toFinset := by rfl
      let l1 : List qCell := [(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-4,8),(-4,9),(-4,10),(-4,11),(-4,12),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6)]
      have hc1 : qf372 = l1.toFinset := by rfl
      let l2 : List qCell := [(-3,7),(-3,8),(-3,9),(-3,10),(-3,11),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-2,11),(-2,12),(-2,13),(-2,14),(-1,-2),(-1,0)]
      have hc2 : qf373 = l2.toFinset := by rfl
      let l3 : List qCell := [(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(-1,11),(-1,12),(-1,13),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8)]
      have hc3 : qf374 = l3.toFinset := by rfl
      let l4 : List qCell := [(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(1,-4),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(1,12),(2,-6),(2,-5),(2,-4)]
      have hc4 : qf375 = l4.toFinset := by rfl
      let l5 : List qCell := [(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(2,12),(3,-6),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2)]
      have hc5 : qf376 = l5.toFinset := by rfl
      let l6 : List qCell := [(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(3,12),(4,-7),(4,-6),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7)]
      have hc6 : qf377 = l6.toFinset := by rfl
      let l7 : List qCell := [(4,8),(4,9),(4,10),(4,11),(4,12),(5,-8),(5,-7),(5,-6),(5,-5),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(6,-7)]
      have hc7 : qf378 = l7.toFinset := by rfl
      let l8 : List qCell := [(6,-6),(6,-5),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(6,9),(7,-8),(7,-7),(7,-6),(7,-5),(7,-4),(7,-3),(7,-2),(7,-1),(7,0)]
      have hc8 : qf379 = l8.toFinset := by rfl
      let l9 : List qCell := [(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(7,8),(7,9),(8,-6),(8,-5),(8,-4),(8,-3),(8,-2),(8,-1),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(8,7),(8,8),(9,-6)]
      have hc9 : qf380 = l9.toFinset := by rfl
      let l10 : List qCell := [(9,-5),(9,-4),(9,-3),(9,-2),(9,-1),(9,0),(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(9,7),(10,-6),(10,-5),(10,-4),(10,-3),(10,-2),(10,-1),(10,0),(10,1),(10,2),(10,3),(10,4),(10,5)]
      have hc10 : qf381 = l10.toFinset := by rfl
      let l11 : List qCell := [(10,6),(10,7),(11,-5),(11,-4),(11,-3),(11,-2),(11,-1),(11,0),(11,1),(11,2),(11,3),(12,-4),(12,-3),(12,-2),(12,-1),(12,0),(12,1),(12,3),(13,-4),(13,-3),(13,-2),(13,-1),(13,0),(13,1)]
      have hc11 : qf382 = l11.toFinset := by rfl
      have hu1 := spUnionToFinset hc0 hc1
      have hu2 := spUnionToFinset hu1 hc2
      have hu3 := spUnionToFinset hu2 hc3
      have hu4 := spUnionToFinset hu3 hc4
      have hu5 := spUnionToFinset hu4 hc5
      have hu6 := spUnionToFinset hu5 hc6
      have hu7 := spUnionToFinset hu6 hc7
      have hu8 := spUnionToFinset hu7 hc8
      have hu9 := spUnionToFinset hu8 hc9
      have hu10 := spUnionToFinset hu9 hc10
      have hu11 := spUnionToFinset hu10 hc11
      have hl : ((((((((((((l0 ++ l1) ++ l2) ++ l3) ++ l4) ++ l5) ++ l6) ++ l7) ++ l8) ++ l9) ++ l10) ++ l11) : List qCell) = spRawH607 := by
        simp only [List.append_assoc]
        rfl
      change (qf371 ∪ qf372 ∪ qf373 ∪ qf374 ∪ qf375 ∪ qf376 ∪ qf377 ∪ qf378 ∪ qf379 ∪ qf380 ∪ qf381 ∪ qf382) = spRawH607.toFinset
      exact hu11.trans (congrArg List.toFinset hl))))
def spRawH612B0 : List qCell := [(-17,0), (-17,2), (-16,0), (-16,1), (-16,2), (-15,-4), (-15,-3), (-15,-2), (-15,-1), (-15,0), (-15,1), (-15,2), (-15,4), (-14,-4), (-14,-3), (-14,-2), (-14,-1), (-14,0), (-14,1), (-14,2), (-14,3), (-14,4), (-13,-5), (-13,-4), (-13,-3), (-13,-2), (-13,-1), (-13,0), (-13,1), (-13,2), (-13,3), (-13,4), (-12,-7), (-12,-6), (-12,-5), (-12,-4), (-12,-3), (-12,-2), (-12,-1), (-12,0), (-12,1), (-12,2), (-12,3), (-12,4), (-12,5), (-12,6), (-11,-8), (-11,-7), (-11,-6), (-11,-5), (-11,-4), (-11,-3), (-11,-2), (-11,-1), (-11,0), (-11,1), (-11,2), (-11,3), (-11,4), (-11,5), (-10,-10), (-10,-9), (-10,-8), (-10,-7), (-10,-6), (-10,-5), (-10,-4), (-10,-3), (-10,-2), (-10,-1), (-10,0), (-10,1), (-10,2), (-10,3), (-10,4), (-10,5), (-10,6), (-9,-10), (-9,-9), (-9,-8), (-9,-7), (-9,-6), (-9,-5), (-9,-4), (-9,-3), (-9,-2), (-9,-1), (-9,0), (-9,1), (-9,2), (-9,3), (-9,4), (-9,5), (-9,6), (-8,-10), (-8,-9), (-8,-8), (-8,-7), (-8,-6), (-8,-5)]
def spRawH612B1 : List qCell := [(-8,-4), (-8,-3), (-8,-2), (-8,-1), (-8,0), (-8,1), (-8,2), (-8,3), (-8,4), (-7,-10), (-7,-9), (-7,-8), (-7,-7), (-7,-6), (-7,-5), (-7,-4), (-7,-3), (-7,-2), (-7,-1), (-7,0), (-7,1), (-7,2), (-7,3), (-7,4), (-7,5), (-6,-12), (-6,-11), (-6,-10), (-6,-9), (-6,-8), (-6,-7), (-6,-6), (-6,-5), (-6,-4), (-6,-3), (-6,-2), (-6,-1), (-6,0), (-6,1), (-6,2), (-6,3), (-6,4), (-5,-11), (-5,-10), (-5,-9), (-5,-8), (-5,-7), (-5,-6), (-5,-5), (-5,-4), (-5,-3), (-5,-2), (-5,-1), (-5,0), (-5,1), (-5,2), (-5,3), (-5,4), (-4,-12), (-4,-11), (-4,-10), (-4,-9), (-4,-8), (-4,-7), (-4,-6), (-4,-5), (-4,-4), (-4,-3), (-4,-2), (-4,-1), (-4,0), (-4,1), (-4,3), (-4,5), (-3,-8), (-3,-7), (-3,-6), (-3,-5), (-3,-4), (-3,-3), (-3,-2), (-3,-1), (-3,0), (-3,2), (-3,3), (-3,4), (-3,5), (-2,-8), (-2,-7), (-2,-6), (-2,-5), (-2,-4), (-2,-3), (-2,-2), (-2,0), (-2,2), (-2,3), (-2,4), (-2,5), (-2,6)]
def spRawH612B2 : List qCell := [(-2,7), (-2,8), (-1,-8), (-1,-7), (-1,-6), (-1,-5), (-1,-4), (-1,-3), (-1,-2), (-1,0), (-1,2), (-1,3), (-1,4), (-1,5), (-1,6), (-1,7), (-1,8), (0,-5), (0,-4), (0,-3), (0,-2), (0,0), (0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (0,8), (1,-5), (1,-3), (1,-1), (1,0), (1,1), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (1,8), (1,9), (1,10), (1,11), (1,12), (2,-4), (2,-3), (2,-2), (2,-1), (2,0), (2,1), (2,2), (2,3), (2,4), (2,5), (2,6), (2,7), (2,8), (2,9), (2,10), (2,11), (3,-4), (3,-3), (3,-2), (3,-1), (3,0), (3,1), (3,2), (3,3), (3,4), (3,5), (3,6), (3,7), (3,8), (3,9), (3,10), (3,11), (3,12), (4,-5), (4,-4), (4,-3), (4,-2), (4,-1), (4,0), (4,1), (4,2), (4,3), (4,4), (4,5), (4,6), (4,7), (4,8), (4,9), (4,10), (5,-4), (5,-3), (5,-2), (5,-1), (5,0)]
def spRawH612B3 : List qCell := [(5,1), (5,2), (5,3), (5,4), (5,5), (5,6), (5,7), (5,8), (5,9), (5,10), (6,-6), (6,-5), (6,-4), (6,-3), (6,-2), (6,-1), (6,0), (6,1), (6,2), (6,3), (6,4), (6,5), (6,6), (6,7), (6,8), (6,9), (6,10), (7,-6), (7,-5), (7,-4), (7,-3), (7,-2), (7,-1), (7,0), (7,1), (7,2), (7,3), (7,4), (7,5), (7,6), (7,7), (7,8), (7,9), (7,10), (8,-5), (8,-4), (8,-3), (8,-2), (8,-1), (8,0), (8,1), (8,2), (8,3), (8,4), (8,5), (8,6), (8,7), (8,8), (9,-6), (9,-5), (9,-4), (9,-3), (9,-2), (9,-1), (9,0), (9,1), (9,2), (9,3), (9,4), (9,5), (9,6), (9,7), (10,-4), (10,-3), (10,-2), (10,-1), (10,0), (10,1), (10,2), (10,3), (10,4), (10,5), (11,-4), (11,-3), (11,-2), (11,-1), (11,0), (11,1), (11,2), (11,3), (11,4), (12,-4), (12,-2), (12,-1), (12,0), (12,1), (12,2), (12,3), (12,4), (13,-2)]
def spRawH612B4 : List qCell := [(13,-1), (13,0), (14,-2), (14,0)]
def spRawH612 : List qCell := spRawH612B0 ++ spRawH612B1 ++ spRawH612B2 ++ spRawH612B3 ++ spRawH612B4
def spRawH612_eq : qm612.H = spRawH612.toFinset := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      let l0 : List qCell := [(-17,0),(-17,2),(-16,0),(-16,1),(-16,2),(-15,-4),(-15,-3),(-15,-2),(-15,-1),(-15,0),(-15,1),(-15,2),(-15,4),(-14,-4),(-14,-3),(-14,-2),(-14,-1),(-14,0),(-14,1),(-14,2),(-14,3),(-14,4),(-13,-5),(-13,-4),(-13,-3)]
      have hc0 : qf443 = l0.toFinset := by rfl
      let l1 : List qCell := [(-13,-2),(-13,-1),(-13,0),(-13,1),(-13,2),(-13,3),(-13,4),(-12,-7),(-12,-6),(-12,-5),(-12,-4),(-12,-3),(-12,-2),(-12,-1),(-12,0),(-12,1),(-12,2),(-12,3),(-12,4),(-12,5),(-12,6),(-11,-8),(-11,-7),(-11,-6),(-11,-5)]
      have hc1 : qf444 = l1.toFinset := by rfl
      let l2 : List qCell := [(-11,-4),(-11,-3),(-11,-2),(-11,-1),(-11,0),(-11,1),(-11,2),(-11,3),(-11,4),(-11,5),(-10,-10),(-10,-9),(-10,-8),(-10,-7),(-10,-6),(-10,-5),(-10,-4),(-10,-3),(-10,-2),(-10,-1),(-10,0),(-10,1),(-10,2),(-10,3),(-10,4)]
      have hc2 : qf445 = l2.toFinset := by rfl
      let l3 : List qCell := [(-10,5),(-10,6),(-9,-10),(-9,-9),(-9,-8),(-9,-7),(-9,-6),(-9,-5),(-9,-4),(-9,-3),(-9,-2),(-9,-1),(-9,0),(-9,1),(-9,2),(-9,3),(-9,4),(-9,5),(-9,6),(-8,-10),(-8,-9),(-8,-8),(-8,-7),(-8,-6),(-8,-5)]
      have hc3 : qf446 = l3.toFinset := by rfl
      let l4 : List qCell := [(-8,-4),(-8,-3),(-8,-2),(-8,-1),(-8,0),(-8,1),(-8,2),(-8,3),(-8,4),(-7,-10),(-7,-9),(-7,-8),(-7,-7),(-7,-6),(-7,-5),(-7,-4),(-7,-3),(-7,-2),(-7,-1),(-7,0),(-7,1),(-7,2),(-7,3),(-7,4),(-7,5)]
      have hc4 : qf447 = l4.toFinset := by rfl
      let l5 : List qCell := [(-6,-12),(-6,-11),(-6,-10),(-6,-9),(-6,-8),(-6,-7),(-6,-6),(-6,-5),(-6,-4),(-6,-3),(-6,-2),(-6,-1),(-6,0),(-6,1),(-6,2),(-6,3),(-6,4),(-5,-11),(-5,-10),(-5,-9),(-5,-8),(-5,-7),(-5,-6),(-5,-5),(-5,-4)]
      have hc5 : qf448 = l5.toFinset := by rfl
      let l6 : List qCell := [(-5,-3),(-5,-2),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-4,-12),(-4,-11),(-4,-10),(-4,-9),(-4,-8),(-4,-7),(-4,-6),(-4,-5),(-4,-4),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,3),(-4,5),(-3,-8)]
      have hc6 : qf449 = l6.toFinset := by rfl
      let l7 : List qCell := [(-3,-7),(-3,-6),(-3,-5),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,2),(-3,3),(-3,4),(-3,5),(-2,-8),(-2,-7),(-2,-6),(-2,-5),(-2,-4),(-2,-3),(-2,-2),(-2,0),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6)]
      have hc7 : qf450 = l7.toFinset := by rfl
      let l8 : List qCell := [(-2,7),(-2,8),(-1,-8),(-1,-7),(-1,-6),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,0),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(0,-5),(0,-4),(0,-3),(0,-2),(0,0),(0,1),(0,2),(0,3)]
      have hc8 : qf451 = l8.toFinset := by rfl
      let l9 : List qCell := [(0,4),(0,5),(0,6),(0,7),(0,8),(1,-5),(1,-3),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(1,12),(2,-4),(2,-3),(2,-2),(2,-1)]
      have hc9 : qf452 = l9.toFinset := by rfl
      let l10 : List qCell := [(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8)]
      have hc10 : qf453 = l10.toFinset := by rfl
      let l11 : List qCell := [(3,9),(3,10),(3,11),(3,12),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(4,10),(5,-4),(5,-3),(5,-2),(5,-1),(5,0)]
      have hc11 : qf454 = l11.toFinset := by rfl
      let l12 : List qCell := [(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(6,-6),(6,-5),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8)]
      have hc12 : qf455 = l12.toFinset := by rfl
      let l13 : List qCell := [(6,9),(6,10),(7,-6),(7,-5),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(7,8),(7,9),(7,10),(8,-5),(8,-4),(8,-3),(8,-2),(8,-1),(8,0)]
      have hc13 : qf456 = l13.toFinset := by rfl
      let l14 : List qCell := [(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(8,7),(8,8),(9,-6),(9,-5),(9,-4),(9,-3),(9,-2),(9,-1),(9,0),(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(9,7),(10,-4),(10,-3),(10,-2)]
      have hc14 : qf457 = l14.toFinset := by rfl
      let l15 : List qCell := [(10,-1),(10,0),(10,1),(10,2),(10,3),(10,4),(10,5),(11,-4),(11,-3),(11,-2),(11,-1),(11,0),(11,1),(11,2),(11,3),(11,4),(12,-4),(12,-2),(12,-1),(12,0),(12,1),(12,2),(12,3),(12,4),(13,-2)]
      have hc15 : qf458 = l15.toFinset := by rfl
      let l16 : List qCell := [(13,-1),(13,0),(14,-2),(14,0)]
      have hc16 : qf459 = l16.toFinset := by rfl
      have hu1 := spUnionToFinset hc0 hc1
      have hu2 := spUnionToFinset hu1 hc2
      have hu3 := spUnionToFinset hu2 hc3
      have hu4 := spUnionToFinset hu3 hc4
      have hu5 := spUnionToFinset hu4 hc5
      have hu6 := spUnionToFinset hu5 hc6
      have hu7 := spUnionToFinset hu6 hc7
      have hu8 := spUnionToFinset hu7 hc8
      have hu9 := spUnionToFinset hu8 hc9
      have hu10 := spUnionToFinset hu9 hc10
      have hu11 := spUnionToFinset hu10 hc11
      have hu12 := spUnionToFinset hu11 hc12
      have hu13 := spUnionToFinset hu12 hc13
      have hu14 := spUnionToFinset hu13 hc14
      have hu15 := spUnionToFinset hu14 hc15
      have hu16 := spUnionToFinset hu15 hc16
      have hl : (((((((((((((((((l0 ++ l1) ++ l2) ++ l3) ++ l4) ++ l5) ++ l6) ++ l7) ++ l8) ++ l9) ++ l10) ++ l11) ++ l12) ++ l13) ++ l14) ++ l15) ++ l16) : List qCell) = spRawH612 := by
        simp only [List.append_assoc]
        rfl
      change (qf443 ∪ qf444 ∪ qf445 ∪ qf446 ∪ qf447 ∪ qf448 ∪ qf449 ∪ qf450 ∪ qf451 ∪ qf452 ∪ qf453 ∪ qf454 ∪ qf455 ∪ qf456 ∪ qf457 ∪ qf458 ∪ qf459) = spRawH612.toFinset
      exact hu16.trans (congrArg List.toFinset hl))))
def spRawH613B0 : List qCell := [(-17,-2), (-17,0), (-17,2), (-16,-2), (-16,-1), (-16,0), (-16,1), (-16,2), (-15,-4), (-15,-3), (-15,-2), (-15,-1), (-15,0), (-15,1), (-15,2), (-15,3), (-15,4), (-14,-4), (-14,-3), (-14,-2), (-14,-1), (-14,0), (-14,1), (-14,2), (-14,3), (-14,4), (-13,-5), (-13,-4), (-13,-3), (-13,-2), (-13,-1), (-13,0), (-13,1), (-13,2), (-13,3), (-13,4), (-13,5), (-12,-7), (-12,-6), (-12,-5), (-12,-4), (-12,-3), (-12,-2), (-12,-1), (-12,0), (-12,1), (-12,2), (-12,3), (-12,4), (-12,5), (-12,6), (-12,7), (-11,-8), (-11,-7), (-11,-6), (-11,-5), (-11,-4), (-11,-3), (-11,-2), (-11,-1), (-11,0), (-11,1), (-11,2), (-11,3), (-11,4), (-11,5), (-11,6), (-11,7), (-11,8), (-10,-10), (-10,-9), (-10,-8), (-10,-7), (-10,-6), (-10,-5), (-10,-4), (-10,-3), (-10,-2), (-10,-1), (-10,0), (-10,1), (-10,2), (-10,3), (-10,4), (-10,5), (-10,6), (-10,7), (-10,8), (-10,9), (-10,10), (-9,-10), (-9,-9), (-9,-8), (-9,-7), (-9,-6), (-9,-5), (-9,-4), (-9,-3), (-9,-2), (-9,-1)]
def spRawH613B1 : List qCell := [(-9,0), (-9,1), (-9,2), (-9,3), (-9,4), (-9,5), (-9,6), (-9,7), (-9,8), (-9,9), (-9,10), (-8,-10), (-8,-9), (-8,-8), (-8,-7), (-8,-6), (-8,-5), (-8,-4), (-8,-3), (-8,-2), (-8,-1), (-8,0), (-8,1), (-8,2), (-8,3), (-8,4), (-8,5), (-8,6), (-8,7), (-8,8), (-8,9), (-8,10), (-7,-10), (-7,-9), (-7,-8), (-7,-7), (-7,-6), (-7,-5), (-7,-4), (-7,-3), (-7,-2), (-7,-1), (-7,0), (-7,1), (-7,2), (-7,3), (-7,4), (-7,5), (-7,6), (-7,7), (-7,8), (-7,9), (-7,10), (-6,-12), (-6,-11), (-6,-10), (-6,-9), (-6,-8), (-6,-7), (-6,-6), (-6,-5), (-6,-4), (-6,-3), (-6,-2), (-6,-1), (-6,0), (-6,1), (-6,2), (-6,3), (-6,4), (-6,5), (-6,6), (-6,7), (-6,8), (-6,9), (-6,10), (-6,11), (-6,12), (-5,-12), (-5,-11), (-5,-10), (-5,-9), (-5,-8), (-5,-7), (-5,-6), (-5,-5), (-5,-4), (-5,-3), (-5,-2), (-5,-1), (-5,0), (-5,1), (-5,2), (-5,3), (-5,4), (-5,5), (-5,6), (-5,7), (-5,8), (-5,9)]
def spRawH613B2 : List qCell := [(-5,10), (-5,11), (-4,-13), (-4,-12), (-4,-11), (-4,-10), (-4,-9), (-4,-8), (-4,-7), (-4,-6), (-4,-5), (-4,-4), (-4,-3), (-4,-2), (-4,-1), (-4,0), (-4,1), (-4,2), (-4,3), (-4,4), (-4,5), (-4,6), (-4,7), (-4,8), (-4,9), (-4,10), (-4,11), (-4,12), (-3,-13), (-3,-12), (-3,-11), (-3,-10), (-3,-9), (-3,-8), (-3,-7), (-3,-6), (-3,-5), (-3,-4), (-3,-3), (-3,-2), (-3,-1), (-3,0), (-3,1), (-3,2), (-3,3), (-3,4), (-3,5), (-3,6), (-3,7), (-3,8), (-2,-13), (-2,-12), (-2,-11), (-2,-10), (-2,-9), (-2,-8), (-2,-7), (-2,-6), (-2,-5), (-2,-4), (-2,-3), (-2,-2), (-2,-1), (-2,0), (-2,2), (-2,3), (-2,4), (-2,5), (-2,6), (-2,7), (-2,8), (-1,-13), (-1,-12), (-1,-11), (-1,-10), (-1,-9), (-1,-8), (-1,-7), (-1,-6), (-1,-5), (-1,-4), (-1,-3), (-1,-2), (-1,0), (-1,1), (-1,2), (-1,3), (-1,4), (-1,5), (-1,6), (-1,7), (-1,8), (0,-13), (0,-12), (0,-11), (0,-10), (0,-9), (0,-8), (0,-7), (0,-6)]
def spRawH613B3 : List qCell := [(0,-5), (0,-4), (0,-3), (0,-2), (0,-1), (0,0), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (0,8), (1,-13), (1,-12), (1,-11), (1,-10), (1,-9), (1,-8), (1,-7), (1,-6), (1,-5), (1,-4), (1,-3), (1,-2), (1,-1), (1,0), (1,1), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (1,8), (2,-13), (2,-12), (2,-11), (2,-10), (2,-9), (2,-8), (2,-7), (2,-6), (2,-5), (2,-4), (2,-3), (2,-2), (2,-1), (2,0), (2,1), (2,2), (2,3), (2,4), (2,5), (2,6), (2,7), (2,8), (2,9), (2,10), (2,11), (2,12), (3,-12), (3,-11), (3,-10), (3,-9), (3,-8), (3,-7), (3,-6), (3,-5), (3,-4), (3,-3), (3,-2), (3,-1), (3,0), (3,1), (3,2), (3,3), (3,4), (3,5), (3,6), (3,7), (3,8), (3,9), (3,10), (3,11), (4,-12), (4,-11), (4,-10), (4,-9), (4,-8), (4,-7), (4,-6), (4,-5), (4,-4), (4,-3), (4,-2), (4,-1), (4,0), (4,1), (4,2)]
def spRawH613B4 : List qCell := [(4,3), (4,4), (4,5), (4,6), (4,7), (4,8), (4,9), (4,10), (4,11), (4,12), (5,-10), (5,-9), (5,-8), (5,-7), (5,-6), (5,-5), (5,-4), (5,-3), (5,-2), (5,-1), (5,0), (5,1), (5,2), (5,3), (5,4), (5,5), (5,6), (5,7), (5,8), (5,9), (5,10), (6,-10), (6,-9), (6,-8), (6,-7), (6,-6), (6,-5), (6,-4), (6,-3), (6,-2), (6,-1), (6,0), (6,1), (6,2), (6,3), (6,4), (6,5), (6,6), (6,7), (6,8), (6,9), (6,10), (7,-10), (7,-9), (7,-8), (7,-7), (7,-6), (7,-5), (7,-4), (7,-3), (7,-2), (7,-1), (7,0), (7,1), (7,2), (7,3), (7,4), (7,5), (7,6), (7,7), (7,8), (7,9), (7,10), (8,-10), (8,-9), (8,-8), (8,-7), (8,-6), (8,-5), (8,-4), (8,-3), (8,-2), (8,-1), (8,0), (8,1), (8,2), (8,3), (8,4), (8,5), (8,6), (8,7), (8,8), (8,9), (8,10), (9,-8), (9,-7), (9,-6), (9,-5), (9,-4), (9,-3)]
def spRawH613B5 : List qCell := [(9,-2), (9,-1), (9,0), (9,1), (9,2), (9,3), (9,4), (9,5), (9,6), (9,7), (9,8), (10,-7), (10,-6), (10,-5), (10,-4), (10,-3), (10,-2), (10,-1), (10,0), (10,1), (10,2), (10,3), (10,4), (10,5), (10,6), (10,7), (11,-5), (11,-4), (11,-3), (11,-2), (11,-1), (11,0), (11,1), (11,2), (11,3), (11,4), (11,5), (12,-4), (12,-3), (12,-2), (12,-1), (12,0), (12,1), (12,2), (12,3), (12,4), (13,-4), (13,-3), (13,-2), (13,-1), (13,0), (13,1), (13,2), (13,3), (13,4), (14,-2), (14,-1), (14,0), (14,1), (14,2), (15,-2), (15,0), (15,2)]
def spRawH613 : List qCell := spRawH613B0 ++ spRawH613B1 ++ spRawH613B2 ++ spRawH613B3 ++ spRawH613B4 ++ spRawH613B5
def spRawH613_eq : qm613.H = spRawH613.toFinset := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      let l0 : List qCell := [(-17,-2),(-17,0),(-17,2),(-16,-2),(-16,-1),(-16,0),(-16,1),(-16,2),(-15,-4),(-15,-3),(-15,-2),(-15,-1),(-15,0),(-15,1),(-15,2),(-15,3),(-15,4),(-14,-4),(-14,-3),(-14,-2),(-14,-1),(-14,0),(-14,1),(-14,2),(-14,3)]
      have hc0 : qf460 = l0.toFinset := by rfl
      let l1 : List qCell := [(-14,4),(-13,-5),(-13,-4),(-13,-3),(-13,-2),(-13,-1),(-13,0),(-13,1),(-13,2),(-13,3),(-13,4),(-13,5),(-12,-7),(-12,-6),(-12,-5),(-12,-4),(-12,-3),(-12,-2),(-12,-1),(-12,0),(-12,1),(-12,2),(-12,3),(-12,4),(-12,5)]
      have hc1 : qf461 = l1.toFinset := by rfl
      let l2 : List qCell := [(-12,6),(-12,7),(-11,-8),(-11,-7),(-11,-6),(-11,-5),(-11,-4),(-11,-3),(-11,-2),(-11,-1),(-11,0),(-11,1),(-11,2),(-11,3),(-11,4),(-11,5),(-11,6),(-11,7),(-11,8),(-10,-10),(-10,-9),(-10,-8),(-10,-7),(-10,-6),(-10,-5)]
      have hc2 : qf462 = l2.toFinset := by rfl
      let l3 : List qCell := [(-10,-4),(-10,-3),(-10,-2),(-10,-1),(-10,0),(-10,1),(-10,2),(-10,3),(-10,4),(-10,5),(-10,6),(-10,7),(-10,8),(-10,9),(-10,10),(-9,-10),(-9,-9),(-9,-8),(-9,-7),(-9,-6),(-9,-5),(-9,-4),(-9,-3),(-9,-2),(-9,-1)]
      have hc3 : qf463 = l3.toFinset := by rfl
      let l4 : List qCell := [(-9,0),(-9,1),(-9,2),(-9,3),(-9,4),(-9,5),(-9,6),(-9,7),(-9,8),(-9,9),(-9,10),(-8,-10),(-8,-9),(-8,-8),(-8,-7),(-8,-6),(-8,-5),(-8,-4),(-8,-3),(-8,-2),(-8,-1),(-8,0),(-8,1),(-8,2),(-8,3)]
      have hc4 : qf464 = l4.toFinset := by rfl
      let l5 : List qCell := [(-8,4),(-8,5),(-8,6),(-8,7),(-8,8),(-8,9),(-8,10),(-7,-10),(-7,-9),(-7,-8),(-7,-7),(-7,-6),(-7,-5),(-7,-4),(-7,-3),(-7,-2),(-7,-1),(-7,0),(-7,1),(-7,2),(-7,3),(-7,4),(-7,5),(-7,6),(-7,7)]
      have hc5 : qf465 = l5.toFinset := by rfl
      let l6 : List qCell := [(-7,8),(-7,9),(-7,10),(-6,-12),(-6,-11),(-6,-10),(-6,-9),(-6,-8),(-6,-7),(-6,-6),(-6,-5),(-6,-4),(-6,-3),(-6,-2),(-6,-1),(-6,0),(-6,1),(-6,2),(-6,3),(-6,4),(-6,5),(-6,6),(-6,7),(-6,8),(-6,9)]
      have hc6 : qf466 = l6.toFinset := by rfl
      let l7 : List qCell := [(-6,10),(-6,11),(-6,12),(-5,-12),(-5,-11),(-5,-10),(-5,-9),(-5,-8),(-5,-7),(-5,-6),(-5,-5),(-5,-4),(-5,-3),(-5,-2),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-5,8),(-5,9)]
      have hc7 : qf467 = l7.toFinset := by rfl
      let l8 : List qCell := [(-5,10),(-5,11),(-4,-13),(-4,-12),(-4,-11),(-4,-10),(-4,-9),(-4,-8),(-4,-7),(-4,-6),(-4,-5),(-4,-4),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-4,8),(-4,9)]
      have hc8 : qf468 = l8.toFinset := by rfl
      let l9 : List qCell := [(-4,10),(-4,11),(-4,12),(-3,-13),(-3,-12),(-3,-11),(-3,-10),(-3,-9),(-3,-8),(-3,-7),(-3,-6),(-3,-5),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8)]
      have hc9 : qf469 = l9.toFinset := by rfl
      let l10 : List qCell := [(-2,-13),(-2,-12),(-2,-11),(-2,-10),(-2,-9),(-2,-8),(-2,-7),(-2,-6),(-2,-5),(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-1,-13),(-1,-12),(-1,-11),(-1,-10)]
      have hc10 : qf470 = l10.toFinset := by rfl
      let l11 : List qCell := [(-1,-9),(-1,-8),(-1,-7),(-1,-6),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(0,-13),(0,-12),(0,-11),(0,-10),(0,-9),(0,-8),(0,-7),(0,-6)]
      have hc11 : qf471 = l11.toFinset := by rfl
      let l12 : List qCell := [(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,-13),(1,-12),(1,-11),(1,-10),(1,-9),(1,-8),(1,-7),(1,-6),(1,-5),(1,-4),(1,-3),(1,-2)]
      have hc12 : qf472 = l12.toFinset := by rfl
      let l13 : List qCell := [(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,-13),(2,-12),(2,-11),(2,-10),(2,-9),(2,-8),(2,-7),(2,-6),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1)]
      have hc13 : qf473 = l13.toFinset := by rfl
      let l14 : List qCell := [(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(2,12),(3,-12),(3,-11),(3,-10),(3,-9),(3,-8),(3,-7),(3,-6),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1)]
      have hc14 : qf474 = l14.toFinset := by rfl
      let l15 : List qCell := [(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(4,-12),(4,-11),(4,-10),(4,-9),(4,-8),(4,-7),(4,-6),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2)]
      have hc15 : qf475 = l15.toFinset := by rfl
      let l16 : List qCell := [(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(4,10),(4,11),(4,12),(5,-10),(5,-9),(5,-8),(5,-7),(5,-6),(5,-5),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4)]
      have hc16 : qf476 = l16.toFinset := by rfl
      let l17 : List qCell := [(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(6,-10),(6,-9),(6,-8),(6,-7),(6,-6),(6,-5),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8)]
      have hc17 : qf477 = l17.toFinset := by rfl
      let l18 : List qCell := [(6,9),(6,10),(7,-10),(7,-9),(7,-8),(7,-7),(7,-6),(7,-5),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(7,8),(7,9),(7,10),(8,-10),(8,-9)]
      have hc18 : qf478 = l18.toFinset := by rfl
      let l19 : List qCell := [(8,-8),(8,-7),(8,-6),(8,-5),(8,-4),(8,-3),(8,-2),(8,-1),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(8,7),(8,8),(8,9),(8,10),(9,-8),(9,-7),(9,-6),(9,-5),(9,-4),(9,-3)]
      have hc19 : qf479 = l19.toFinset := by rfl
      let l20 : List qCell := [(9,-2),(9,-1),(9,0),(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(9,7),(9,8),(10,-7),(10,-6),(10,-5),(10,-4),(10,-3),(10,-2),(10,-1),(10,0),(10,1),(10,2),(10,3),(10,4),(10,5),(10,6)]
      have hc20 : qf480 = l20.toFinset := by rfl
      let l21 : List qCell := [(10,7),(11,-5),(11,-4),(11,-3),(11,-2),(11,-1),(11,0),(11,1),(11,2),(11,3),(11,4),(11,5),(12,-4),(12,-3),(12,-2),(12,-1),(12,0),(12,1),(12,2),(12,3),(12,4),(13,-4),(13,-3),(13,-2),(13,-1)]
      have hc21 : qf481 = l21.toFinset := by rfl
      let l22 : List qCell := [(13,0),(13,1),(13,2),(13,3),(13,4),(14,-2),(14,-1),(14,0),(14,1),(14,2),(15,-2),(15,0),(15,2)]
      have hc22 : qf482 = l22.toFinset := by rfl
      have hu1 := spUnionToFinset hc0 hc1
      have hu2 := spUnionToFinset hu1 hc2
      have hu3 := spUnionToFinset hu2 hc3
      have hu4 := spUnionToFinset hu3 hc4
      have hu5 := spUnionToFinset hu4 hc5
      have hu6 := spUnionToFinset hu5 hc6
      have hu7 := spUnionToFinset hu6 hc7
      have hu8 := spUnionToFinset hu7 hc8
      have hu9 := spUnionToFinset hu8 hc9
      have hu10 := spUnionToFinset hu9 hc10
      have hu11 := spUnionToFinset hu10 hc11
      have hu12 := spUnionToFinset hu11 hc12
      have hu13 := spUnionToFinset hu12 hc13
      have hu14 := spUnionToFinset hu13 hc14
      have hu15 := spUnionToFinset hu14 hc15
      have hu16 := spUnionToFinset hu15 hc16
      have hu17 := spUnionToFinset hu16 hc17
      have hu18 := spUnionToFinset hu17 hc18
      have hu19 := spUnionToFinset hu18 hc19
      have hu20 := spUnionToFinset hu19 hc20
      have hu21 := spUnionToFinset hu20 hc21
      have hu22 := spUnionToFinset hu21 hc22
      have hl : (((((((((((((((((((((((l0 ++ l1) ++ l2) ++ l3) ++ l4) ++ l5) ++ l6) ++ l7) ++ l8) ++ l9) ++ l10) ++ l11) ++ l12) ++ l13) ++ l14) ++ l15) ++ l16) ++ l17) ++ l18) ++ l19) ++ l20) ++ l21) ++ l22) : List qCell) = spRawH613 := by
        simp only [List.append_assoc]
        rfl
      change (qf460 ∪ qf461 ∪ qf462 ∪ qf463 ∪ qf464 ∪ qf465 ∪ qf466 ∪ qf467 ∪ qf468 ∪ qf469 ∪ qf470 ∪ qf471 ∪ qf472 ∪ qf473 ∪ qf474 ∪ qf475 ∪ qf476 ∪ qf477 ∪ qf478 ∪ qf479 ∪ qf480 ∪ qf481 ∪ qf482) = spRawH613.toFinset
      exact hu22.trans (congrArg List.toFinset hl))))
def sp613Pl0 : List qCell := spRawH607.map (qplacement (qT.rotation ⟨607,5,5,4⟩) (qT.shift ⟨607,5,5,4⟩))
def sp613Pl1 : List qCell := spRawH503.map (qplacement (qT.rotation ⟨503,3,1,4⟩) (qT.shift ⟨503,3,1,4⟩))
def sp613Pl2 : List qCell := spRawH592.map (qplacement (qT.rotation ⟨592,7,1,3⟩) (qT.shift ⟨592,7,1,3⟩))
def sp613Pl3 : List qCell := spRawH592.map (qplacement (qT.rotation ⟨592,5,5,3⟩) (qT.shift ⟨592,5,5,3⟩))
def sp613Pl4 : List qCell := spRawH607.map (qplacement (qT.rotation ⟨607,7,1,4⟩) (qT.shift ⟨607,7,1,4⟩))
def sp613Pl5 : List qCell := spRawH612.map (qplacement (qT.rotation ⟨612,4,1,4⟩) (qT.shift ⟨612,4,1,4⟩))
def sp613Pl6 : List qCell := spRawH612.map (qplacement (qT.rotation ⟨612,0,5,4⟩) (qT.shift ⟨612,0,5,4⟩))
def sp613Combined : List qCell := qorigin :: (sp613Pl0 ++ sp613Pl1 ++ sp613Pl2 ++ sp613Pl3 ++ sp613Pl4 ++ sp613Pl5 ++ sp613Pl6)
def sp613Combined_canonical : qcanonical sp613Combined = spRawH613 := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| decide +kernel))
def sp613HSemantics : insert qorigin (qunionH [qplaceRow ⟨607,5,5,4⟩ qm607,qplaceRow ⟨503,3,1,4⟩ qm503,qplaceRow ⟨592,7,1,3⟩ qm592,qplaceRow ⟨592,5,5,3⟩ qm592,qplaceRow ⟨607,7,1,4⟩ qm607,qplaceRow ⟨612,4,1,4⟩ qm612,qplaceRow ⟨612,0,5,4⟩ qm612]) = sp613Combined.toFinset := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      have hp0 : (qplaceRow ⟨607,5,5,4⟩ qm607).H = sp613Pl0.toFinset :=
        spPlacedH_list ⟨607,5,5,4⟩ qm607 spRawH607 spRawH607_eq
      have hp1 : (qplaceRow ⟨503,3,1,4⟩ qm503).H = sp613Pl1.toFinset :=
        spPlacedH_list ⟨503,3,1,4⟩ qm503 spRawH503 spRawH503_eq
      have hp2 : (qplaceRow ⟨592,7,1,3⟩ qm592).H = sp613Pl2.toFinset :=
        spPlacedH_list ⟨592,7,1,3⟩ qm592 spRawH592 spRawH592_eq
      have hp3 : (qplaceRow ⟨592,5,5,3⟩ qm592).H = sp613Pl3.toFinset :=
        spPlacedH_list ⟨592,5,5,3⟩ qm592 spRawH592 spRawH592_eq
      have hp4 : (qplaceRow ⟨607,7,1,4⟩ qm607).H = sp613Pl4.toFinset :=
        spPlacedH_list ⟨607,7,1,4⟩ qm607 spRawH607 spRawH607_eq
      have hp5 : (qplaceRow ⟨612,4,1,4⟩ qm612).H = sp613Pl5.toFinset :=
        spPlacedH_list ⟨612,4,1,4⟩ qm612 spRawH612 spRawH612_eq
      have hp6 : (qplaceRow ⟨612,0,5,4⟩ qm612).H = sp613Pl6.toFinset :=
        spPlacedH_list ⟨612,0,5,4⟩ qm612 spRawH612 spRawH612_eq
      have hu : qunionH [qplaceRow ⟨607,5,5,4⟩ qm607,qplaceRow ⟨503,3,1,4⟩ qm503,qplaceRow ⟨592,7,1,3⟩ qm592,qplaceRow ⟨592,5,5,3⟩ qm592,qplaceRow ⟨607,7,1,4⟩ qm607,qplaceRow ⟨612,4,1,4⟩ qm612,qplaceRow ⟨612,0,5,4⟩ qm612] = ([sp613Pl0,sp613Pl1,sp613Pl2,sp613Pl3,sp613Pl4,sp613Pl5,sp613Pl6] : List (List qCell)).flatten.toFinset := by
        apply qlist_unionH
        exact (congrArg₂ List.cons hp0 (congrArg₂ List.cons hp1 (congrArg₂ List.cons hp2 (congrArg₂ List.cons hp3 (congrArg₂ List.cons hp4 (congrArg₂ List.cons hp5 (congrArg₂ List.cons hp6 (rfl : ([] : List (Finset qCell)) = []))))))))
      rw [hu]
      simp only [sp613Combined,List.flatten_cons,List.flatten_nil,List.append_nil,List.toFinset_cons,List.append_assoc])))
def sp613H : (qforkRow [qplaceRow ⟨607,5,5,4⟩ qm607,qplaceRow ⟨503,3,1,4⟩ qm503,qplaceRow ⟨592,7,1,3⟩ qm592,qplaceRow ⟨592,5,5,3⟩ qm592,qplaceRow ⟨607,7,1,4⟩ qm607,qplaceRow ⟨612,4,1,4⟩ qm612,qplaceRow ⟨612,0,5,4⟩ qm612]).H = qm613.H := by
  set_option maxRecDepth 100000 in
    change insert qorigin (qunionH [qplaceRow ⟨607,5,5,4⟩ qm607,qplaceRow ⟨503,3,1,4⟩ qm503,qplaceRow ⟨592,7,1,3⟩ qm592,qplaceRow ⟨592,5,5,3⟩ qm592,qplaceRow ⟨607,7,1,4⟩ qm607,qplaceRow ⟨612,4,1,4⟩ qm612,qplaceRow ⟨612,0,5,4⟩ qm612]) = qm613.H
    rw [sp613HSemantics,spRawH613_eq]
    exact qlist_H_target sp613Combined spRawH613 sp613Combined_canonical
def sp613S0 : Finset qCell := {(-7,2),(-7,3),(-7,4),(-6,-1),(-6,2),(-6,3),(-6,4),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-2,-1),(-2,0),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-1),(0,0),(0,2),(0,3),(0,4),(1,-1),(1,0),(1,3),(1,4),(2,-1),(2,4)}
def sp613Step0 : (qplaceRow ⟨503,3,1,4⟩ qm503).H ⊆ sp613S0 := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      have h : ∀ b ∈ spRawH503.map (qplacement (qT.rotation ⟨503,3,1,4⟩) (qT.shift ⟨503,3,1,4⟩)),b ∈ sp613S0 := by decide +kernel
      intro b hm
      exact h b ((spPlacedH_mem ⟨503,3,1,4⟩ qm503 spRawH503 spRawH503_eq b).mp hm))))
def sp613S1 : Finset qCell := {(-7,2),(-7,3),(-7,4),(-6,-1),(-6,2),(-6,3),(-6,4),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-1,0),(0,0),(1,-1),(1,0),(2,-1)}
def sp613Step1 : ∀ b ∈ sp613S0,b ∈ (qplaceRow ⟨592,7,1,3⟩ qm592).H → b ∈ sp613S1 := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      have h : ∀ b ∈ sp613S0,b ∈ spRawH592.map (qplacement (qT.rotation ⟨592,7,1,3⟩) (qT.shift ⟨592,7,1,3⟩)) → b ∈ sp613S1 := by decide +kernel
      intro b hb hm
      exact h b hb ((spPlacedH_mem ⟨592,7,1,3⟩ qm592 spRawH592 spRawH592_eq b).mp hm))))
def sp613S2 : Finset qCell := {(-5,-1),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,0),(-1,0),(0,0),(1,-1),(1,0),(2,-1)}
def sp613Step2 : ∀ b ∈ sp613S1,b ∈ (qplaceRow ⟨592,5,5,3⟩ qm592).H → b ∈ sp613S2 := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      have h : ∀ b ∈ sp613S1,b ∈ spRawH592.map (qplacement (qT.rotation ⟨592,5,5,3⟩) (qT.shift ⟨592,5,5,3⟩)) → b ∈ sp613S2 := by decide +kernel
      intro b hb hm
      exact h b hb ((spPlacedH_mem ⟨592,5,5,3⟩ qm592 spRawH592 spRawH592_eq b).mp hm))))
def sp613S3 : Finset qCell := {(-3,-1),(-2,0),(-1,0),(0,0),(1,-1),(1,0),(2,-1)}
def sp613Step3 : ∀ b ∈ sp613S2,b ∈ (qplaceRow ⟨607,5,5,4⟩ qm607).H → b ∈ sp613S3 := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      have h : ∀ b ∈ sp613S2,b ∈ spRawH607.map (qplacement (qT.rotation ⟨607,5,5,4⟩) (qT.shift ⟨607,5,5,4⟩)) → b ∈ sp613S3 := by decide +kernel
      intro b hb hm
      exact h b hb ((spPlacedH_mem ⟨607,5,5,4⟩ qm607 spRawH607 spRawH607_eq b).mp hm))))
def sp613S4 : Finset qCell := {(-3,-1),(-2,0),(-1,0),(0,0),(1,-1)}
def sp613Step4 : ∀ b ∈ sp613S3,b ∈ (qplaceRow ⟨607,7,1,4⟩ qm607).H → b ∈ sp613S4 := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      have h : ∀ b ∈ sp613S3,b ∈ spRawH607.map (qplacement (qT.rotation ⟨607,7,1,4⟩) (qT.shift ⟨607,7,1,4⟩)) → b ∈ sp613S4 := by decide +kernel
      intro b hb hm
      exact h b hb ((spPlacedH_mem ⟨607,7,1,4⟩ qm607 spRawH607 spRawH607_eq b).mp hm))))
def sp613S5 : Finset qCell := {(-2,0),(-1,0),(0,0),(1,-1)}
def sp613Step5 : ∀ b ∈ sp613S4,b ∈ (qplaceRow ⟨612,4,1,4⟩ qm612).H → b ∈ sp613S5 := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      have h : ∀ b ∈ sp613S4,b ∈ spRawH612.map (qplacement (qT.rotation ⟨612,4,1,4⟩) (qT.shift ⟨612,4,1,4⟩)) → b ∈ sp613S5 := by decide +kernel
      intro b hb hm
      exact h b hb ((spPlacedH_mem ⟨612,4,1,4⟩ qm612 spRawH612 spRawH612_eq b).mp hm))))
def sp613S6 : Finset qCell := {(-2,0),(-1,0),(0,0)}
def sp613Step6 : ∀ b ∈ sp613S5,b ∈ (qplaceRow ⟨612,0,5,4⟩ qm612).H → b ∈ sp613S6 := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      have h : ∀ b ∈ sp613S5,b ∈ spRawH612.map (qplacement (qT.rotation ⟨612,0,5,4⟩) (qT.shift ⟨612,0,5,4⟩)) → b ∈ sp613S6 := by decide +kernel
      intro b hb hm
      exact h b hb ((spPlacedH_mem ⟨612,0,5,4⟩ qm612 spRawH612 spRawH612_eq b).mp hm))))
def sp613Bound : qcommonH [qplaceRow ⟨607,5,5,4⟩ qm607,qplaceRow ⟨503,3,1,4⟩ qm503,qplaceRow ⟨592,7,1,3⟩ qm592,qplaceRow ⟨592,5,5,3⟩ qm592,qplaceRow ⟨607,7,1,4⟩ qm607,qplaceRow ⟨612,4,1,4⟩ qm612,qplaceRow ⟨612,0,5,4⟩ qm612] ⊆ insert qorigin ({(-2,0),(-1,0),(-1,1)} : Finset qCell) := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      intro b hb
      have h0 := sp613Step0 (qcommonH_le_at [qplaceRow ⟨607,5,5,4⟩ qm607,qplaceRow ⟨503,3,1,4⟩ qm503,qplaceRow ⟨592,7,1,3⟩ qm592,qplaceRow ⟨592,5,5,3⟩ qm592,qplaceRow ⟨607,7,1,4⟩ qm607,qplaceRow ⟨612,4,1,4⟩ qm612,qplaceRow ⟨612,0,5,4⟩ qm612] 1 (qplaceRow ⟨503,3,1,4⟩ qm503) rfl hb)
      have h1 := sp613Step1 b h0 (qcommonH_le_at [qplaceRow ⟨607,5,5,4⟩ qm607,qplaceRow ⟨503,3,1,4⟩ qm503,qplaceRow ⟨592,7,1,3⟩ qm592,qplaceRow ⟨592,5,5,3⟩ qm592,qplaceRow ⟨607,7,1,4⟩ qm607,qplaceRow ⟨612,4,1,4⟩ qm612,qplaceRow ⟨612,0,5,4⟩ qm612] 2 (qplaceRow ⟨592,7,1,3⟩ qm592) rfl hb)
      have h2 := sp613Step2 b h1 (qcommonH_le_at [qplaceRow ⟨607,5,5,4⟩ qm607,qplaceRow ⟨503,3,1,4⟩ qm503,qplaceRow ⟨592,7,1,3⟩ qm592,qplaceRow ⟨592,5,5,3⟩ qm592,qplaceRow ⟨607,7,1,4⟩ qm607,qplaceRow ⟨612,4,1,4⟩ qm612,qplaceRow ⟨612,0,5,4⟩ qm612] 3 (qplaceRow ⟨592,5,5,3⟩ qm592) rfl hb)
      have h3 := sp613Step3 b h2 (qcommonH_le_at [qplaceRow ⟨607,5,5,4⟩ qm607,qplaceRow ⟨503,3,1,4⟩ qm503,qplaceRow ⟨592,7,1,3⟩ qm592,qplaceRow ⟨592,5,5,3⟩ qm592,qplaceRow ⟨607,7,1,4⟩ qm607,qplaceRow ⟨612,4,1,4⟩ qm612,qplaceRow ⟨612,0,5,4⟩ qm612] 0 (qplaceRow ⟨607,5,5,4⟩ qm607) rfl hb)
      have h4 := sp613Step4 b h3 (qcommonH_le_at [qplaceRow ⟨607,5,5,4⟩ qm607,qplaceRow ⟨503,3,1,4⟩ qm503,qplaceRow ⟨592,7,1,3⟩ qm592,qplaceRow ⟨592,5,5,3⟩ qm592,qplaceRow ⟨607,7,1,4⟩ qm607,qplaceRow ⟨612,4,1,4⟩ qm612,qplaceRow ⟨612,0,5,4⟩ qm612] 4 (qplaceRow ⟨607,7,1,4⟩ qm607) rfl hb)
      have h5 := sp613Step5 b h4 (qcommonH_le_at [qplaceRow ⟨607,5,5,4⟩ qm607,qplaceRow ⟨503,3,1,4⟩ qm503,qplaceRow ⟨592,7,1,3⟩ qm592,qplaceRow ⟨592,5,5,3⟩ qm592,qplaceRow ⟨607,7,1,4⟩ qm607,qplaceRow ⟨612,4,1,4⟩ qm612,qplaceRow ⟨612,0,5,4⟩ qm612] 5 (qplaceRow ⟨612,4,1,4⟩ qm612) rfl hb)
      have h6 := sp613Step6 b h5 (qcommonH_le_at [qplaceRow ⟨607,5,5,4⟩ qm607,qplaceRow ⟨503,3,1,4⟩ qm503,qplaceRow ⟨592,7,1,3⟩ qm592,qplaceRow ⟨592,5,5,3⟩ qm592,qplaceRow ⟨607,7,1,4⟩ qm607,qplaceRow ⟨612,4,1,4⟩ qm612,qplaceRow ⟨612,0,5,4⟩ qm612] 6 (qplaceRow ⟨612,0,5,4⟩ qm612) rfl hb)
      exact (show sp613S6 ⊆ insert qorigin ({(-2,0),(-1,0),(-1,1)} : Finset qCell) by decide +kernel) h6)))
def sp613A : (qforkRow [qplaceRow ⟨607,5,5,4⟩ qm607,qplaceRow ⟨503,3,1,4⟩ qm503,qplaceRow ⟨592,7,1,3⟩ qm592,qplaceRow ⟨592,5,5,3⟩ qm592,qplaceRow ⟨607,7,1,4⟩ qm607,qplaceRow ⟨612,4,1,4⟩ qm612,qplaceRow ⟨612,0,5,4⟩ qm612]).A = ({(-2,0),(-1,0),(-1,1)} : Finset qCell) := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      change (qunionA [qplaceRow ⟨607,5,5,4⟩ qm607,qplaceRow ⟨503,3,1,4⟩ qm503,qplaceRow ⟨592,7,1,3⟩ qm592,qplaceRow ⟨592,5,5,3⟩ qm592,qplaceRow ⟨607,7,1,4⟩ qm607,qplaceRow ⟨612,4,1,4⟩ qm612,qplaceRow ⟨612,0,5,4⟩ qm612] ∪ qcommonH [qplaceRow ⟨607,5,5,4⟩ qm607,qplaceRow ⟨503,3,1,4⟩ qm503,qplaceRow ⟨592,7,1,3⟩ qm592,qplaceRow ⟨592,5,5,3⟩ qm592,qplaceRow ⟨607,7,1,4⟩ qm607,qplaceRow ⟨612,4,1,4⟩ qm612,qplaceRow ⟨612,0,5,4⟩ qm612]).erase qorigin = ({(-2,0),(-1,0),(-1,1)} : Finset qCell)
      apply erase_union_eq_of_left_subset
      · decide +kernel
      · exact sp613Bound
      · decide +kernel
      · decide +kernel)))
def qmeq_613 : qr 613 = qm613 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 613 = qv613 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 613 < 6 by decide,↓reduceDIte,he,qv613,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_503,qmeq_592,qmeq_607,qmeq_612]
          apply qx
          · exact sp613A
          · exact sp613H
          · run_tac qhb (← `(tactic| decide +kernel)))))
def ql614b0 : List qCell := [(-15,-2),(-15,0),(-15,2),(-14,-2),(-14,-1),(-14,0),(-14,1),(-14,2),(-13,-4),(-13,-3),(-13,-2),(-13,-1),(-13,0),(-13,1),(-13,2),(-13,3),(-13,4),(-13,5),(-13,6),(-12,-4),(-12,-3),(-12,-2),(-12,-1),(-12,0),(-12,1)]
def ql614b1 : List qCell := [(-12,2),(-12,3),(-12,4),(-12,5),(-12,6),(-11,-5),(-11,-4),(-11,-3),(-11,-2),(-11,-1),(-11,0),(-11,1),(-11,2),(-11,3),(-11,4),(-11,5),(-11,6),(-11,7),(-11,8),(-11,9),(-10,-7),(-10,-6),(-10,-5),(-10,-4),(-10,-3)]
def ql614b2 : List qCell := [(-10,-2),(-10,-1),(-10,0),(-10,1),(-10,2),(-10,3),(-10,4),(-10,5),(-10,6),(-10,7),(-10,8),(-10,9),(-9,-8),(-9,-7),(-9,-6),(-9,-5),(-9,-4),(-9,-3),(-9,-2),(-9,-1),(-9,0),(-9,1),(-9,2),(-9,3),(-9,4)]
def ql614b3 : List qCell := [(-9,5),(-9,6),(-9,7),(-9,8),(-9,9),(-9,10),(-8,-10),(-8,-9),(-8,-8),(-8,-7),(-8,-6),(-8,-5),(-8,-4),(-8,-3),(-8,-2),(-8,-1),(-8,0),(-8,1),(-8,2),(-8,3),(-8,4),(-8,5),(-8,6),(-8,7),(-8,8)]
def ql614b4 : List qCell := [(-8,9),(-8,10),(-8,11),(-8,12),(-7,-10),(-7,-9),(-7,-8),(-7,-7),(-7,-6),(-7,-5),(-7,-4),(-7,-3),(-7,-2),(-7,-1),(-7,0),(-7,1),(-7,2),(-7,3),(-7,4),(-7,5),(-7,6),(-7,7),(-7,8),(-7,9),(-7,10)]
def ql614b5 : List qCell := [(-7,11),(-7,12),(-6,-10),(-6,-9),(-6,-8),(-6,-7),(-6,-6),(-6,-5),(-6,-4),(-6,-3),(-6,-2),(-6,-1),(-6,0),(-6,1),(-6,2),(-6,3),(-6,4),(-6,5),(-6,6),(-6,7),(-6,8),(-6,9),(-6,10),(-6,11),(-6,12)]
def ql614b6 : List qCell := [(-5,-10),(-5,-9),(-5,-8),(-5,-7),(-5,-6),(-5,-5),(-5,-4),(-5,-3),(-5,-2),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-5,8),(-5,9),(-5,10),(-5,11),(-5,12),(-5,13),(-5,14)]
def ql614b7 : List qCell := [(-4,-12),(-4,-11),(-4,-10),(-4,-9),(-4,-8),(-4,-7),(-4,-6),(-4,-5),(-4,-4),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-4,8),(-4,9),(-4,10),(-4,11),(-4,12)]
def ql614b8 : List qCell := [(-4,13),(-4,14),(-3,-12),(-3,-11),(-3,-10),(-3,-9),(-3,-8),(-3,-7),(-3,-6),(-3,-5),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-3,10)]
def ql614b9 : List qCell := [(-3,11),(-3,12),(-3,13),(-3,14),(-2,-13),(-2,-12),(-2,-11),(-2,-10),(-2,-9),(-2,-8),(-2,-7),(-2,-6),(-2,-5),(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7)]
def ql614b10 : List qCell := [(-2,8),(-2,9),(-2,10),(-2,11),(-2,12),(-2,13),(-2,14),(-1,-13),(-1,-12),(-1,-11),(-1,-10),(-1,-9),(-1,-8),(-1,-7),(-1,-6),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4)]
def ql614b11 : List qCell := [(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(-1,11),(-1,12),(-1,13),(-1,14),(-1,15),(-1,16),(0,-13),(0,-12),(0,-11),(0,-10),(0,-9),(0,-8),(0,-7),(0,-6),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1)]
def ql614b12 : List qCell := [(0,0),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(0,15),(1,-13),(1,-12),(1,-11),(1,-10),(1,-9),(1,-8),(1,-7),(1,-6),(1,-5),(1,-4)]
def ql614b13 : List qCell := [(1,-3),(1,-2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(1,12),(1,13),(1,14),(1,15),(1,16),(1,17),(2,-13),(2,-12),(2,-11),(2,-10),(2,-9)]
def ql614b14 : List qCell := [(2,-8),(2,-7),(2,-6),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(2,12),(2,13),(2,14),(2,15),(2,16)]
def ql614b15 : List qCell := [(3,-13),(3,-12),(3,-11),(3,-10),(3,-9),(3,-8),(3,-7),(3,-6),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11)]
def ql614b16 : List qCell := [(3,12),(3,13),(3,14),(3,15),(3,16),(3,17),(4,-13),(4,-12),(4,-11),(4,-10),(4,-9),(4,-8),(4,-7),(4,-6),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5)]
def ql614b17 : List qCell := [(4,6),(4,7),(4,8),(4,9),(4,10),(4,11),(4,12),(4,13),(4,14),(4,15),(5,-12),(5,-11),(5,-10),(5,-9),(5,-8),(5,-7),(5,-6),(5,-5),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2)]
def ql614b18 : List qCell := [(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(5,11),(5,12),(5,13),(5,14),(5,15),(6,-12),(6,-11),(6,-10),(6,-9),(6,-8),(6,-7),(6,-6),(6,-5),(6,-4),(6,-3),(6,-2),(6,-1)]
def ql614b19 : List qCell := [(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(6,9),(6,10),(6,11),(6,12),(6,13),(6,14),(6,15),(7,-10),(7,-9),(7,-8),(7,-7),(7,-6),(7,-5),(7,-4),(7,-3),(7,-2)]
def ql614b20 : List qCell := [(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(7,8),(7,9),(7,10),(7,11),(7,12),(7,13),(7,14),(7,15),(8,-10),(8,-9),(8,-8),(8,-7),(8,-6),(8,-5),(8,-4),(8,-3)]
def ql614b21 : List qCell := [(8,-2),(8,-1),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(8,7),(8,8),(8,9),(8,10),(8,11),(8,12),(8,13),(9,-10),(9,-9),(9,-8),(9,-7),(9,-6),(9,-5),(9,-4),(9,-3),(9,-2)]
def ql614b22 : List qCell := [(9,-1),(9,0),(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(9,7),(9,8),(9,9),(9,10),(9,11),(9,12),(9,13),(10,-10),(10,-9),(10,-8),(10,-7),(10,-6),(10,-5),(10,-4),(10,-3),(10,-2),(10,-1)]
def ql614b23 : List qCell := [(10,0),(10,1),(10,2),(10,3),(10,4),(10,5),(10,6),(10,7),(10,8),(10,9),(10,10),(10,11),(10,12),(10,13),(11,-8),(11,-7),(11,-6),(11,-5),(11,-4),(11,-3),(11,-2),(11,-1),(11,0),(11,1),(11,2)]
def ql614b24 : List qCell := [(11,3),(11,4),(11,5),(11,6),(11,7),(11,8),(11,9),(11,10),(11,11),(12,-7),(12,-6),(12,-5),(12,-4),(12,-3),(12,-2),(12,-1),(12,0),(12,1),(12,2),(12,3),(12,4),(12,5),(12,6),(12,7),(12,8)]
def ql614b25 : List qCell := [(12,9),(12,10),(13,-5),(13,-4),(13,-3),(13,-2),(13,-1),(13,0),(13,1),(13,2),(13,3),(13,4),(13,5),(13,6),(13,7),(13,8),(13,9),(13,10),(14,-4),(14,-3),(14,-2),(14,-1),(14,0),(14,1),(14,2)]
def ql614b26 : List qCell := [(14,3),(14,4),(14,5),(14,6),(14,7),(15,-4),(15,-3),(15,-2),(15,-1),(15,0),(15,1),(15,2),(15,3),(15,4),(15,5),(15,6),(15,7),(16,-2),(16,-1),(16,0),(16,1),(16,2),(16,3),(17,-2),(17,0)]
def ql614b27 : List qCell := [(17,1),(17,2),(17,3)]
def ql614 : List qCell := ql614b0 ++ ql614b1 ++ ql614b2 ++ ql614b3 ++ ql614b4 ++ ql614b5 ++ ql614b6 ++ ql614b7 ++ ql614b8 ++ ql614b9 ++ ql614b10 ++ ql614b11 ++ ql614b12 ++ ql614b13 ++ ql614b14 ++ ql614b15 ++ ql614b16 ++ ql614b17 ++ ql614b18 ++ ql614b19 ++ ql614b20 ++ ql614b21 ++ ql614b22 ++ ql614b23 ++ ql614b24 ++ ql614b25 ++ ql614b26 ++ ql614b27
lemma qn614 : (ql614).Nodup := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qm614 : qR := ⟨{(1,0),(1,1)},⟨(ql614 : Multiset qCell), Multiset.coe_nodup.mpr qn614⟩,33⟩
def spRawH370B0 : List qCell := [(-5,-1), (-5,1), (-4,-1), (-4,0), (-4,1), (-3,-1), (-3,0), (-3,1), (-3,2), (-3,3), (-2,-2), (-2,-1), (-2,0), (-1,0), (-1,1), (0,-1), (0,0), (0,1), (0,2), (0,3), (1,-2), (1,-1), (1,0), (1,1), (1,2), (1,3), (1,4), (2,-1), (2,1), (2,2), (2,3), (2,4), (3,-1), (3,2), (4,2)]
def spRawH370 : List qCell := spRawH370B0
def spRawH370_eq : qm370.H = spRawH370.toFinset := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      change (spRawH370B0.toFinset) = spRawH370.toFinset
      simp only [spRawH370,List.toFinset_append,Finset.union_assoc])))
def spRawH392B0 : List qCell := [(-4,-1), (-4,1), (-3,-1), (-3,0), (-3,1), (-2,-1), (-2,0), (-2,1), (-1,-5), (-1,-4), (-1,-3), (-1,-2), (-1,0), (-1,1), (-1,2), (-1,3), (0,-4), (0,-3), (0,-2), (0,-1), (0,0), (0,1), (0,2), (1,-5), (1,-4), (1,-3), (1,-1), (1,0), (1,1), (1,2), (1,3), (2,-1), (2,0), (2,1), (3,-1), (3,0), (3,1), (4,-1), (4,0), (4,1), (5,-1)]
def spRawH392 : List qCell := spRawH392B0
def spRawH392_eq : qm392.H = spRawH392.toFinset := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      change (spRawH392B0.toFinset) = spRawH392.toFinset
      simp only [spRawH392,List.toFinset_append,Finset.union_assoc])))
def spRawH543B0 : List qCell := [(-6,3), (-5,-1), (-5,3), (-4,-1), (-4,1), (-4,2), (-4,3), (-3,-2), (-3,-1), (-3,1), (-3,2), (-3,3), (-3,4), (-3,5), (-3,6), (-3,7), (-2,-2), (-2,-1), (-2,0), (-2,1), (-2,2), (-2,3), (-2,4), (-2,5), (-2,6), (-1,-1), (-1,0), (-1,2), (-1,3), (-1,4), (-1,5), (-1,6), (0,-3), (0,-2), (0,-1), (0,0), (0,1), (0,2), (1,-4), (1,-3), (1,-2), (1,-1), (1,0), (1,1), (1,2), (2,-4), (2,-3), (2,-2), (2,-1), (2,0), (2,1), (3,-2), (3,-1), (3,1), (4,-2)]
def spRawH543 : List qCell := spRawH543B0
def spRawH543_eq : qm543.H = spRawH543.toFinset := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      change (spRawH543B0.toFinset) = spRawH543.toFinset
      simp only [spRawH543,List.toFinset_append,Finset.union_assoc])))
def spRawH600B0 : List qCell := [(-5,-1), (-5,1), (-5,2), (-5,4), (-4,-5), (-4,-3), (-4,-1), (-4,0), (-4,1), (-4,2), (-4,3), (-4,4), (-3,-5), (-3,-4), (-3,-3), (-3,-2), (-3,-1), (-3,0), (-3,1), (-3,2), (-3,3), (-3,4), (-3,5), (-3,6), (-3,7)]
def spRawH600B1 : List qCell := [(-3,8), (-3,9), (-2,-8), (-2,-7), (-2,-6), (-2,-5), (-2,-4), (-2,-3), (-2,-2), (-2,0), (-2,2), (-2,3), (-2,4), (-2,5), (-2,6), (-2,7), (-2,8), (-1,-8), (-1,-7), (-1,-6), (-1,-5), (-1,-4), (-1,-3), (-1,-2), (-1,0)]
def spRawH600B2 : List qCell := [(-1,1), (-1,2), (-1,3), (-1,4), (-1,5), (-1,6), (-1,7), (-1,8), (-1,9), (0,-8), (0,-7), (0,-6), (0,-5), (0,-4), (0,-3), (0,-2), (0,-1), (0,0), (0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7)]
def spRawH600B3 : List qCell := [(1,-12), (1,-11), (1,-10), (1,-9), (1,-8), (1,-7), (1,-6), (1,-5), (1,-4), (1,-3), (1,-2), (1,-1), (1,0), (1,1), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (2,-11), (2,-10), (2,-9), (2,-8), (2,-7)]
def spRawH600B4 : List qCell := [(2,-6), (2,-5), (2,-4), (2,-3), (2,-2), (2,-1), (2,0), (2,1), (2,2), (2,3), (2,4), (2,5), (2,6), (2,7), (3,-12), (3,-11), (3,-10), (3,-9), (3,-8), (3,-7), (3,-6), (3,-5), (3,-4), (3,-3), (3,-2)]
def spRawH600B5 : List qCell := [(3,-1), (3,0), (3,1), (3,2), (3,3), (3,4), (3,5), (3,6), (3,7), (4,-10), (4,-9), (4,-8), (4,-7), (4,-6), (4,-5), (4,-4), (4,-3), (4,-2), (4,-1), (4,0), (4,1), (4,2), (4,3), (4,4), (4,5)]
def spRawH600B6 : List qCell := [(5,-10), (5,-9), (5,-8), (5,-7), (5,-6), (5,-5), (5,-4), (5,-3), (5,-2), (5,-1), (5,0), (5,1), (5,2), (5,3), (5,4), (6,-10), (6,-9), (6,-8), (6,-7), (6,-6), (6,-5), (6,-4), (6,-3), (6,-2), (6,-1)]
def spRawH600B7 : List qCell := [(6,0), (6,1), (6,2), (6,3), (6,4), (6,5), (6,6), (7,-10), (7,-9), (7,-8), (7,-7), (7,-6), (7,-5), (7,-4), (7,-3), (7,-2), (7,-1), (7,0), (7,1), (7,2), (7,3), (7,4), (7,5), (7,6), (8,-8)]
def spRawH600B8 : List qCell := [(8,-7), (8,-6), (8,-5), (8,-4), (8,-3), (8,-2), (8,-1), (8,0), (8,1), (8,2), (8,3), (8,4), (8,5), (9,-7), (9,-6), (9,-5), (9,-4), (9,-3), (9,-2), (9,-1), (9,0), (9,1), (9,2), (9,3), (9,4)]
def spRawH600B9 : List qCell := [(9,5), (9,6), (10,-5), (10,-4), (10,-3), (10,-2), (10,-1), (10,0), (10,1), (10,2), (10,3), (10,4), (11,-4), (11,-3), (11,-2), (11,-1), (11,0), (11,1), (11,2), (11,3), (11,4), (12,-4), (12,-3), (12,-2), (12,-1)]
def spRawH600B10 : List qCell := [(12,0), (12,1), (12,2), (12,4), (13,0), (13,1), (13,2), (14,0), (14,2)]
def spRawH600 : List qCell := spRawH600B0 ++ spRawH600B1 ++ spRawH600B2 ++ spRawH600B3 ++ spRawH600B4 ++ spRawH600B5 ++ spRawH600B6 ++ spRawH600B7 ++ spRawH600B8 ++ spRawH600B9 ++ spRawH600B10
def spRawH600_eq : qm600.H = spRawH600.toFinset := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      let l0 : List qCell := [(-5,-1),(-5,1),(-5,2),(-5,4),(-4,-5),(-4,-3),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-3,-5),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7)]
      have hc0 : qf289 = l0.toFinset := by rfl
      let l1 : List qCell := [(-3,8),(-3,9),(-2,-8),(-2,-7),(-2,-6),(-2,-5),(-2,-4),(-2,-3),(-2,-2),(-2,0),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-1,-8),(-1,-7),(-1,-6),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,0)]
      have hc1 : qf290 = l1.toFinset := by rfl
      let l2 : List qCell := [(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(0,-8),(0,-7),(0,-6),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7)]
      have hc2 : qf291 = l2.toFinset := by rfl
      let l3 : List qCell := [(1,-12),(1,-11),(1,-10),(1,-9),(1,-8),(1,-7),(1,-6),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,-11),(2,-10),(2,-9),(2,-8),(2,-7)]
      have hc3 : qf292 = l3.toFinset := by rfl
      let l4 : List qCell := [(2,-6),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(3,-12),(3,-11),(3,-10),(3,-9),(3,-8),(3,-7),(3,-6),(3,-5),(3,-4),(3,-3),(3,-2)]
      have hc4 : qf293 = l4.toFinset := by rfl
      let l5 : List qCell := [(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(4,-10),(4,-9),(4,-8),(4,-7),(4,-6),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5)]
      have hc5 : qf294 = l5.toFinset := by rfl
      let l6 : List qCell := [(5,-10),(5,-9),(5,-8),(5,-7),(5,-6),(5,-5),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(6,-10),(6,-9),(6,-8),(6,-7),(6,-6),(6,-5),(6,-4),(6,-3),(6,-2),(6,-1)]
      have hc6 : qf295 = l6.toFinset := by rfl
      let l7 : List qCell := [(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(7,-10),(7,-9),(7,-8),(7,-7),(7,-6),(7,-5),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(8,-8)]
      have hc7 : qf296 = l7.toFinset := by rfl
      let l8 : List qCell := [(8,-7),(8,-6),(8,-5),(8,-4),(8,-3),(8,-2),(8,-1),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(9,-7),(9,-6),(9,-5),(9,-4),(9,-3),(9,-2),(9,-1),(9,0),(9,1),(9,2),(9,3),(9,4)]
      have hc8 : qf297 = l8.toFinset := by rfl
      let l9 : List qCell := [(9,5),(9,6),(10,-5),(10,-4),(10,-3),(10,-2),(10,-1),(10,0),(10,1),(10,2),(10,3),(10,4),(11,-4),(11,-3),(11,-2),(11,-1),(11,0),(11,1),(11,2),(11,3),(11,4),(12,-4),(12,-3),(12,-2),(12,-1)]
      have hc9 : qf298 = l9.toFinset := by rfl
      let l10 : List qCell := [(12,0),(12,1),(12,2),(12,4),(13,0),(13,1),(13,2),(14,0),(14,2)]
      have hc10 : qf299 = l10.toFinset := by rfl
      have hu1 := spUnionToFinset hc0 hc1
      have hu2 := spUnionToFinset hu1 hc2
      have hu3 := spUnionToFinset hu2 hc3
      have hu4 := spUnionToFinset hu3 hc4
      have hu5 := spUnionToFinset hu4 hc5
      have hu6 := spUnionToFinset hu5 hc6
      have hu7 := spUnionToFinset hu6 hc7
      have hu8 := spUnionToFinset hu7 hc8
      have hu9 := spUnionToFinset hu8 hc9
      have hu10 := spUnionToFinset hu9 hc10
      have hl : (((((((((((l0 ++ l1) ++ l2) ++ l3) ++ l4) ++ l5) ++ l6) ++ l7) ++ l8) ++ l9) ++ l10) : List qCell) = spRawH600 := by
        simp only [List.append_assoc]
        rfl
      change (qf289 ∪ qf290 ∪ qf291 ∪ qf292 ∪ qf293 ∪ qf294 ∪ qf295 ∪ qf296 ∪ qf297 ∪ qf298 ∪ qf299) = spRawH600.toFinset
      exact hu10.trans (congrArg List.toFinset hl))))
def spRawH608B0 : List qCell := [(-9,-1), (-9,1), (-9,3), (-8,-1), (-8,0), (-8,1), (-8,2), (-8,3), (-7,-1), (-7,0), (-7,1), (-7,2), (-7,3), (-7,4), (-7,5), (-7,6), (-7,8), (-6,-3), (-6,-2), (-6,-1), (-6,0), (-6,1), (-6,2), (-6,3), (-6,4), (-6,5), (-6,6), (-6,7), (-6,8), (-5,-2), (-5,-1), (-5,0), (-5,1), (-5,2), (-5,3), (-5,4), (-5,5), (-5,6), (-5,7), (-5,8), (-5,9), (-5,10), (-5,11), (-4,-3), (-4,-2), (-4,-1), (-4,0), (-4,1), (-4,2), (-4,3), (-4,4), (-4,5), (-4,6), (-4,7), (-4,8), (-4,9), (-4,10), (-3,-2), (-3,-1), (-3,0), (-3,1), (-3,2), (-3,3), (-3,4), (-3,5), (-3,6), (-3,7), (-3,8), (-3,9), (-3,10), (-3,11), (-3,12), (-3,13), (-2,-3), (-2,-1), (-2,0), (-2,1), (-2,2), (-2,3), (-2,4), (-2,5), (-2,6), (-2,7), (-2,8), (-2,9), (-2,10), (-2,11), (-2,12), (-1,-3), (-1,-2), (-1,-1), (-1,0), (-1,1), (-1,2), (-1,3), (-1,4), (-1,5), (-1,6), (-1,7), (-1,8)]
def spRawH608B1 : List qCell := [(-1,9), (-1,10), (-1,11), (-1,12), (-1,13), (0,-2), (0,-1), (0,0), (0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (0,8), (0,9), (0,10), (0,11), (0,12), (0,13), (0,14), (1,-7), (1,-6), (1,-5), (1,-4), (1,-3), (1,-2), (1,-1), (1,0), (1,1), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (1,8), (1,9), (1,10), (1,11), (1,12), (1,13), (2,-7), (2,-6), (2,-5), (2,-4), (2,-3), (2,-2), (2,-1), (2,0), (2,1), (2,2), (2,3), (2,4), (2,5), (2,6), (2,7), (2,8), (2,9), (2,10), (2,11), (2,12), (2,13), (2,14), (3,-7), (3,-6), (3,-5), (3,-4), (3,-3), (3,-2), (3,-1), (3,0), (3,1), (3,2), (3,3), (3,4), (3,5), (3,6), (3,7), (3,8), (3,9), (3,10), (3,11), (3,12), (4,-7), (4,-6), (4,-5), (4,-4), (4,-3), (4,-2), (4,-1), (4,0), (4,1), (4,2), (4,3), (4,4), (4,5), (4,6), (4,7)]
def spRawH608B2 : List qCell := [(4,8), (4,9), (4,10), (4,11), (4,12), (5,-6), (5,-5), (5,-4), (5,-3), (5,-2), (5,-1), (5,0), (5,1), (5,2), (5,3), (5,4), (5,5), (5,6), (5,7), (5,8), (5,9), (5,10), (5,11), (5,12), (6,-6), (6,-5), (6,-4), (6,-3), (6,-2), (6,-1), (6,0), (6,1), (6,2), (6,3), (6,4), (6,5), (6,6), (6,7), (6,8), (6,9), (6,10), (6,11), (6,12), (7,-4), (7,-3), (7,-2), (7,-1), (7,0), (7,1), (7,2), (7,3), (7,4), (7,5), (7,6), (7,7), (7,8), (7,9), (7,10), (8,-6), (8,-5), (8,-4), (8,-3), (8,-2), (8,-1), (8,0), (8,1), (8,2), (8,3), (8,4), (8,5), (8,6), (8,7), (8,8), (8,9), (8,10), (9,-6), (9,-5), (9,-4), (9,-3), (9,-2), (9,-1), (9,0), (9,1), (9,2), (9,3), (9,4), (9,5), (9,6), (9,7), (9,8), (9,9), (9,10), (10,-5), (10,-4), (10,-3), (10,-2), (10,-1), (10,0), (10,1), (10,2)]
def spRawH608B3 : List qCell := [(10,3), (10,4), (10,5), (10,6), (10,7), (10,8), (11,-6), (11,-5), (11,-4), (11,-3), (11,-2), (11,-1), (11,0), (11,1), (11,2), (11,3), (11,4), (11,5), (11,6), (11,7), (12,-4), (12,-3), (12,-2), (12,-1), (12,0), (12,1), (12,2), (12,3), (12,4), (12,5), (12,6), (12,7), (13,-4), (13,-3), (13,-2), (13,-1), (13,0), (13,1), (13,2), (13,3), (13,4), (14,-4), (14,-2), (14,-1), (14,0), (14,1), (14,2), (14,3), (14,4), (15,-2), (15,-1), (15,0), (16,-2), (16,0)]
def spRawH608 : List qCell := spRawH608B0 ++ spRawH608B1 ++ spRawH608B2 ++ spRawH608B3
def spRawH608_eq : qm608.H = spRawH608.toFinset := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      let l0 : List qCell := [(-9,-1),(-9,1),(-9,3),(-8,-1),(-8,0),(-8,1),(-8,2),(-8,3),(-7,-1),(-7,0),(-7,1),(-7,2),(-7,3),(-7,4),(-7,5),(-7,6),(-7,8),(-6,-3),(-6,-2),(-6,-1),(-6,0),(-6,1),(-6,2),(-6,3),(-6,4)]
      have hc0 : qf383 = l0.toFinset := by rfl
      let l1 : List qCell := [(-6,5),(-6,6),(-6,7),(-6,8),(-5,-2),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-5,8),(-5,9),(-5,10),(-5,11),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3)]
      have hc1 : qf384 = l1.toFinset := by rfl
      let l2 : List qCell := [(-4,4),(-4,5),(-4,6),(-4,7),(-4,8),(-4,9),(-4,10),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-3,10),(-3,11),(-3,12),(-3,13),(-2,-3),(-2,-1)]
      have hc2 : qf385 = l2.toFinset := by rfl
      let l3 : List qCell := [(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-2,11),(-2,12),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8)]
      have hc3 : qf386 = l3.toFinset := by rfl
      let l4 : List qCell := [(-1,9),(-1,10),(-1,11),(-1,12),(-1,13),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(1,-7),(1,-6),(1,-5)]
      have hc4 : qf387 = l4.toFinset := by rfl
      let l5 : List qCell := [(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(1,12),(1,13),(2,-7),(2,-6),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1)]
      have hc5 : qf388 = l5.toFinset := by rfl
      let l6 : List qCell := [(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(2,12),(2,13),(2,14),(3,-7),(3,-6),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2)]
      have hc6 : qf389 = l6.toFinset := by rfl
      let l7 : List qCell := [(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(3,12),(4,-7),(4,-6),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7)]
      have hc7 : qf390 = l7.toFinset := by rfl
      let l8 : List qCell := [(4,8),(4,9),(4,10),(4,11),(4,12),(5,-6),(5,-5),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(5,11),(5,12),(6,-6)]
      have hc8 : qf391 = l8.toFinset := by rfl
      let l9 : List qCell := [(6,-5),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(6,9),(6,10),(6,11),(6,12),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2)]
      have hc9 : qf392 = l9.toFinset := by rfl
      let l10 : List qCell := [(7,3),(7,4),(7,5),(7,6),(7,7),(7,8),(7,9),(7,10),(8,-6),(8,-5),(8,-4),(8,-3),(8,-2),(8,-1),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(8,7),(8,8),(8,9),(8,10)]
      have hc10 : qf393 = l10.toFinset := by rfl
      let l11 : List qCell := [(9,-6),(9,-5),(9,-4),(9,-3),(9,-2),(9,-1),(9,0),(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(9,7),(9,8),(9,9),(9,10),(10,-5),(10,-4),(10,-3),(10,-2),(10,-1),(10,0),(10,1),(10,2)]
      have hc11 : qf394 = l11.toFinset := by rfl
      let l12 : List qCell := [(10,3),(10,4),(10,5),(10,6),(10,7),(10,8),(11,-6),(11,-5),(11,-4),(11,-3),(11,-2),(11,-1),(11,0),(11,1),(11,2),(11,3),(11,4),(11,5),(11,6),(11,7),(12,-4),(12,-3),(12,-2),(12,-1),(12,0)]
      have hc12 : qf395 = l12.toFinset := by rfl
      let l13 : List qCell := [(12,1),(12,2),(12,3),(12,4),(12,5),(12,6),(12,7),(13,-4),(13,-3),(13,-2),(13,-1),(13,0),(13,1),(13,2),(13,3),(13,4),(14,-4),(14,-2),(14,-1),(14,0),(14,1),(14,2),(14,3),(14,4),(15,-2)]
      have hc13 : qf396 = l13.toFinset := by rfl
      let l14 : List qCell := [(15,-1),(15,0),(16,-2),(16,0)]
      have hc14 : qf397 = l14.toFinset := by rfl
      have hu1 := spUnionToFinset hc0 hc1
      have hu2 := spUnionToFinset hu1 hc2
      have hu3 := spUnionToFinset hu2 hc3
      have hu4 := spUnionToFinset hu3 hc4
      have hu5 := spUnionToFinset hu4 hc5
      have hu6 := spUnionToFinset hu5 hc6
      have hu7 := spUnionToFinset hu6 hc7
      have hu8 := spUnionToFinset hu7 hc8
      have hu9 := spUnionToFinset hu8 hc9
      have hu10 := spUnionToFinset hu9 hc10
      have hu11 := spUnionToFinset hu10 hc11
      have hu12 := spUnionToFinset hu11 hc12
      have hu13 := spUnionToFinset hu12 hc13
      have hu14 := spUnionToFinset hu13 hc14
      have hl : (((((((((((((((l0 ++ l1) ++ l2) ++ l3) ++ l4) ++ l5) ++ l6) ++ l7) ++ l8) ++ l9) ++ l10) ++ l11) ++ l12) ++ l13) ++ l14) : List qCell) = spRawH608 := by
        simp only [List.append_assoc]
        rfl
      change (qf383 ∪ qf384 ∪ qf385 ∪ qf386 ∪ qf387 ∪ qf388 ∪ qf389 ∪ qf390 ∪ qf391 ∪ qf392 ∪ qf393 ∪ qf394 ∪ qf395 ∪ qf396 ∪ qf397) = spRawH608.toFinset
      exact hu14.trans (congrArg List.toFinset hl))))
def spRawH610B0 : List qCell := [(-12,0), (-12,1), (-12,2), (-12,3), (-11,0), (-11,1), (-11,2), (-11,3), (-10,0), (-10,1), (-10,2), (-10,3), (-10,4), (-10,6), (-9,-2), (-9,-1), (-9,0), (-9,1), (-9,2), (-9,3), (-9,4), (-9,5), (-9,6), (-9,7), (-8,-2)]
def spRawH610B1 : List qCell := [(-8,-1), (-8,0), (-8,1), (-8,2), (-8,3), (-8,4), (-8,5), (-8,6), (-7,-2), (-7,-1), (-7,0), (-7,1), (-7,2), (-7,3), (-7,4), (-7,5), (-7,6), (-6,-2), (-6,-1), (-6,0), (-6,1), (-6,2), (-6,3), (-6,4), (-6,5)]
def spRawH610B2 : List qCell := [(-6,6), (-6,8), (-6,9), (-6,11), (-5,-1), (-5,0), (-5,1), (-5,2), (-5,3), (-5,4), (-5,5), (-5,6), (-5,7), (-5,8), (-5,9), (-5,10), (-5,11), (-4,-1), (-4,0), (-4,1), (-4,2), (-4,3), (-4,4), (-4,5), (-4,6)]
def spRawH610B3 : List qCell := [(-4,7), (-4,8), (-4,9), (-4,10), (-4,11), (-4,12), (-4,13), (-4,14), (-3,1), (-3,2), (-3,3), (-3,4), (-3,5), (-3,6), (-3,7), (-3,8), (-3,9), (-3,10), (-3,11), (-3,12), (-3,13), (-2,0), (-2,1), (-2,2), (-2,3)]
def spRawH610B4 : List qCell := [(-2,4), (-2,5), (-2,6), (-2,7), (-2,8), (-2,9), (-2,10), (-2,11), (-2,12), (-2,13), (-2,14), (-2,15), (-2,16), (-1,-5), (-1,-4), (-1,-3), (-1,-2), (-1,-1), (-1,0), (-1,2), (-1,3), (-1,4), (-1,5), (-1,6), (-1,7)]
def spRawH610B5 : List qCell := [(-1,8), (-1,9), (-1,10), (-1,11), (-1,12), (-1,13), (-1,14), (-1,15), (0,-5), (0,-4), (0,-3), (0,-2), (0,-1), (0,0), (0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (0,8), (0,9), (0,10), (0,11)]
def spRawH610B6 : List qCell := [(0,12), (0,13), (0,14), (0,15), (0,16), (1,-5), (1,-4), (1,-3), (1,-2), (1,-1), (1,0), (1,1), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (1,8), (1,9), (1,10), (1,11), (1,12), (1,13), (1,14)]
def spRawH610B7 : List qCell := [(2,-5), (2,-4), (2,-3), (2,-2), (2,-1), (2,0), (2,1), (2,2), (2,3), (2,4), (2,5), (2,6), (2,7), (2,8), (2,9), (2,10), (2,11), (2,12), (2,13), (2,14), (3,-3), (3,-2), (3,-1), (3,0), (3,1)]
def spRawH610B8 : List qCell := [(3,2), (3,3), (3,4), (3,5), (3,6), (3,7), (3,8), (3,9), (3,10), (3,11), (3,12), (3,13), (3,14), (4,-3), (4,-2), (4,-1), (4,0), (4,1), (4,2), (4,3), (4,4), (4,5), (4,6), (4,7), (4,8)]
def spRawH610B9 : List qCell := [(4,9), (4,10), (4,11), (4,12), (4,13), (4,14), (5,-3), (5,-2), (5,-1), (5,0), (5,1), (5,2), (5,3), (5,4), (5,5), (5,6), (5,7), (5,8), (5,9), (5,10), (5,11), (5,12), (6,-4), (6,-3), (6,-2)]
def spRawH610B10 : List qCell := [(6,-1), (6,0), (6,1), (6,2), (6,3), (6,4), (6,5), (6,6), (6,7), (6,8), (6,9), (6,10), (6,11), (6,12), (7,-4), (7,-3), (7,-2), (7,-1), (7,0), (7,1), (7,2), (7,3), (7,4), (7,5), (7,6)]
def spRawH610B11 : List qCell := [(7,7), (7,8), (7,9), (7,10), (7,11), (7,12), (8,-3), (8,-2), (8,-1), (8,0), (8,1), (8,2), (8,3), (8,4), (8,5), (8,6), (8,7), (8,8), (8,9), (8,10), (9,-4), (9,-3), (9,-2), (9,-1), (9,0)]
def spRawH610B12 : List qCell := [(9,1), (9,2), (9,3), (9,4), (9,5), (9,6), (9,7), (9,8), (9,9), (10,-2), (10,-1), (10,0), (10,1), (10,2), (10,3), (10,4), (10,5), (10,6), (10,7), (10,8), (10,9), (11,-2), (11,-1), (11,0), (11,1)]
def spRawH610B13 : List qCell := [(11,2), (11,3), (11,4), (11,5), (11,6), (12,-2), (12,0), (12,1), (12,2), (12,3), (12,4), (12,5), (12,6), (13,0), (13,1), (13,2), (14,0), (14,2)]
def spRawH610 : List qCell := spRawH610B0 ++ spRawH610B1 ++ spRawH610B2 ++ spRawH610B3 ++ spRawH610B4 ++ spRawH610B5 ++ spRawH610B6 ++ spRawH610B7 ++ spRawH610B8 ++ spRawH610B9 ++ spRawH610B10 ++ spRawH610B11 ++ spRawH610B12 ++ spRawH610B13
def spRawH610_eq : qm610.H = spRawH610.toFinset := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      let l0 : List qCell := [(-12,0),(-12,1),(-12,2),(-12,3),(-11,0),(-11,1),(-11,2),(-11,3),(-10,0),(-10,1),(-10,2),(-10,3),(-10,4),(-10,6),(-9,-2),(-9,-1),(-9,0),(-9,1),(-9,2),(-9,3),(-9,4),(-9,5),(-9,6),(-9,7),(-8,-2)]
      have hc0 : qf412 = l0.toFinset := by rfl
      let l1 : List qCell := [(-8,-1),(-8,0),(-8,1),(-8,2),(-8,3),(-8,4),(-8,5),(-8,6),(-7,-2),(-7,-1),(-7,0),(-7,1),(-7,2),(-7,3),(-7,4),(-7,5),(-7,6),(-6,-2),(-6,-1),(-6,0),(-6,1),(-6,2),(-6,3),(-6,4),(-6,5)]
      have hc1 : qf413 = l1.toFinset := by rfl
      let l2 : List qCell := [(-6,6),(-6,8),(-6,9),(-6,11),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-5,8),(-5,9),(-5,10),(-5,11),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6)]
      have hc2 : qf414 = l2.toFinset := by rfl
      let l3 : List qCell := [(-4,7),(-4,8),(-4,9),(-4,10),(-4,11),(-4,12),(-4,13),(-4,14),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-3,10),(-3,11),(-3,12),(-3,13),(-2,0),(-2,1),(-2,2),(-2,3)]
      have hc3 : qf415 = l3.toFinset := by rfl
      let l4 : List qCell := [(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9),(-2,10),(-2,11),(-2,12),(-2,13),(-2,14),(-2,15),(-2,16),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7)]
      have hc4 : qf416 = l4.toFinset := by rfl
      let l5 : List qCell := [(-1,8),(-1,9),(-1,10),(-1,11),(-1,12),(-1,13),(-1,14),(-1,15),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11)]
      have hc5 : qf417 = l5.toFinset := by rfl
      let l6 : List qCell := [(0,12),(0,13),(0,14),(0,15),(0,16),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(1,12),(1,13),(1,14)]
      have hc6 : qf418 = l6.toFinset := by rfl
      let l7 : List qCell := [(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(2,12),(2,13),(2,14),(3,-3),(3,-2),(3,-1),(3,0),(3,1)]
      have hc7 : qf419 = l7.toFinset := by rfl
      let l8 : List qCell := [(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(3,12),(3,13),(3,14),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8)]
      have hc8 : qf420 = l8.toFinset := by rfl
      let l9 : List qCell := [(4,9),(4,10),(4,11),(4,12),(4,13),(4,14),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(5,11),(5,12),(6,-4),(6,-3),(6,-2)]
      have hc9 : qf421 = l9.toFinset := by rfl
      let l10 : List qCell := [(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(6,9),(6,10),(6,11),(6,12),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6)]
      have hc10 : qf422 = l10.toFinset := by rfl
      let l11 : List qCell := [(7,7),(7,8),(7,9),(7,10),(7,11),(7,12),(8,-3),(8,-2),(8,-1),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(8,7),(8,8),(8,9),(8,10),(9,-4),(9,-3),(9,-2),(9,-1),(9,0)]
      have hc11 : qf423 = l11.toFinset := by rfl
      let l12 : List qCell := [(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(9,7),(9,8),(9,9),(10,-2),(10,-1),(10,0),(10,1),(10,2),(10,3),(10,4),(10,5),(10,6),(10,7),(10,8),(10,9),(11,-2),(11,-1),(11,0),(11,1)]
      have hc12 : qf424 = l12.toFinset := by rfl
      let l13 : List qCell := [(11,2),(11,3),(11,4),(11,5),(11,6),(12,-2),(12,0),(12,1),(12,2),(12,3),(12,4),(12,5),(12,6),(13,0),(13,1),(13,2),(14,0),(14,2)]
      have hc13 : qf425 = l13.toFinset := by rfl
      have hu1 := spUnionToFinset hc0 hc1
      have hu2 := spUnionToFinset hu1 hc2
      have hu3 := spUnionToFinset hu2 hc3
      have hu4 := spUnionToFinset hu3 hc4
      have hu5 := spUnionToFinset hu4 hc5
      have hu6 := spUnionToFinset hu5 hc6
      have hu7 := spUnionToFinset hu6 hc7
      have hu8 := spUnionToFinset hu7 hc8
      have hu9 := spUnionToFinset hu8 hc9
      have hu10 := spUnionToFinset hu9 hc10
      have hu11 := spUnionToFinset hu10 hc11
      have hu12 := spUnionToFinset hu11 hc12
      have hu13 := spUnionToFinset hu12 hc13
      have hl : ((((((((((((((l0 ++ l1) ++ l2) ++ l3) ++ l4) ++ l5) ++ l6) ++ l7) ++ l8) ++ l9) ++ l10) ++ l11) ++ l12) ++ l13) : List qCell) = spRawH610 := by
        simp only [List.append_assoc]
        rfl
      change (qf412 ∪ qf413 ∪ qf414 ∪ qf415 ∪ qf416 ∪ qf417 ∪ qf418 ∪ qf419 ∪ qf420 ∪ qf421 ∪ qf422 ∪ qf423 ∪ qf424 ∪ qf425) = spRawH610.toFinset
      exact hu13.trans (congrArg List.toFinset hl))))
def spRawH614 : List qCell := ql614
def spRawH614_eq : qm614.H = spRawH614.toFinset := by
  set_option maxRecDepth 100000 in
    exact qrowH_list ql614 qn614
def sp614Pl0 : List qCell := spRawH608.map (qplacement (qT.rotation ⟨608,1,7,5⟩) (qT.shift ⟨608,1,7,5⟩))
def sp614Pl1 : List qCell := spRawH543.map (qplacement (qT.rotation ⟨543,3,5,6⟩) (qT.shift ⟨543,3,5,6⟩))
def sp614Pl2 : List qCell := spRawH370.map (qplacement (qT.rotation ⟨370,6,3,4⟩) (qT.shift ⟨370,6,3,4⟩))
def sp614Pl3 : List qCell := spRawH392.map (qplacement (qT.rotation ⟨392,7,3,4⟩) (qT.shift ⟨392,7,3,4⟩))
def sp614Pl4 : List qCell := spRawH610.map (qplacement (qT.rotation ⟨610,3,5,6⟩) (qT.shift ⟨610,3,5,6⟩))
def sp614Pl5 : List qCell := spRawH600.map (qplacement (qT.rotation ⟨600,0,6,4⟩) (qT.shift ⟨600,0,6,4⟩))
def sp614Pl6 : List qCell := spRawH613.map (qplacement (qT.rotation ⟨613,0,6,4⟩) (qT.shift ⟨613,0,6,4⟩))
def sp614Combined : List qCell := qorigin :: (sp614Pl0 ++ sp614Pl1 ++ sp614Pl2 ++ sp614Pl3 ++ sp614Pl4 ++ sp614Pl5 ++ sp614Pl6)
def sp614Combined_canonical : qcanonical sp614Combined = spRawH614 := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| decide +kernel))
def sp614HSemantics : insert qorigin (qunionH [qplaceRow ⟨608,1,7,5⟩ qm608,qplaceRow ⟨543,3,5,6⟩ qm543,qplaceRow ⟨370,6,3,4⟩ qm370,qplaceRow ⟨392,7,3,4⟩ qm392,qplaceRow ⟨610,3,5,6⟩ qm610,qplaceRow ⟨600,0,6,4⟩ qm600,qplaceRow ⟨613,0,6,4⟩ qm613]) = sp614Combined.toFinset := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      have hp0 : (qplaceRow ⟨608,1,7,5⟩ qm608).H = sp614Pl0.toFinset :=
        spPlacedH_list ⟨608,1,7,5⟩ qm608 spRawH608 spRawH608_eq
      have hp1 : (qplaceRow ⟨543,3,5,6⟩ qm543).H = sp614Pl1.toFinset :=
        spPlacedH_list ⟨543,3,5,6⟩ qm543 spRawH543 spRawH543_eq
      have hp2 : (qplaceRow ⟨370,6,3,4⟩ qm370).H = sp614Pl2.toFinset :=
        spPlacedH_list ⟨370,6,3,4⟩ qm370 spRawH370 spRawH370_eq
      have hp3 : (qplaceRow ⟨392,7,3,4⟩ qm392).H = sp614Pl3.toFinset :=
        spPlacedH_list ⟨392,7,3,4⟩ qm392 spRawH392 spRawH392_eq
      have hp4 : (qplaceRow ⟨610,3,5,6⟩ qm610).H = sp614Pl4.toFinset :=
        spPlacedH_list ⟨610,3,5,6⟩ qm610 spRawH610 spRawH610_eq
      have hp5 : (qplaceRow ⟨600,0,6,4⟩ qm600).H = sp614Pl5.toFinset :=
        spPlacedH_list ⟨600,0,6,4⟩ qm600 spRawH600 spRawH600_eq
      have hp6 : (qplaceRow ⟨613,0,6,4⟩ qm613).H = sp614Pl6.toFinset :=
        spPlacedH_list ⟨613,0,6,4⟩ qm613 spRawH613 spRawH613_eq
      have hu : qunionH [qplaceRow ⟨608,1,7,5⟩ qm608,qplaceRow ⟨543,3,5,6⟩ qm543,qplaceRow ⟨370,6,3,4⟩ qm370,qplaceRow ⟨392,7,3,4⟩ qm392,qplaceRow ⟨610,3,5,6⟩ qm610,qplaceRow ⟨600,0,6,4⟩ qm600,qplaceRow ⟨613,0,6,4⟩ qm613] = ([sp614Pl0,sp614Pl1,sp614Pl2,sp614Pl3,sp614Pl4,sp614Pl5,sp614Pl6] : List (List qCell)).flatten.toFinset := by
        apply qlist_unionH
        exact (congrArg₂ List.cons hp0 (congrArg₂ List.cons hp1 (congrArg₂ List.cons hp2 (congrArg₂ List.cons hp3 (congrArg₂ List.cons hp4 (congrArg₂ List.cons hp5 (congrArg₂ List.cons hp6 (rfl : ([] : List (Finset qCell)) = []))))))))
      rw [hu]
      simp only [sp614Combined,List.flatten_cons,List.flatten_nil,List.append_nil,List.toFinset_cons,List.append_assoc])))
def sp614H : (qforkRow [qplaceRow ⟨608,1,7,5⟩ qm608,qplaceRow ⟨543,3,5,6⟩ qm543,qplaceRow ⟨370,6,3,4⟩ qm370,qplaceRow ⟨392,7,3,4⟩ qm392,qplaceRow ⟨610,3,5,6⟩ qm610,qplaceRow ⟨600,0,6,4⟩ qm600,qplaceRow ⟨613,0,6,4⟩ qm613]).H = qm614.H := by
  set_option maxRecDepth 100000 in
    change insert qorigin (qunionH [qplaceRow ⟨608,1,7,5⟩ qm608,qplaceRow ⟨543,3,5,6⟩ qm543,qplaceRow ⟨370,6,3,4⟩ qm370,qplaceRow ⟨392,7,3,4⟩ qm392,qplaceRow ⟨610,3,5,6⟩ qm610,qplaceRow ⟨600,0,6,4⟩ qm600,qplaceRow ⟨613,0,6,4⟩ qm613]) = qm614.H
    rw [sp614HSemantics,spRawH614_eq]
    exact qlist_H_target sp614Combined spRawH614 sp614Combined_canonical
def sp614S0 : Finset qCell := {(-5,-2),(-4,-2),(-4,1),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,1),(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(0,-1),(0,0),(1,0),(1,1),(1,2),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,1)}
def sp614Step0 : (qplaceRow ⟨370,6,3,4⟩ qm370).H ⊆ sp614S0 := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      have h : ∀ b ∈ spRawH370.map (qplacement (qT.rotation ⟨370,6,3,4⟩) (qT.shift ⟨370,6,3,4⟩)),b ∈ sp614S0 := by decide +kernel
      intro b hm
      exact h b ((spPlacedH_mem ⟨370,6,3,4⟩ qm370 spRawH370 spRawH370_eq b).mp hm))))
def sp614S1 : Finset qCell := {(-4,1),(-3,-1),(-3,1),(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(0,-1),(0,0),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,1)}
def sp614Step1 : ∀ b ∈ sp614S0,b ∈ (qplaceRow ⟨392,7,3,4⟩ qm392).H → b ∈ sp614S1 := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      have h : ∀ b ∈ sp614S0,b ∈ spRawH392.map (qplacement (qT.rotation ⟨392,7,3,4⟩) (qT.shift ⟨392,7,3,4⟩)) → b ∈ sp614S1 := by decide +kernel
      intro b hb hm
      exact h b hb ((spPlacedH_mem ⟨392,7,3,4⟩ qm392 spRawH392 spRawH392_eq b).mp hm))))
def sp614S2 : Finset qCell := {(-4,1),(-3,-1),(-3,1),(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-1,-2),(-1,-1),(-1,0),(-1,1),(0,-1),(0,0),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0)}
def sp614Step2 : ∀ b ∈ sp614S1,b ∈ (qplaceRow ⟨543,3,5,6⟩ qm543).H → b ∈ sp614S2 := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      have h : ∀ b ∈ sp614S1,b ∈ spRawH543.map (qplacement (qT.rotation ⟨543,3,5,6⟩) (qT.shift ⟨543,3,5,6⟩)) → b ∈ sp614S2 := by decide +kernel
      intro b hb hm
      exact h b hb ((spPlacedH_mem ⟨543,3,5,6⟩ qm543 spRawH543 spRawH543_eq b).mp hm))))
def sp614S3 : Finset qCell := {(-3,-1),(-3,1),(-2,-3),(-2,-1),(-2,0),(-2,1),(-1,-2),(-1,-1),(-1,0),(-1,1),(0,0),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0)}
def sp614Step3 : ∀ b ∈ sp614S2,b ∈ (qplaceRow ⟨600,0,6,4⟩ qm600).H → b ∈ sp614S3 := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      have h : ∀ b ∈ sp614S2,b ∈ spRawH600.map (qplacement (qT.rotation ⟨600,0,6,4⟩) (qT.shift ⟨600,0,6,4⟩)) → b ∈ sp614S3 := by decide +kernel
      intro b hb hm
      exact h b hb ((spPlacedH_mem ⟨600,0,6,4⟩ qm600 spRawH600 spRawH600_eq b).mp hm))))
def sp614S4 : Finset qCell := {(-3,-1),(-3,1),(-2,-3),(-2,-1),(-2,0),(-2,1),(-1,-2),(-1,-1),(-1,0),(-1,1),(0,0),(1,0),(1,1),(2,1)}
def sp614Step4 : ∀ b ∈ sp614S3,b ∈ (qplaceRow ⟨610,3,5,6⟩ qm610).H → b ∈ sp614S4 := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      have h : ∀ b ∈ sp614S3,b ∈ spRawH610.map (qplacement (qT.rotation ⟨610,3,5,6⟩) (qT.shift ⟨610,3,5,6⟩)) → b ∈ sp614S4 := by decide +kernel
      intro b hb hm
      exact h b hb ((spPlacedH_mem ⟨610,3,5,6⟩ qm610 spRawH610 spRawH610_eq b).mp hm))))
def sp614S5 : Finset qCell := {(0,0),(1,0),(1,1),(2,1)}
def sp614Step5 : ∀ b ∈ sp614S4,b ∈ (qplaceRow ⟨608,1,7,5⟩ qm608).H → b ∈ sp614S5 := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      have h : ∀ b ∈ sp614S4,b ∈ spRawH608.map (qplacement (qT.rotation ⟨608,1,7,5⟩) (qT.shift ⟨608,1,7,5⟩)) → b ∈ sp614S5 := by decide +kernel
      intro b hb hm
      exact h b hb ((spPlacedH_mem ⟨608,1,7,5⟩ qm608 spRawH608 spRawH608_eq b).mp hm))))
def sp614S6 : Finset qCell := {(0,0),(1,0),(1,1)}
def sp614Step6 : ∀ b ∈ sp614S5,b ∈ (qplaceRow ⟨613,0,6,4⟩ qm613).H → b ∈ sp614S6 := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      have h : ∀ b ∈ sp614S5,b ∈ spRawH613.map (qplacement (qT.rotation ⟨613,0,6,4⟩) (qT.shift ⟨613,0,6,4⟩)) → b ∈ sp614S6 := by decide +kernel
      intro b hb hm
      exact h b hb ((spPlacedH_mem ⟨613,0,6,4⟩ qm613 spRawH613 spRawH613_eq b).mp hm))))
def sp614Bound : qcommonH [qplaceRow ⟨608,1,7,5⟩ qm608,qplaceRow ⟨543,3,5,6⟩ qm543,qplaceRow ⟨370,6,3,4⟩ qm370,qplaceRow ⟨392,7,3,4⟩ qm392,qplaceRow ⟨610,3,5,6⟩ qm610,qplaceRow ⟨600,0,6,4⟩ qm600,qplaceRow ⟨613,0,6,4⟩ qm613] ⊆ insert qorigin ({(1,0),(1,1)} : Finset qCell) := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      intro b hb
      have h0 := sp614Step0 (qcommonH_le_at [qplaceRow ⟨608,1,7,5⟩ qm608,qplaceRow ⟨543,3,5,6⟩ qm543,qplaceRow ⟨370,6,3,4⟩ qm370,qplaceRow ⟨392,7,3,4⟩ qm392,qplaceRow ⟨610,3,5,6⟩ qm610,qplaceRow ⟨600,0,6,4⟩ qm600,qplaceRow ⟨613,0,6,4⟩ qm613] 2 (qplaceRow ⟨370,6,3,4⟩ qm370) rfl hb)
      have h1 := sp614Step1 b h0 (qcommonH_le_at [qplaceRow ⟨608,1,7,5⟩ qm608,qplaceRow ⟨543,3,5,6⟩ qm543,qplaceRow ⟨370,6,3,4⟩ qm370,qplaceRow ⟨392,7,3,4⟩ qm392,qplaceRow ⟨610,3,5,6⟩ qm610,qplaceRow ⟨600,0,6,4⟩ qm600,qplaceRow ⟨613,0,6,4⟩ qm613] 3 (qplaceRow ⟨392,7,3,4⟩ qm392) rfl hb)
      have h2 := sp614Step2 b h1 (qcommonH_le_at [qplaceRow ⟨608,1,7,5⟩ qm608,qplaceRow ⟨543,3,5,6⟩ qm543,qplaceRow ⟨370,6,3,4⟩ qm370,qplaceRow ⟨392,7,3,4⟩ qm392,qplaceRow ⟨610,3,5,6⟩ qm610,qplaceRow ⟨600,0,6,4⟩ qm600,qplaceRow ⟨613,0,6,4⟩ qm613] 1 (qplaceRow ⟨543,3,5,6⟩ qm543) rfl hb)
      have h3 := sp614Step3 b h2 (qcommonH_le_at [qplaceRow ⟨608,1,7,5⟩ qm608,qplaceRow ⟨543,3,5,6⟩ qm543,qplaceRow ⟨370,6,3,4⟩ qm370,qplaceRow ⟨392,7,3,4⟩ qm392,qplaceRow ⟨610,3,5,6⟩ qm610,qplaceRow ⟨600,0,6,4⟩ qm600,qplaceRow ⟨613,0,6,4⟩ qm613] 5 (qplaceRow ⟨600,0,6,4⟩ qm600) rfl hb)
      have h4 := sp614Step4 b h3 (qcommonH_le_at [qplaceRow ⟨608,1,7,5⟩ qm608,qplaceRow ⟨543,3,5,6⟩ qm543,qplaceRow ⟨370,6,3,4⟩ qm370,qplaceRow ⟨392,7,3,4⟩ qm392,qplaceRow ⟨610,3,5,6⟩ qm610,qplaceRow ⟨600,0,6,4⟩ qm600,qplaceRow ⟨613,0,6,4⟩ qm613] 4 (qplaceRow ⟨610,3,5,6⟩ qm610) rfl hb)
      have h5 := sp614Step5 b h4 (qcommonH_le_at [qplaceRow ⟨608,1,7,5⟩ qm608,qplaceRow ⟨543,3,5,6⟩ qm543,qplaceRow ⟨370,6,3,4⟩ qm370,qplaceRow ⟨392,7,3,4⟩ qm392,qplaceRow ⟨610,3,5,6⟩ qm610,qplaceRow ⟨600,0,6,4⟩ qm600,qplaceRow ⟨613,0,6,4⟩ qm613] 0 (qplaceRow ⟨608,1,7,5⟩ qm608) rfl hb)
      have h6 := sp614Step6 b h5 (qcommonH_le_at [qplaceRow ⟨608,1,7,5⟩ qm608,qplaceRow ⟨543,3,5,6⟩ qm543,qplaceRow ⟨370,6,3,4⟩ qm370,qplaceRow ⟨392,7,3,4⟩ qm392,qplaceRow ⟨610,3,5,6⟩ qm610,qplaceRow ⟨600,0,6,4⟩ qm600,qplaceRow ⟨613,0,6,4⟩ qm613] 6 (qplaceRow ⟨613,0,6,4⟩ qm613) rfl hb)
      exact (show sp614S6 ⊆ insert qorigin ({(1,0),(1,1)} : Finset qCell) by decide +kernel) h6)))
def sp614A : (qforkRow [qplaceRow ⟨608,1,7,5⟩ qm608,qplaceRow ⟨543,3,5,6⟩ qm543,qplaceRow ⟨370,6,3,4⟩ qm370,qplaceRow ⟨392,7,3,4⟩ qm392,qplaceRow ⟨610,3,5,6⟩ qm610,qplaceRow ⟨600,0,6,4⟩ qm600,qplaceRow ⟨613,0,6,4⟩ qm613]).A = ({(1,0),(1,1)} : Finset qCell) := by
  set_option maxRecDepth 100000 in
    run_tac qhb (← `(tactic| (
      change (qunionA [qplaceRow ⟨608,1,7,5⟩ qm608,qplaceRow ⟨543,3,5,6⟩ qm543,qplaceRow ⟨370,6,3,4⟩ qm370,qplaceRow ⟨392,7,3,4⟩ qm392,qplaceRow ⟨610,3,5,6⟩ qm610,qplaceRow ⟨600,0,6,4⟩ qm600,qplaceRow ⟨613,0,6,4⟩ qm613] ∪ qcommonH [qplaceRow ⟨608,1,7,5⟩ qm608,qplaceRow ⟨543,3,5,6⟩ qm543,qplaceRow ⟨370,6,3,4⟩ qm370,qplaceRow ⟨392,7,3,4⟩ qm392,qplaceRow ⟨610,3,5,6⟩ qm610,qplaceRow ⟨600,0,6,4⟩ qm600,qplaceRow ⟨613,0,6,4⟩ qm613]).erase qorigin = ({(1,0),(1,1)} : Finset qCell)
      apply erase_union_eq_of_left_subset
      · decide +kernel
      · exact sp614Bound
      · decide +kernel
      · decide +kernel)))
def qmeq_614 : qr 614 = qm614 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 614 = qv614 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 614 < 6 by decide,↓reduceDIte,he,qv614,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_370,qmeq_392,qmeq_543,qmeq_600,qmeq_608,qmeq_610,qmeq_613]
          apply qx
          · exact sp614A
          · exact sp614H
          · run_tac qhb (← `(tactic| decide +kernel)))))
def ql615b0 : List qCell := [(-15,0),(-15,2),(-14,0),(-14,1),(-14,2),(-13,-4),(-13,-3),(-13,-2),(-13,-1),(-13,0),(-13,1),(-13,2),(-13,3),(-13,4),(-12,-5),(-12,-4),(-12,-3),(-12,-2),(-12,-1),(-12,0),(-12,1),(-12,2),(-12,3),(-12,4),(-12,5)]
def ql615b1 : List qCell := [(-11,-5),(-11,-4),(-11,-3),(-11,-2),(-11,-1),(-11,0),(-11,1),(-11,2),(-11,3),(-11,4),(-11,5),(-10,-9),(-10,-8),(-10,-7),(-10,-6),(-10,-5),(-10,-4),(-10,-3),(-10,-2),(-10,-1),(-10,0),(-10,1),(-10,2),(-10,3),(-10,4)]
def ql615b2 : List qCell := [(-10,5),(-10,6),(-10,7),(-10,8),(-10,9),(-9,-9),(-9,-8),(-9,-7),(-9,-6),(-9,-5),(-9,-4),(-9,-3),(-9,-2),(-9,-1),(-9,0),(-9,1),(-9,2),(-9,3),(-9,4),(-9,5),(-9,6),(-9,7),(-9,8),(-9,9),(-8,-10)]
def ql615b3 : List qCell := [(-8,-9),(-8,-8),(-8,-7),(-8,-6),(-8,-5),(-8,-4),(-8,-3),(-8,-2),(-8,-1),(-8,0),(-8,1),(-8,2),(-8,3),(-8,4),(-8,5),(-8,6),(-8,7),(-8,8),(-8,9),(-8,10),(-7,-11),(-7,-10),(-7,-9),(-7,-8),(-7,-7)]
def ql615b4 : List qCell := [(-7,-6),(-7,-5),(-7,-4),(-7,-3),(-7,-2),(-7,-1),(-7,0),(-7,1),(-7,2),(-7,3),(-7,4),(-7,5),(-7,6),(-7,7),(-7,8),(-7,9),(-7,10),(-7,11),(-6,-11),(-6,-10),(-6,-9),(-6,-8),(-6,-7),(-6,-6),(-6,-5)]
def ql615b5 : List qCell := [(-6,-4),(-6,-3),(-6,-2),(-6,-1),(-6,0),(-6,1),(-6,2),(-6,3),(-6,4),(-6,5),(-6,6),(-6,7),(-6,8),(-6,9),(-6,10),(-6,11),(-5,-12),(-5,-11),(-5,-10),(-5,-9),(-5,-8),(-5,-7),(-5,-6),(-5,-5),(-5,-4)]
def ql615b6 : List qCell := [(-5,-3),(-5,-2),(-5,-1),(-5,0),(-5,1),(-5,2),(-5,3),(-5,4),(-5,5),(-5,6),(-5,7),(-5,8),(-5,9),(-5,10),(-5,11),(-5,12),(-4,-14),(-4,-13),(-4,-12),(-4,-11),(-4,-10),(-4,-9),(-4,-8),(-4,-7),(-4,-6)]
def ql615b7 : List qCell := [(-4,-5),(-4,-4),(-4,-3),(-4,-2),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-4,6),(-4,7),(-4,8),(-4,9),(-4,10),(-4,11),(-4,12),(-4,13),(-4,14),(-3,-14),(-3,-13),(-3,-12),(-3,-11),(-3,-10)]
def ql615b8 : List qCell := [(-3,-9),(-3,-8),(-3,-7),(-3,-6),(-3,-5),(-3,-4),(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-3,7),(-3,8),(-3,9),(-3,10),(-3,11),(-3,12),(-3,13),(-3,14),(-2,-16)]
def ql615b9 : List qCell := [(-2,-15),(-2,-14),(-2,-13),(-2,-12),(-2,-11),(-2,-10),(-2,-9),(-2,-8),(-2,-7),(-2,-6),(-2,-5),(-2,-4),(-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-2,6),(-2,7),(-2,8),(-2,9)]
def ql615b10 : List qCell := [(-2,10),(-2,11),(-2,12),(-2,13),(-2,14),(-2,15),(-2,16),(-1,-15),(-1,-14),(-1,-13),(-1,-12),(-1,-11),(-1,-10),(-1,-9),(-1,-8),(-1,-7),(-1,-6),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2)]
def ql615b11 : List qCell := [(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(-1,8),(-1,9),(-1,10),(-1,11),(-1,12),(-1,13),(-1,14),(-1,15),(0,-16),(0,-15),(0,-14),(0,-13),(0,-12),(0,-11),(0,-10),(0,-9),(0,-8),(0,-7),(0,-6),(0,-5)]
def ql615b12 : List qCell := [(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(0,15),(0,16),(1,-15),(1,-14),(1,-13),(1,-12)]
def ql615b13 : List qCell := [(1,-11),(1,-10),(1,-9),(1,-8),(1,-7),(1,-6),(1,-5),(1,-4),(1,-3),(1,-2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(1,12),(1,13),(1,14)]
def ql615b14 : List qCell := [(1,15),(1,16),(2,-16),(2,-15),(2,-14),(2,-13),(2,-12),(2,-11),(2,-10),(2,-9),(2,-8),(2,-7),(2,-6),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)]
def ql615b15 : List qCell := [(2,7),(2,8),(2,9),(2,10),(2,11),(2,12),(2,13),(2,14),(2,15),(2,16),(3,-14),(3,-13),(3,-12),(3,-11),(3,-10),(3,-9),(3,-8),(3,-7),(3,-6),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0)]
def ql615b16 : List qCell := [(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(3,12),(3,13),(3,14),(3,15),(3,16),(4,-14),(4,-13),(4,-12),(4,-11),(4,-10),(4,-9),(4,-8),(4,-7),(4,-6)]
def ql615b17 : List qCell := [(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(4,10),(4,11),(4,12),(4,13),(4,14),(5,-14),(5,-13),(5,-12),(5,-11),(5,-10)]
def ql615b18 : List qCell := [(5,-9),(5,-8),(5,-7),(5,-6),(5,-5),(5,-4),(5,-3),(5,-2),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(5,11),(5,12),(5,13),(5,14),(6,-14)]
def ql615b19 : List qCell := [(6,-13),(6,-12),(6,-11),(6,-10),(6,-9),(6,-8),(6,-7),(6,-6),(6,-5),(6,-4),(6,-3),(6,-2),(6,-1),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(6,9),(6,10),(6,11)]
def ql615b20 : List qCell := [(6,12),(6,13),(6,14),(7,-12),(7,-11),(7,-10),(7,-9),(7,-8),(7,-7),(7,-6),(7,-5),(7,-4),(7,-3),(7,-2),(7,-1),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(7,8),(7,9)]
def ql615b21 : List qCell := [(7,10),(7,11),(7,12),(7,13),(7,14),(8,-12),(8,-11),(8,-10),(8,-9),(8,-8),(8,-7),(8,-6),(8,-5),(8,-4),(8,-3),(8,-2),(8,-1),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(8,7)]
def ql615b22 : List qCell := [(8,8),(8,9),(8,10),(8,11),(8,12),(9,-12),(9,-11),(9,-10),(9,-9),(9,-8),(9,-7),(9,-6),(9,-5),(9,-4),(9,-3),(9,-2),(9,-1),(9,0),(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(9,7)]
def ql615b23 : List qCell := [(9,8),(9,9),(9,10),(9,11),(9,12),(10,-10),(10,-9),(10,-8),(10,-7),(10,-6),(10,-5),(10,-4),(10,-3),(10,-2),(10,-1),(10,0),(10,1),(10,2),(10,3),(10,4),(10,5),(10,6),(10,7),(10,8),(10,9)]
def ql615b24 : List qCell := [(10,10),(10,11),(10,12),(11,-9),(11,-8),(11,-7),(11,-6),(11,-5),(11,-4),(11,-3),(11,-2),(11,-1),(11,0),(11,1),(11,2),(11,3),(11,4),(11,5),(11,6),(11,7),(11,8),(11,9),(11,10),(12,-9),(12,-8)]
def ql615b25 : List qCell := [(12,-7),(12,-6),(12,-5),(12,-4),(12,-3),(12,-2),(12,-1),(12,0),(12,1),(12,2),(12,3),(12,4),(12,5),(12,6),(12,7),(12,8),(12,9),(13,-6),(13,-5),(13,-4),(13,-3),(13,-2),(13,-1),(13,0),(13,1)]
def ql615b26 : List qCell := [(13,2),(13,3),(13,4),(13,5),(13,6),(13,7),(13,8),(13,9),(14,-6),(14,-5),(14,-4),(14,-3),(14,-2),(14,-1),(14,0),(14,1),(14,2),(14,3),(14,4),(14,5),(14,6),(15,-2),(15,-1),(15,0),(15,1)]
def ql615b27 : List qCell := [(15,2),(15,3),(15,4),(15,5),(15,6),(16,-2),(16,0),(16,1),(16,2),(17,0),(17,2)]
def ql615 : List qCell := ql615b0 ++ ql615b1 ++ ql615b2 ++ ql615b3 ++ ql615b4 ++ ql615b5 ++ ql615b6 ++ ql615b7 ++ ql615b8 ++ ql615b9 ++ ql615b10 ++ ql615b11 ++ ql615b12 ++ ql615b13 ++ ql615b14 ++ ql615b15 ++ ql615b16 ++ ql615b17 ++ ql615b18 ++ ql615b19 ++ ql615b20 ++ ql615b21 ++ ql615b22 ++ ql615b23 ++ ql615b24 ++ ql615b25 ++ ql615b26 ++ ql615b27
lemma qn615 : (ql615).Nodup := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qm615 : qR := ⟨{(1,0)},⟨(ql615 : Multiset qCell), Multiset.coe_nodup.mpr qn615⟩,34⟩
def qhbCanonical (t : Lean.Syntax) : Lean.Elab.Tactic.TacticM Unit :=
  Lean.withOptions (fun o => Lean.maxHeartbeats.set o 0) <|
    withTheReader Lean.Core.Context (fun c => { c with maxHeartbeats := 0 }) (Lean.Elab.Tactic.evalTactic t)
def qpl0 : List qCell := ql602.map (qplacement (qT.rotation ⟨602,7,6,4⟩) (qT.shift ⟨602,7,6,4⟩))
def qpl1 : List qCell := ql614.map (qplacement (qT.rotation ⟨614,1,4,3⟩) (qT.shift ⟨614,1,4,3⟩))
def qpl2 : List qCell := ql533.map (qplacement (qT.rotation ⟨533,5,6,4⟩) (qT.shift ⟨533,5,6,4⟩))
def qpl3 : List qCell := ql590.map (qplacement (qT.rotation ⟨590,7,6,4⟩) (qT.shift ⟨590,7,6,4⟩))
def qpl4 : List qCell := ql611.map (qplacement (qT.rotation ⟨611,6,3,4⟩) (qT.shift ⟨611,6,3,4⟩))
def qpl5 : List qCell := ql587.map (qplacement (qT.rotation ⟨587,3,3,4⟩) (qT.shift ⟨587,3,3,4⟩))
def qpl6 : List qCell := ql601.map (qplacement (qT.rotation ⟨601,5,6,4⟩) (qT.shift ⟨601,5,6,4⟩))
def qpl7 : List qCell := ql406.map (qplacement (qT.rotation ⟨406,1,6,4⟩) (qT.shift ⟨406,1,6,4⟩))
def qpl8 : List qCell := ql591.map (qplacement (qT.rotation ⟨591,3,3,4⟩) (qT.shift ⟨591,3,3,4⟩))
def qpl9 : List qCell := ql586.map (qplacement (qT.rotation ⟨586,3,3,4⟩) (qT.shift ⟨586,3,3,4⟩))
def qpl10 : List qCell := ql584.map (qplacement (qT.rotation ⟨584,5,6,4⟩) (qT.shift ⟨584,5,6,4⟩))
def qpl11 : List qCell := ql406.map (qplacement (qT.rotation ⟨406,3,3,4⟩) (qT.shift ⟨406,3,3,4⟩))
def qcombined : List qCell := qorigin :: (qpl0 ++ qpl1 ++ qpl2 ++ qpl3 ++ qpl4 ++ qpl5 ++ qpl6 ++ qpl7 ++ qpl8 ++ qpl9 ++ qpl10 ++ qpl11)
def qcombined_canonical : qcanonical qcombined = ql615 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhbCanonical (← `(tactic| decide +kernel))
def qhbSem (t : Lean.Syntax) : Lean.Elab.Tactic.TacticM Unit := Lean.withOptions (fun o => Lean.maxHeartbeats.set o 0) (withTheReader Lean.Core.Context (fun c => { c with maxHeartbeats := 0 }) (Lean.Elab.Tactic.evalTactic t))
def qm406_H_list : qm406.H = ql406.toFinset := by exact qrowH_list ql406 qn406
def qm533_H_list : qm533.H = ql533.toFinset := by exact qrowH_list ql533 qn533
def qm584_H_list : qm584.H = ql584.toFinset := by exact qrowH_list ql584 qn584
def qm586_H_list : qm586.H = ql586.toFinset := by exact qrowH_list ql586 qn586
def qm587_H_list : qm587.H = ql587.toFinset := by exact qrowH_list ql587 qn587
def qm590_H_list : qm590.H = ql590.toFinset := by exact qrowH_list ql590 qn590
def qm591_H_list : qm591.H = ql591.toFinset := by exact qrowH_list ql591 qn591
def qm601_H_list : qm601.H = ql601.toFinset := by exact qrowH_list ql601 qn601
def qm602_H_list : qm602.H = ql602.toFinset := by exact qrowH_list ql602 qn602
def qm611_H_list : qm611.H = ql611.toFinset := by exact qrowH_list ql611 qn611
def qm614_H_list : qm614.H = ql614.toFinset := by exact qrowH_list ql614 qn614
def qm615_H_list : qm615.H = ql615.toFinset := by exact qrowH_list ql615 qn615
def qcombined_H_semantics : insert qorigin (qunionH [qplaceRow ⟨602,7,6,4⟩ qm602,qplaceRow ⟨614,1,4,3⟩ qm614,qplaceRow ⟨533,5,6,4⟩ qm533,qplaceRow ⟨590,7,6,4⟩ qm590,qplaceRow ⟨611,6,3,4⟩ qm611,qplaceRow ⟨587,3,3,4⟩ qm587,qplaceRow ⟨601,5,6,4⟩ qm601,qplaceRow ⟨406,1,6,4⟩ qm406,qplaceRow ⟨591,3,3,4⟩ qm591,qplaceRow ⟨586,3,3,4⟩ qm586,qplaceRow ⟨584,5,6,4⟩ qm584,qplaceRow ⟨406,3,3,4⟩ qm406]) = qcombined.toFinset := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhbSem (← `(tactic| (
        have hu : qunionH [qplaceRow ⟨602,7,6,4⟩ qm602,qplaceRow ⟨614,1,4,3⟩ qm614,qplaceRow ⟨533,5,6,4⟩ qm533,qplaceRow ⟨590,7,6,4⟩ qm590,qplaceRow ⟨611,6,3,4⟩ qm611,qplaceRow ⟨587,3,3,4⟩ qm587,qplaceRow ⟨601,5,6,4⟩ qm601,qplaceRow ⟨406,1,6,4⟩ qm406,qplaceRow ⟨591,3,3,4⟩ qm591,qplaceRow ⟨586,3,3,4⟩ qm586,qplaceRow ⟨584,5,6,4⟩ qm584,qplaceRow ⟨406,3,3,4⟩ qm406] = ([qpl0,qpl1,qpl2,qpl3,qpl4,qpl5,qpl6,qpl7,qpl8,qpl9,qpl10,qpl11] : List (List qCell)).flatten.toFinset := by
          apply qlist_unionH
          simp only [List.map_cons,List.map_nil,qplaceRow,qR.H,Prod.fst,Prod.snd,
                qm406_H_list,qm533_H_list,qm584_H_list,qm586_H_list,qm587_H_list,qm590_H_list,qm591_H_list,qm601_H_list,qm602_H_list,qm611_H_list,qm614_H_list,qlist_image]
          rfl
        rw [hu]
        simp only [qcombined,List.flatten_cons,List.flatten_nil,List.append_nil,List.toFinset_cons,List.append_assoc]
      )))
def qlast_H_canonical : (qforkRow [qplaceRow ⟨602,7,6,4⟩ qm602,qplaceRow ⟨614,1,4,3⟩ qm614,qplaceRow ⟨533,5,6,4⟩ qm533,qplaceRow ⟨590,7,6,4⟩ qm590,qplaceRow ⟨611,6,3,4⟩ qm611,qplaceRow ⟨587,3,3,4⟩ qm587,qplaceRow ⟨601,5,6,4⟩ qm601,qplaceRow ⟨406,1,6,4⟩ qm406,qplaceRow ⟨591,3,3,4⟩ qm591,qplaceRow ⟨586,3,3,4⟩ qm586,qplaceRow ⟨584,5,6,4⟩ qm584,qplaceRow ⟨406,3,3,4⟩ qm406]).H = qm615.H := by
  change insert qorigin (qunionH [qplaceRow ⟨602,7,6,4⟩ qm602,qplaceRow ⟨614,1,4,3⟩ qm614,qplaceRow ⟨533,5,6,4⟩ qm533,qplaceRow ⟨590,7,6,4⟩ qm590,qplaceRow ⟨611,6,3,4⟩ qm611,qplaceRow ⟨587,3,3,4⟩ qm587,qplaceRow ⟨601,5,6,4⟩ qm601,qplaceRow ⟨406,1,6,4⟩ qm406,qplaceRow ⟨591,3,3,4⟩ qm591,qplaceRow ⟨586,3,3,4⟩ qm586,qplaceRow ⟨584,5,6,4⟩ qm584,qplaceRow ⟨406,3,3,4⟩ qm406]) = qm615.H
  rw [qcombined_H_semantics,qm615_H_list]
  exact qlist_H_target qcombined ql615 qcombined_canonical
def qhbGeometry (t : Lean.Syntax) : Lean.Elab.Tactic.TacticM Unit := Lean.withOptions (fun o => Lean.maxHeartbeats.set o 0) (withTheReader Lean.Core.Context (fun c => { c with maxHeartbeats := 0 }) (Lean.Elab.Tactic.evalTactic t))
def qsmall0 : Finset qCell := {(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),(0,0),(0,1),(1,-4),(1,-3),(1,-2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,-1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,-1),(5,1)}
def qsmall_initial : (qplaceRow ⟨406,1,6,4⟩ qm406).H ⊆ qsmall0 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhbGeometry (← `(tactic| decide +kernel))
def qsmall1 : Finset qCell := {(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),(0,0),(0,1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1)}
def qsmall_step1 : ∀ b ∈ qsmall0,b ∈ (qplaceRow ⟨406,3,3,4⟩ qm406).H → b ∈ qsmall1 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhbGeometry (← `(tactic| decide +kernel))
def qsmall2 : Finset qCell := {(-3,-1),(-2,-1),(-2,1),(-1,-1),(-1,0),(-1,1),(0,0),(0,1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1)}
def qsmall_step2 : ∀ b ∈ qsmall1,b ∈ (qplaceRow ⟨533,5,6,4⟩ qm533).H → b ∈ qsmall2 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhbGeometry (← `(tactic| decide +kernel))
def qsmall3 : Finset qCell := {(-2,1),(-1,0),(-1,1),(0,0),(0,1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0),(3,1),(4,-1),(4,0),(4,1)}
def qsmall_step3 : ∀ b ∈ qsmall2,b ∈ (qplaceRow ⟨584,5,6,4⟩ qm584).H → b ∈ qsmall3 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhbGeometry (← `(tactic| decide +kernel))
def qsmall4 : Finset qCell := {(-2,1),(-1,0),(-1,1),(0,0),(0,1),(1,0),(1,1),(2,-1),(2,0),(2,1),(3,-1),(3,0),(4,-1),(4,0)}
def qsmall_step4 : ∀ b ∈ qsmall3,b ∈ (qplaceRow ⟨587,3,3,4⟩ qm587).H → b ∈ qsmall4 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhbGeometry (← `(tactic| decide +kernel))
def qsmall5 : Finset qCell := {(-2,1),(-1,0),(-1,1),(0,0),(0,1),(1,0),(1,1),(2,1)}
def qsmall_step5 : ∀ b ∈ qsmall4,b ∈ (qplaceRow ⟨586,3,3,4⟩ qm586).H → b ∈ qsmall5 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhbGeometry (← `(tactic| decide +kernel))
def qsmall6 : Finset qCell := {(-2,1),(-1,0),(-1,1),(0,0),(0,1),(1,0),(2,1)}
def qsmall_step6 : ∀ b ∈ qsmall5,b ∈ (qplaceRow ⟨591,3,3,4⟩ qm591).H → b ∈ qsmall6 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhbGeometry (← `(tactic| decide +kernel))
def qsmall7 : Finset qCell := {(-1,0),(-1,1),(0,0),(0,1),(1,0),(2,1)}
def qsmall_step7 : ∀ b ∈ qsmall6,b ∈ (qplaceRow ⟨590,7,6,4⟩ qm590).H → b ∈ qsmall7 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhbGeometry (← `(tactic| decide +kernel))
def qsmall8 : Finset qCell := {(-1,0),(-1,1),(0,0),(1,0),(2,1)}
def qsmall_step8 : ∀ b ∈ qsmall7,b ∈ (qplaceRow ⟨601,5,6,4⟩ qm601).H → b ∈ qsmall8 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhbGeometry (← `(tactic| decide +kernel))
def qsmall9 : Finset qCell := {(-1,0),(-1,1),(0,0),(1,0)}
def qsmall_step9 : ∀ b ∈ qsmall8,b ∈ (qplaceRow ⟨602,7,6,4⟩ qm602).H → b ∈ qsmall9 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhbGeometry (← `(tactic| decide +kernel))
def qsmall10 : Finset qCell := {(-1,0),(0,0),(1,0)}
def qsmall_step10 : ∀ b ∈ qsmall9,b ∈ (qplaceRow ⟨611,6,3,4⟩ qm611).H → b ∈ qsmall10 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhbGeometry (← `(tactic| decide +kernel))
def qsmall11 : Finset qCell := {(0,0),(1,0)}
lemma qsmall_step11 : ∀ b ∈ qsmall10,b ∈ (qplaceRow ⟨614,1,4,3⟩ qm614).H → b ∈ qsmall11 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhbGeometry (← `(tactic| decide +kernel))
def qerase_union_pair (s t : Finset qCell)
    (hs : s ⊆ {qorigin,(1,0)}) (ht : t ⊆ {qorigin,(1,0)})
    (hone : (1,0) ∈ s) : (s ∪ t).erase qorigin = {(1,0)} := by
  ext b
  constructor
  · intro hb
    obtain ⟨hne,hunion⟩ := Finset.mem_erase.mp hb
    have hmem := (Finset.mem_union.mp hunion).elim (fun h => hs h) (fun h => ht h)
    have he : b = qorigin ∨ b = (1,0) := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hmem
    exact Finset.mem_singleton.mpr (he.resolve_left hne)
  · intro hb
    have he := Finset.mem_singleton.mp hb
    subst b
    exact Finset.mem_erase.mpr ⟨by decide,Finset.mem_union_left _ hone⟩
def qlast_common_small : qcommonH [qplaceRow ⟨602,7,6,4⟩ qm602,qplaceRow ⟨614,1,4,3⟩ qm614,qplaceRow ⟨533,5,6,4⟩ qm533,qplaceRow ⟨590,7,6,4⟩ qm590,qplaceRow ⟨611,6,3,4⟩ qm611,qplaceRow ⟨587,3,3,4⟩ qm587,qplaceRow ⟨601,5,6,4⟩ qm601,qplaceRow ⟨406,1,6,4⟩ qm406,qplaceRow ⟨591,3,3,4⟩ qm591,qplaceRow ⟨586,3,3,4⟩ qm586,qplaceRow ⟨584,5,6,4⟩ qm584,qplaceRow ⟨406,3,3,4⟩ qm406] ⊆ qsmall11 := by
  run_tac qhbGeometry (← `(tactic| (
    intro b hb
    have h0 := qsmall_initial (qcommonH_le_at [qplaceRow ⟨602,7,6,4⟩ qm602,qplaceRow ⟨614,1,4,3⟩ qm614,qplaceRow ⟨533,5,6,4⟩ qm533,qplaceRow ⟨590,7,6,4⟩ qm590,qplaceRow ⟨611,6,3,4⟩ qm611,qplaceRow ⟨587,3,3,4⟩ qm587,qplaceRow ⟨601,5,6,4⟩ qm601,qplaceRow ⟨406,1,6,4⟩ qm406,qplaceRow ⟨591,3,3,4⟩ qm591,qplaceRow ⟨586,3,3,4⟩ qm586,qplaceRow ⟨584,5,6,4⟩ qm584,qplaceRow ⟨406,3,3,4⟩ qm406] 7 (qplaceRow ⟨406,1,6,4⟩ qm406) rfl hb)
    have h1 := qsmall_step1 b h0 (qcommonH_le_at [qplaceRow ⟨602,7,6,4⟩ qm602,qplaceRow ⟨614,1,4,3⟩ qm614,qplaceRow ⟨533,5,6,4⟩ qm533,qplaceRow ⟨590,7,6,4⟩ qm590,qplaceRow ⟨611,6,3,4⟩ qm611,qplaceRow ⟨587,3,3,4⟩ qm587,qplaceRow ⟨601,5,6,4⟩ qm601,qplaceRow ⟨406,1,6,4⟩ qm406,qplaceRow ⟨591,3,3,4⟩ qm591,qplaceRow ⟨586,3,3,4⟩ qm586,qplaceRow ⟨584,5,6,4⟩ qm584,qplaceRow ⟨406,3,3,4⟩ qm406] 11 (qplaceRow ⟨406,3,3,4⟩ qm406) rfl hb)
    have h2 := qsmall_step2 b h1 (qcommonH_le_at [qplaceRow ⟨602,7,6,4⟩ qm602,qplaceRow ⟨614,1,4,3⟩ qm614,qplaceRow ⟨533,5,6,4⟩ qm533,qplaceRow ⟨590,7,6,4⟩ qm590,qplaceRow ⟨611,6,3,4⟩ qm611,qplaceRow ⟨587,3,3,4⟩ qm587,qplaceRow ⟨601,5,6,4⟩ qm601,qplaceRow ⟨406,1,6,4⟩ qm406,qplaceRow ⟨591,3,3,4⟩ qm591,qplaceRow ⟨586,3,3,4⟩ qm586,qplaceRow ⟨584,5,6,4⟩ qm584,qplaceRow ⟨406,3,3,4⟩ qm406] 2 (qplaceRow ⟨533,5,6,4⟩ qm533) rfl hb)
    have h3 := qsmall_step3 b h2 (qcommonH_le_at [qplaceRow ⟨602,7,6,4⟩ qm602,qplaceRow ⟨614,1,4,3⟩ qm614,qplaceRow ⟨533,5,6,4⟩ qm533,qplaceRow ⟨590,7,6,4⟩ qm590,qplaceRow ⟨611,6,3,4⟩ qm611,qplaceRow ⟨587,3,3,4⟩ qm587,qplaceRow ⟨601,5,6,4⟩ qm601,qplaceRow ⟨406,1,6,4⟩ qm406,qplaceRow ⟨591,3,3,4⟩ qm591,qplaceRow ⟨586,3,3,4⟩ qm586,qplaceRow ⟨584,5,6,4⟩ qm584,qplaceRow ⟨406,3,3,4⟩ qm406] 10 (qplaceRow ⟨584,5,6,4⟩ qm584) rfl hb)
    have h4 := qsmall_step4 b h3 (qcommonH_le_at [qplaceRow ⟨602,7,6,4⟩ qm602,qplaceRow ⟨614,1,4,3⟩ qm614,qplaceRow ⟨533,5,6,4⟩ qm533,qplaceRow ⟨590,7,6,4⟩ qm590,qplaceRow ⟨611,6,3,4⟩ qm611,qplaceRow ⟨587,3,3,4⟩ qm587,qplaceRow ⟨601,5,6,4⟩ qm601,qplaceRow ⟨406,1,6,4⟩ qm406,qplaceRow ⟨591,3,3,4⟩ qm591,qplaceRow ⟨586,3,3,4⟩ qm586,qplaceRow ⟨584,5,6,4⟩ qm584,qplaceRow ⟨406,3,3,4⟩ qm406] 5 (qplaceRow ⟨587,3,3,4⟩ qm587) rfl hb)
    have h5 := qsmall_step5 b h4 (qcommonH_le_at [qplaceRow ⟨602,7,6,4⟩ qm602,qplaceRow ⟨614,1,4,3⟩ qm614,qplaceRow ⟨533,5,6,4⟩ qm533,qplaceRow ⟨590,7,6,4⟩ qm590,qplaceRow ⟨611,6,3,4⟩ qm611,qplaceRow ⟨587,3,3,4⟩ qm587,qplaceRow ⟨601,5,6,4⟩ qm601,qplaceRow ⟨406,1,6,4⟩ qm406,qplaceRow ⟨591,3,3,4⟩ qm591,qplaceRow ⟨586,3,3,4⟩ qm586,qplaceRow ⟨584,5,6,4⟩ qm584,qplaceRow ⟨406,3,3,4⟩ qm406] 9 (qplaceRow ⟨586,3,3,4⟩ qm586) rfl hb)
    have h6 := qsmall_step6 b h5 (qcommonH_le_at [qplaceRow ⟨602,7,6,4⟩ qm602,qplaceRow ⟨614,1,4,3⟩ qm614,qplaceRow ⟨533,5,6,4⟩ qm533,qplaceRow ⟨590,7,6,4⟩ qm590,qplaceRow ⟨611,6,3,4⟩ qm611,qplaceRow ⟨587,3,3,4⟩ qm587,qplaceRow ⟨601,5,6,4⟩ qm601,qplaceRow ⟨406,1,6,4⟩ qm406,qplaceRow ⟨591,3,3,4⟩ qm591,qplaceRow ⟨586,3,3,4⟩ qm586,qplaceRow ⟨584,5,6,4⟩ qm584,qplaceRow ⟨406,3,3,4⟩ qm406] 8 (qplaceRow ⟨591,3,3,4⟩ qm591) rfl hb)
    have h7 := qsmall_step7 b h6 (qcommonH_le_at [qplaceRow ⟨602,7,6,4⟩ qm602,qplaceRow ⟨614,1,4,3⟩ qm614,qplaceRow ⟨533,5,6,4⟩ qm533,qplaceRow ⟨590,7,6,4⟩ qm590,qplaceRow ⟨611,6,3,4⟩ qm611,qplaceRow ⟨587,3,3,4⟩ qm587,qplaceRow ⟨601,5,6,4⟩ qm601,qplaceRow ⟨406,1,6,4⟩ qm406,qplaceRow ⟨591,3,3,4⟩ qm591,qplaceRow ⟨586,3,3,4⟩ qm586,qplaceRow ⟨584,5,6,4⟩ qm584,qplaceRow ⟨406,3,3,4⟩ qm406] 3 (qplaceRow ⟨590,7,6,4⟩ qm590) rfl hb)
    have h8 := qsmall_step8 b h7 (qcommonH_le_at [qplaceRow ⟨602,7,6,4⟩ qm602,qplaceRow ⟨614,1,4,3⟩ qm614,qplaceRow ⟨533,5,6,4⟩ qm533,qplaceRow ⟨590,7,6,4⟩ qm590,qplaceRow ⟨611,6,3,4⟩ qm611,qplaceRow ⟨587,3,3,4⟩ qm587,qplaceRow ⟨601,5,6,4⟩ qm601,qplaceRow ⟨406,1,6,4⟩ qm406,qplaceRow ⟨591,3,3,4⟩ qm591,qplaceRow ⟨586,3,3,4⟩ qm586,qplaceRow ⟨584,5,6,4⟩ qm584,qplaceRow ⟨406,3,3,4⟩ qm406] 6 (qplaceRow ⟨601,5,6,4⟩ qm601) rfl hb)
    have h9 := qsmall_step9 b h8 (qcommonH_le_at [qplaceRow ⟨602,7,6,4⟩ qm602,qplaceRow ⟨614,1,4,3⟩ qm614,qplaceRow ⟨533,5,6,4⟩ qm533,qplaceRow ⟨590,7,6,4⟩ qm590,qplaceRow ⟨611,6,3,4⟩ qm611,qplaceRow ⟨587,3,3,4⟩ qm587,qplaceRow ⟨601,5,6,4⟩ qm601,qplaceRow ⟨406,1,6,4⟩ qm406,qplaceRow ⟨591,3,3,4⟩ qm591,qplaceRow ⟨586,3,3,4⟩ qm586,qplaceRow ⟨584,5,6,4⟩ qm584,qplaceRow ⟨406,3,3,4⟩ qm406] 0 (qplaceRow ⟨602,7,6,4⟩ qm602) rfl hb)
    have h10 := qsmall_step10 b h9 (qcommonH_le_at [qplaceRow ⟨602,7,6,4⟩ qm602,qplaceRow ⟨614,1,4,3⟩ qm614,qplaceRow ⟨533,5,6,4⟩ qm533,qplaceRow ⟨590,7,6,4⟩ qm590,qplaceRow ⟨611,6,3,4⟩ qm611,qplaceRow ⟨587,3,3,4⟩ qm587,qplaceRow ⟨601,5,6,4⟩ qm601,qplaceRow ⟨406,1,6,4⟩ qm406,qplaceRow ⟨591,3,3,4⟩ qm591,qplaceRow ⟨586,3,3,4⟩ qm586,qplaceRow ⟨584,5,6,4⟩ qm584,qplaceRow ⟨406,3,3,4⟩ qm406] 4 (qplaceRow ⟨611,6,3,4⟩ qm611) rfl hb)
    have h11 := qsmall_step11 b h10 (qcommonH_le_at [qplaceRow ⟨602,7,6,4⟩ qm602,qplaceRow ⟨614,1,4,3⟩ qm614,qplaceRow ⟨533,5,6,4⟩ qm533,qplaceRow ⟨590,7,6,4⟩ qm590,qplaceRow ⟨611,6,3,4⟩ qm611,qplaceRow ⟨587,3,3,4⟩ qm587,qplaceRow ⟨601,5,6,4⟩ qm601,qplaceRow ⟨406,1,6,4⟩ qm406,qplaceRow ⟨591,3,3,4⟩ qm591,qplaceRow ⟨586,3,3,4⟩ qm586,qplaceRow ⟨584,5,6,4⟩ qm584,qplaceRow ⟨406,3,3,4⟩ qm406] 1 (qplaceRow ⟨614,1,4,3⟩ qm614) rfl hb)
    exact h11)))
def qlast_A_small : (qforkRow [qplaceRow ⟨602,7,6,4⟩ qm602,qplaceRow ⟨614,1,4,3⟩ qm614,qplaceRow ⟨533,5,6,4⟩ qm533,qplaceRow ⟨590,7,6,4⟩ qm590,qplaceRow ⟨611,6,3,4⟩ qm611,qplaceRow ⟨587,3,3,4⟩ qm587,qplaceRow ⟨601,5,6,4⟩ qm601,qplaceRow ⟨406,1,6,4⟩ qm406,qplaceRow ⟨591,3,3,4⟩ qm591,qplaceRow ⟨586,3,3,4⟩ qm586,qplaceRow ⟨584,5,6,4⟩ qm584,qplaceRow ⟨406,3,3,4⟩ qm406]).A = qm615.A := by
  run_tac qhbGeometry (← `(tactic| (
    change (qunionA [qplaceRow ⟨602,7,6,4⟩ qm602,qplaceRow ⟨614,1,4,3⟩ qm614,qplaceRow ⟨533,5,6,4⟩ qm533,qplaceRow ⟨590,7,6,4⟩ qm590,qplaceRow ⟨611,6,3,4⟩ qm611,qplaceRow ⟨587,3,3,4⟩ qm587,qplaceRow ⟨601,5,6,4⟩ qm601,qplaceRow ⟨406,1,6,4⟩ qm406,qplaceRow ⟨591,3,3,4⟩ qm591,qplaceRow ⟨586,3,3,4⟩ qm586,qplaceRow ⟨584,5,6,4⟩ qm584,qplaceRow ⟨406,3,3,4⟩ qm406] ∪ qcommonH [qplaceRow ⟨602,7,6,4⟩ qm602,qplaceRow ⟨614,1,4,3⟩ qm614,qplaceRow ⟨533,5,6,4⟩ qm533,qplaceRow ⟨590,7,6,4⟩ qm590,qplaceRow ⟨611,6,3,4⟩ qm611,qplaceRow ⟨587,3,3,4⟩ qm587,qplaceRow ⟨601,5,6,4⟩ qm601,qplaceRow ⟨406,1,6,4⟩ qm406,qplaceRow ⟨591,3,3,4⟩ qm591,qplaceRow ⟨586,3,3,4⟩ qm586,qplaceRow ⟨584,5,6,4⟩ qm584,qplaceRow ⟨406,3,3,4⟩ qm406]).erase qorigin = ({(1,0)} : Finset qCell)
    apply qerase_union_pair
    · decide +kernel
    · exact qlast_common_small
    · decide +kernel)))
def qlast_fast : qforkRow [qplaceRow ⟨602,7,6,4⟩ qm602,qplaceRow ⟨614,1,4,3⟩ qm614,qplaceRow ⟨533,5,6,4⟩ qm533,qplaceRow ⟨590,7,6,4⟩ qm590,qplaceRow ⟨611,6,3,4⟩ qm611,qplaceRow ⟨587,3,3,4⟩ qm587,qplaceRow ⟨601,5,6,4⟩ qm601,qplaceRow ⟨406,1,6,4⟩ qm406,qplaceRow ⟨591,3,3,4⟩ qm591,qplaceRow ⟨586,3,3,4⟩ qm586,qplaceRow ⟨584,5,6,4⟩ qm584,qplaceRow ⟨406,3,3,4⟩ qm406] = qm615 := by
  apply qx
  · exact qlast_A_small
  · exact qlast_H_canonical
  · set_option maxHeartbeats 0 in
      set_option maxRecDepth 100000 in
        run_tac qhbGeometry (← `(tactic| decide +kernel))
def qmeq_615 : qr 615 = qm615 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
          have he : qe 615 = qv615 := by run_tac qentryLookup
          rw [qr]
          simp only [show ¬ 615 < 6 by decide,↓reduceDIte,he,qv615,List.map_cons,List.map_nil,qE.terms,qT.child,Prod.fst,Prod.snd]
          try simp only [Nat.reduceLT,dite_true]
          rw [qmeq_406,qmeq_533,qmeq_584,qmeq_586,qmeq_587,qmeq_590,qmeq_591,qmeq_601,qmeq_602,qmeq_611,qmeq_614]
          exact qlast_fast)))
def qGoal (M : Finset qCell) : Prop := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (∃ (r : Fin 8) (t : qCell),qsnaky.image (qplacement r t) ⊆ M)
def qgoal_mono {M M' : Finset qCell} (h : M ⊆ M') (hG : qGoal M) : qGoal M' := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          obtain ⟨r,t,ht⟩ := hG
          exact ⟨r,t,ht.trans h⟩)
def qinverseRotation (r : Fin 8) : Fin 8 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (if r = 3 then 5 else if r = 5 then 3 else r)
def qorient_inverse (r : Fin 8) (p : qCell) : qorient (qinverseRotation r) (qorient r p) = p := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          fin_cases r <;> ext <;> simp [qorient,qinverseRotation])
def qorient_inverse' (r : Fin 8) (p : qCell) : qorient r (qorient (qinverseRotation r) p) = p := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          fin_cases r <;> ext <;> simp [qorient,qinverseRotation])
def qorientEquiv (r : Fin 8) : qCell ≃ qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨qorient r,qorient (qinverseRotation r),qorient_inverse r,qorient_inverse' r⟩)
def qplacementEquiv (r : Fin 8) (t : qCell) : qCell ≃ qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ((qorientEquiv r).trans (Equiv.addRight t))
def qplacementEquiv_apply (r : Fin 8) (t p : qCell) :
    qplacementEquiv r t p = qplacement r t p := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (rfl)
def qorient_add (r : Fin 8) (p q : qCell) : qorient r (p + q) = qorient r p + qorient r q := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          fin_cases r <;> ext <;> simp [qorient] <;> ring)
def qcomposeRotation (r s : Fin 8) : Fin 8 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (![![0,1,2,3,4,5,6,7],![1,0,3,2,5,4,7,6],
    ![2,5,0,7,6,1,4,3],![3,4,1,6,7,0,5,2],
    ![4,3,6,1,0,7,2,5],![5,2,7,0,1,6,3,4],
    ![6,7,4,5,2,3,0,1],![7,6,5,4,3,2,1,0]] r s)
def qorient_compose (r s : Fin 8) (p : qCell) :
    qorient r (qorient s p) = qorient (qcomposeRotation r s) p := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          fin_cases r <;> fin_cases s <;> ext <;> simp [qorient,qcomposeRotation])
def qgoal_map (r : Fin 8) (t : qCell) (M : Finset qCell) (hG : qGoal M) :
    qGoal (M.image (qplacementEquiv r t)) := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          obtain ⟨s,u,hu⟩ := hG
          refine ⟨qcomposeRotation r s,qorient r u + t,?_⟩
          intro x hx
          obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
          have hm := hu (Finset.mem_image_of_mem (qplacement s u) hp)
          have hh := Finset.mem_image_of_mem (qplacementEquiv r t) hm
          simpa only [qplacementEquiv_apply,qplacement,qorient_add,qorient_compose,add_assoc] using hh)
def qbaseRow_threat (i : Fin 6) :
    Threat qGoal (qbaseRow i).A (qbaseRow i).H (qbaseRow i).height := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          apply threat_leaf qGoal (fun h hG => qgoal_mono h hG) qorigin (qbaseEnvelope i)
          exact ⟨0,-qbasePoint i,Finset.Subset.refl _⟩)
def qplaceRow_threat (t : qT) (d : qR)
    (hd : Threat qGoal d.A d.H d.height) :
    Threat qGoal (qplaceRow t d).A (qplaceRow t d).H (qplaceRow t d).height := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          exact threat_map qGoal (qplacementEquiv t.rotation t.shift) (qgoal_map t.rotation t.shift)
            d.A d.H d.height hd)
def qmem_unionA (ds : List qR) (d : qR) (hd : d ∈ ds) :
    d.A ⊆ qunionA ds := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          induction ds with
          | nil => simp at hd
          | cons e ds ih =>
              simp only [List.mem_cons] at hd
              rcases hd with rfl | hd
              · exact Finset.subset_union_left
              · exact (ih hd).trans Finset.subset_union_right)
def qmem_unionH (ds : List qR) (d : qR) (hd : d ∈ ds) :
    d.H ⊆ qunionH ds := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          induction ds with
          | nil => simp at hd
          | cons e ds ih =>
              simp only [List.mem_cons] at hd
              rcases hd with rfl | hd
              · exact Finset.subset_union_left
              · exact (ih hd).trans Finset.subset_union_right)
def qmem_foldInter (ds : List qR) (S : Finset qCell) (b : qCell)
    (hS : b ∈ S) (hb : ∀ d ∈ ds,b ∈ d.H) :
    b ∈ (ds.map qR.H).foldr (· ∩ ·) S := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          induction ds with
          | nil => exact hS
          | cons d ds ih =>
              apply Finset.mem_inter.mpr
              exact ⟨hb d (by simp),ih (by intro e he; exact hb e (by simp [he]))⟩)
def qmem_commonH_of_all (ds : List qR) (hne : ds ≠ []) (b : qCell)
    (hb : ∀ d ∈ ds,b ∈ d.H) : b ∈ qcommonH ds := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          cases ds with
          | nil => exact False.elim (hne rfl)
          | cons e ds =>
              exact qmem_foldInter ds e.H b (hb e (by simp)) (by
                intro d hd; exact hb d (by simp [hd])))
def qheight_le_foldMax (ds : List qR) (d : qR) (hd : d ∈ ds) :
    d.height ≤ (ds.map qR.height).foldr max 0 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          induction ds with
          | nil => simp at hd
          | cons e ds ih =>
              simp only [List.mem_cons] at hd
              rcases hd with rfl | hd
              · exact le_max_left _ _
              · exact (ih hd).trans (le_max_right _ _))
def qforkRow_threat (ds : List qR) (hne : ds ≠ [])
    (hs : ∀ d ∈ ds,Threat qGoal d.A d.H d.height) :
    Threat qGoal (qforkRow ds).A (qforkRow ds).H (qforkRow ds).height := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          change Threat qGoal _ _ (1 + (ds.map qR.height).foldr max 0)
          rw [Nat.add_comm 1]
          let td : qR → ThreatData qCell := fun d => ⟨d.A,d.H,d.height⟩
          apply threat_fork qGoal (fun h hG => qgoal_mono h hG) qorigin (ds.map td)
            (by intro h; exact hne (List.map_eq_nil_iff.mp h)) _
          · intro d hd
            obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
            exact hs e he
          · intro d hd
            obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
            exact qheight_le_foldMax ds e he
          · intro d hd x hx
            obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
            have hm : x ∈ qunionA ds ∪ qcommonH ds :=
              Finset.mem_union_left _ (qmem_unionA ds e he hx)
            by_cases hx0 : x = qorigin
            · exact Finset.mem_insert.mpr (Or.inl hx0)
            · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hx0,hm⟩)
          · intro d hd x hx
            obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
            exact Finset.mem_insert_of_mem (qmem_unionH ds e he hx)
          · exact Finset.mem_insert_self _ _
          · intro b hb
            have hc : b ∈ qcommonH ds := qmem_commonH_of_all ds hne b (by
              intro e he
              exact hb (td e) (List.mem_map.mpr ⟨e,he,rfl⟩))
            have hm : b ∈ qunionA ds ∪ qcommonH ds := Finset.mem_union_right _ hc
            by_cases hb0 : b = qorigin
            · exact Finset.mem_insert.mpr (Or.inl hb0)
            · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hb0,hm⟩))
def qe_valid_of_TableValid (hv : qTableValid) (i : ℕ) (hi : i < 616) (hil : 6 ≤ i) :
    (qe i).terms ≠ [] ∧ ∀ t ∈ (qe i).terms,t.child < i := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          have hsize := hv.1
          have hk : i - 6 < qtable.size := by omega
          have hh := hv.2 (i - 6) hk
          have he : qe i = qtable[i - 6]?.getD qemptyEntry := rfl
          rw [he]
          have hhidx := hh.1
          have hhne := hh.2.1
          have hhchild := hh.2.2
          refine ⟨hhne,?_⟩
          intro t ht
          have hc := hhchild t ht
          rw [hhidx] at hc
          omega)
def qr_threat
    (hvalid : ∀ i,i < 616 → 6 ≤ i →
      (qe i).terms ≠ [] ∧ ∀ t ∈ (qe i).terms,t.child < i)
    (i : ℕ) (hib : i < 616) :
    Threat qGoal (qr i).A (qr i).H (qr i).height := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          induction i using Nat.strong_induction_on with
          | h i ih =>
              by_cases hi : i < 6
              · have he : qr i = qbaseRow ⟨i,hi⟩ := by
                  rw [qr]
                  exact dif_pos hi
                simp only [he]
                exact qbaseRow_threat ⟨i,hi⟩
              · have hv := hvalid i hib (by omega)
                let f : qT → qR := fun t =>
                  qplaceRow t (if _ : t.child < i then qr t.child else qemptyRow)
                have he : qr i = qforkRow ((qe i).terms.map f) := by
                  rw [qr]
                  exact dif_neg hi
                have hne : (qe i).terms.map f ≠ [] := by
                  intro hempty
                  exact hv.1 (List.map_eq_nil_iff.mp hempty)
                have hs : ∀ d ∈ (qe i).terms.map f,
                    Threat qGoal d.A d.H d.height := by
                  intro d hd
                  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hd
                  change Threat qGoal (qplaceRow t _).A (qplaceRow t _).H (qplaceRow t _).height
                  apply qplaceRow_threat
                  have hti := hv.2 t ht
                  simp only [dif_pos hti]
                  exact ih t.child hti (by omega)
                generalize hds : (qe i).terms.map f = ds at he hne hs
                have hf := qforkRow_threat ds hne hs
                rw [← he] at hf
                exact hf)
def qoext (a b : qR) (ha : a.A = b.A) (hh : a.H = b.H) (ht : a.height = b.height) : a = b := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          apply Prod.ext
          · exact ha
          · apply Prod.ext
            · exact hh
            · exact ht)
def qmoveRow (r : Fin 8) (t : qCell) (d : qR) : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨d.A.image (qplacement r t),d.H.image (qplacement r t),d.height⟩)
def qmoveRow_threat (r : Fin 8) (t : qCell) (d : qR)
    (hd : Threat qGoal d.A d.H d.height) :
    Threat qGoal (qmoveRow r t d).A (qmoveRow r t d).H (qmoveRow r t d).height := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          exact threat_map qGoal (qplacementEquiv r t) (qgoal_map r t) d.A d.H d.height hd)
def qo406 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (qm406)
def qo533 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (qm533)
def qo557 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (qm557)
def qo584 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (qm584)
def qo586 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (qm586)
def qo587 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (qm587)
def qo590 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (qm590)
def qo591 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (qm591)
def qo595 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (qm595)
def qo601 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (qm601)
def qo602 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (qm602)
def qo603 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (qm603)
def qo611 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (qm611)
def qo614 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (qm614)
def qo615 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (qm615)
def qmem_moveRow_H_iff (r : Fin 8) (t : qCell) (d : qR) (b : qCell) :
    b ∈ (qmoveRow r t d).H ↔ (qplacementEquiv r t).symm b ∈ d.H := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          change b ∈ d.H.image (qplacementEquiv r t) ↔ _
          constructor
          · intro h
            obtain ⟨a,ha,hab⟩ := Finset.mem_image.mp h
            simpa only [← hab,Equiv.symm_apply_apply] using ha
          · intro h
            exact Finset.mem_image.mpr ⟨_,h,(qplacementEquiv r t).apply_symm_apply b⟩)
def qnot_mem_unionH (ds : List qR) (b : qCell)
    (h : ∀ d ∈ ds,b ∉ d.H) : b ∉ qunionH ds := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          induction ds with
          | nil => simp [qunionH]
          | cons d ds ih =>
              have hd := h d (by simp)
              have ht := ih (by intro e he; exact h e (by simp [he]))
              simpa only [qunionH,List.map_cons,List.foldr_cons,Finset.mem_union,not_or] using And.intro hd ht)
def qescapeChildren : List qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ([
  qmoveRow 4 (0,1) qo406,
  qmoveRow 6 (0,-2) qo406,
  qmoveRow 0 (0,1) qo533,
  qmoveRow 0 (0,1) qo584,
  qmoveRow 6 (0,-2) qo586,
  qmoveRow 6 (0,-2) qo587,
  qmoveRow 2 (0,1) qo590,
  qmoveRow 2 (0,-2) qo591,
  qmoveRow 0 (0,1) qo601,
  qmoveRow 2 (0,1) qo602,
  qmoveRow 5 (0,-2) qo611,
  qmoveRow 4 (1,-1) qo614])
def qescapeRawH : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (insert qorigin (qunionH qescapeChildren))
def qescapeMemo : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (⟨{qorigin},qescapeRawH.image (qplacement 0 (0,1)),34⟩)
def qrootChildren : List qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ([
  qmoveRow 0 (1,0) qo557,
  qmoveRow 6 (-1,0) qo557,
  qmoveRow 2 (1,0) qo595,
  qmoveRow 3 (0,1) qo595,
  qmoveRow 4 (-1,0) qo595,
  qmoveRow 5 (0,-1) qo595,
  qmoveRow 0 (1,0) qo595,
  qmoveRow 1 (0,1) qo595,
  qmoveRow 6 (-1,0) qo595,
  qmoveRow 7 (0,-1) qo595,
  qmoveRow 0 (1,0) qo603,
  qmoveRow 1 (0,1) qo603,
  qmoveRow 4 (-1,0) qo603,
  qmoveRow 5 (0,-1) qo603,
  qmoveRow 2 (1,0) qo557,
  qmoveRow 3 (0,1) qo557,
  qmoveRow 0 (-1,0) qo615,
  qmoveRow 1 (0,-1) qo615,
  qmoveRow 2 (-1,0) qo615,
  qmoveRow 3 (0,-1) qo615,
  qmoveRow 0 (0,0) qescapeMemo,
  qmoveRow 2 (0,0) qescapeMemo,
  qmoveRow 3 (0,0) qescapeMemo,
  qmoveRow 6 (0,0) qescapeMemo])
def qescapeI_0 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-5,0),(-4,0),(-4,1),(-4,2),(-4,3),(-3,0),(-3,1),(-3,2),(-3,3),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-4),(1,-3),(1,-2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)})
def qescapeinitial : (qmoveRow 4 (0,1) qo406).H ⊆ qescapeI_0 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          have h : ∀ a ∈ qo406.H,qplacement 4 (0,1) a ∈ qescapeI_0 := by decide +kernel
          intro b hb
          obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
          exact h a ha)
def qescapeI_1 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-4),(1,-3),(1,-2),(1,1),(1,2),(1,3)})
def qescapestep_1 : ∀ b ∈ qescapeI_0,(qplacementEquiv 6 (0,-2)).symm b ∈ qo406.H → b ∈ qescapeI_1 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qescapeI_2 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-4),(1,-3),(1,-2),(1,1),(1,2),(1,3)})
def qescapestep_2 : ∀ b ∈ qescapeI_1,(qplacementEquiv 0 (0,1)).symm b ∈ qo533.H → b ∈ qescapeI_2 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qescapeI_3 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3)})
def qescapestep_3 : ∀ b ∈ qescapeI_2,(qplacementEquiv 0 (0,1)).symm b ∈ qo584.H → b ∈ qescapeI_3 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qescapeI_4 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-2),(0,-1),(0,0)})
def qescapestep_4 : ∀ b ∈ qescapeI_3,(qplacementEquiv 6 (0,-2)).symm b ∈ qo586.H → b ∈ qescapeI_4 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qescapeI_5 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(0,-2),(0,-1),(0,0)})
def qescapestep_5 : ∀ b ∈ qescapeI_4,(qplacementEquiv 6 (0,-2)).symm b ∈ qo587.H → b ∈ qescapeI_5 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qescapeI_6 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-1,-2),(-1,-1),(-1,0),(-1,1),(0,-2),(0,-1),(0,0)})
def qescapestep_6 : ∀ b ∈ qescapeI_5,(qplacementEquiv 2 (0,1)).symm b ∈ qo590.H → b ∈ qescapeI_6 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qescapeI_7 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-1,-2),(-1,-1),(-1,1),(0,-2),(0,-1),(0,0)})
def qescapestep_7 : ∀ b ∈ qescapeI_6,(qplacementEquiv 2 (0,-2)).symm b ∈ qo591.H → b ∈ qescapeI_7 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qescapeI_8 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-1,-2),(-1,1),(0,-2),(0,-1),(0,0)})
def qescapestep_8 : ∀ b ∈ qescapeI_7,(qplacementEquiv 0 (0,1)).symm b ∈ qo601.H → b ∈ qescapeI_8 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qescapeI_9 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-1,-2),(0,-2),(0,-1),(0,0)})
def qescapestep_9 : ∀ b ∈ qescapeI_8,(qplacementEquiv 2 (0,1)).symm b ∈ qo602.H → b ∈ qescapeI_9 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qescapeI_10 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(0,-2),(0,-1),(0,0)})
def qescapestep_10 : ∀ b ∈ qescapeI_9,(qplacementEquiv 5 (0,-2)).symm b ∈ qo611.H → b ∈ qescapeI_10 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qescapeI_11 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(0,-1),(0,0)})
def qescapestep_11 : ∀ b ∈ qescapeI_10,(qplacementEquiv 4 (1,-1)).symm b ∈ qo614.H → b ∈ qescapeI_11 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qescape_small_common (b : qCell) (hb : ∀ e ∈ qescapeChildren,b ∈ e.H) : b ∈ qescapeI_11 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          have h0 := qescapeinitial (hb (qmoveRow 4 (0,1) qo406) (List.Mem.head _))
          have h1 := qescapestep_1 b h0 ((qmem_moveRow_H_iff 6 (0,-2) qo406 b).mp (hb (qmoveRow 6 (0,-2) qo406) (List.Mem.tail _ (List.Mem.head _))))
          have h2 := qescapestep_2 b h1 ((qmem_moveRow_H_iff 0 (0,1) qo533 b).mp (hb (qmoveRow 0 (0,1) qo533) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
          have h3 := qescapestep_3 b h2 ((qmem_moveRow_H_iff 0 (0,1) qo584 b).mp (hb (qmoveRow 0 (0,1) qo584) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
          have h4 := qescapestep_4 b h3 ((qmem_moveRow_H_iff 6 (0,-2) qo586 b).mp (hb (qmoveRow 6 (0,-2) qo586) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
          have h5 := qescapestep_5 b h4 ((qmem_moveRow_H_iff 6 (0,-2) qo587 b).mp (hb (qmoveRow 6 (0,-2) qo587) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
          have h6 := qescapestep_6 b h5 ((qmem_moveRow_H_iff 2 (0,1) qo590 b).mp (hb (qmoveRow 2 (0,1) qo590) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
          have h7 := qescapestep_7 b h6 ((qmem_moveRow_H_iff 2 (0,-2) qo591 b).mp (hb (qmoveRow 2 (0,-2) qo591) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))
          have h8 := qescapestep_8 b h7 ((qmem_moveRow_H_iff 0 (0,1) qo601 b).mp (hb (qmoveRow 0 (0,1) qo601) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))
          have h9 := qescapestep_9 b h8 ((qmem_moveRow_H_iff 2 (0,1) qo602 b).mp (hb (qmoveRow 2 (0,1) qo602) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))
          have h10 := qescapestep_10 b h9 ((qmem_moveRow_H_iff 5 (0,-2) qo611 b).mp (hb (qmoveRow 5 (0,-2) qo611) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))
          have h11 := qescapestep_11 b h10 ((qmem_moveRow_H_iff 4 (1,-1) qo614 b).mp (hb (qmoveRow 4 (1,-1) qo614) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))
          exact h11)
def qf539 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-5,-1),(-5,0),(-5,1),(-5,3),(-5,4),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-3,5),(-3,6),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4)] : List qCell).toFinset)
def qf540 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(-2,5),(-2,6),(-2,7),(-2,8),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(-1,6),(-1,7),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2)] : List qCell).toFinset)
def qf541 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1)] : List qCell).toFinset)
def qf542 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(4,-4),(4,-3),(4,-2),(4,-1)] : List qCell).toFinset)
def qf543 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (([(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(5,-1),(5,0),(5,1),(5,2),(5,3),(5,4),(6,-1),(6,0),(6,1),(6,3),(6,4)] : List qCell).toFinset)
def qrootI_0 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ((qf539 ∪ qf540 ∪ qf541 ∪ qf542 ∪ qf543))
def qrootinitial : (qmoveRow 0 (1,0) qo557).H ⊆ qrootI_0 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          have h : ∀ a ∈ qo557.H,qplacement 0 (1,0) a ∈ qrootI_0 := by decide +kernel
          intro b hb
          obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
          exact h a ha)
def qrootI_1 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-5,-1),(-5,0),(-5,1),(-4,-1),(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-2,5),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(-1,5),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1)})
def qrootstep_1 : ∀ b ∈ qrootI_0,(qplacementEquiv 6 (-1,0)).symm b ∈ qo557.H → b ∈ qrootI_1 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qrootI_2 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-5,-1),(-5,0),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(5,-1),(5,0),(5,1)})
def qrootstep_2 : ∀ b ∈ qrootI_1,(qplacementEquiv 2 (1,0)).symm b ∈ qo595.H → b ∈ qrootI_2 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qrootI_3 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-5,-1),(-5,0),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,-2),(2,0),(2,1),(3,-2),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)})
def qrootstep_3 : ∀ b ∈ qrootI_2,(qplacementEquiv 3 (0,1)).symm b ∈ qo595.H → b ∈ qrootI_3 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qrootI_4 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-5,-1),(-5,0),(-5,1),(-4,-1),(-4,0),(-4,1),(-3,-1),(-3,0),(-3,1),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,-2),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)})
def qrootstep_4 : ∀ b ∈ qrootI_3,(qplacementEquiv 4 (-1,0)).symm b ∈ qo595.H → b ∈ qrootI_4 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qrootI_5 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-5,-1),(-5,0),(-4,-1),(-4,0),(-3,-1),(-3,0),(-2,-1),(-2,0),(-2,2),(-1,-5),(-1,-4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,-2),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)})
def qrootstep_5 : ∀ b ∈ qrootI_4,(qplacementEquiv 5 (0,-1)).symm b ∈ qo595.H → b ∈ qrootI_5 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qrootI_6 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-5,-1),(-5,0),(-4,-1),(-4,0),(-3,-1),(-3,0),(-2,-1),(-2,0),(-2,2),(-1,-1),(-1,0),(-1,1),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,-2),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)})
def qrootstep_6 : ∀ b ∈ qrootI_5,(qplacementEquiv 0 (1,0)).symm b ∈ qo595.H → b ∈ qrootI_6 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qrootI_7 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-5,0),(-4,0),(-3,0),(-2,0),(-2,2),(-1,-1),(-1,0),(-1,1),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,-2),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)})
def qrootstep_7 : ∀ b ∈ qrootI_6,(qplacementEquiv 1 (0,1)).symm b ∈ qo595.H → b ∈ qrootI_7 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qrootI_8 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-5,0),(-4,0),(-3,0),(-2,0),(-2,2),(-1,-1),(-1,0),(-1,1),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-1),(1,0),(1,1),(2,-2),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)})
def qrootstep_8 : ∀ b ∈ qrootI_7,(qplacementEquiv 6 (-1,0)).symm b ∈ qo595.H → b ∈ qrootI_8 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qrootI_9 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-5,0),(-4,0),(-3,0),(-2,0),(-2,2),(-1,-1),(-1,0),(-1,1),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-1),(1,0),(1,1),(2,-2),(2,0),(3,0),(4,0),(5,0)})
def qrootstep_9 : ∀ b ∈ qrootI_8,(qplacementEquiv 7 (0,-1)).symm b ∈ qo595.H → b ∈ qrootI_9 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qrootI_10 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-2,2),(-1,-1),(-1,0),(-1,1),(0,-5),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-1),(1,0),(1,1),(2,-2),(2,0),(3,0),(4,0),(5,0)})
def qrootstep_10 : ∀ b ∈ qrootI_9,(qplacementEquiv 0 (1,0)).symm b ∈ qo603.H → b ∈ qrootI_10 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qrootI_11 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-2,2),(-1,-1),(-1,0),(-1,1),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-1),(1,0),(1,1),(2,-2),(2,0),(3,0),(4,0),(5,0)})
def qrootstep_11 : ∀ b ∈ qrootI_10,(qplacementEquiv 1 (0,1)).symm b ∈ qo603.H → b ∈ qrootI_11 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qrootI_12 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-2,2),(-1,-1),(-1,0),(-1,1),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,-1),(1,0),(1,1),(2,-2)})
def qrootstep_12 : ∀ b ∈ qrootI_11,(qplacementEquiv 4 (-1,0)).symm b ∈ qo603.H → b ∈ qrootI_12 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qrootI_13 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-2,2),(-1,-1),(-1,0),(-1,1),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-2)})
def qrootstep_13 : ∀ b ∈ qrootI_12,(qplacementEquiv 5 (0,-1)).symm b ∈ qo603.H → b ∈ qrootI_13 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qrootI_14 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-1,-1),(-1,0),(-1,1),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1),(2,-2)})
def qrootstep_14 : ∀ b ∈ qrootI_13,(qplacementEquiv 2 (1,0)).symm b ∈ qo557.H → b ∈ qrootI_14 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qrootI_15 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-1,-1),(-1,0),(-1,1),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1)})
def qrootstep_15 : ∀ b ∈ qrootI_14,(qplacementEquiv 3 (0,1)).symm b ∈ qo557.H → b ∈ qrootI_15 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qrootI_16 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-1,-1),(-1,0),(-1,1),(0,0),(0,1),(1,-1),(1,0),(1,1)})
def qrootstep_16 : ∀ b ∈ qrootI_15,(qplacementEquiv 0 (-1,0)).symm b ∈ qo615.H → b ∈ qrootI_16 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qrootI_17 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-1,-1),(-1,1),(0,0),(0,1),(1,-1),(1,0),(1,1)})
def qrootstep_17 : ∀ b ∈ qrootI_16,(qplacementEquiv 1 (0,-1)).symm b ∈ qo615.H → b ∈ qrootI_17 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qrootI_18 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-1,-1),(-1,1),(0,0),(1,-1),(1,0),(1,1)})
def qrootstep_18 : ∀ b ∈ qrootI_17,(qplacementEquiv 2 (-1,0)).symm b ∈ qo615.H → b ∈ qrootI_18 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qrootI_19 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(-1,-1),(-1,1),(0,0),(1,-1),(1,1)})
def qrootstep_19 : ∀ b ∈ qrootI_18,(qplacementEquiv 3 (0,-1)).symm b ∈ qo615.H → b ∈ qrootI_19 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qroot_small_common (b : qCell) (hb : ∀ e ∈ qrootChildren,b ∈ e.H) : b ∈ qrootI_19 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          have h0 := qrootinitial (hb (qmoveRow 0 (1,0) qo557) (List.Mem.head _))
          have h1 := qrootstep_1 b h0 ((qmem_moveRow_H_iff 6 (-1,0) qo557 b).mp (hb (qmoveRow 6 (-1,0) qo557) (List.Mem.tail _ (List.Mem.head _))))
          have h2 := qrootstep_2 b h1 ((qmem_moveRow_H_iff 2 (1,0) qo595 b).mp (hb (qmoveRow 2 (1,0) qo595) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
          have h3 := qrootstep_3 b h2 ((qmem_moveRow_H_iff 3 (0,1) qo595 b).mp (hb (qmoveRow 3 (0,1) qo595) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
          have h4 := qrootstep_4 b h3 ((qmem_moveRow_H_iff 4 (-1,0) qo595 b).mp (hb (qmoveRow 4 (-1,0) qo595) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
          have h5 := qrootstep_5 b h4 ((qmem_moveRow_H_iff 5 (0,-1) qo595 b).mp (hb (qmoveRow 5 (0,-1) qo595) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
          have h6 := qrootstep_6 b h5 ((qmem_moveRow_H_iff 0 (1,0) qo595 b).mp (hb (qmoveRow 0 (1,0) qo595) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
          have h7 := qrootstep_7 b h6 ((qmem_moveRow_H_iff 1 (0,1) qo595 b).mp (hb (qmoveRow 1 (0,1) qo595) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))
          have h8 := qrootstep_8 b h7 ((qmem_moveRow_H_iff 6 (-1,0) qo595 b).mp (hb (qmoveRow 6 (-1,0) qo595) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))
          have h9 := qrootstep_9 b h8 ((qmem_moveRow_H_iff 7 (0,-1) qo595 b).mp (hb (qmoveRow 7 (0,-1) qo595) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))
          have h10 := qrootstep_10 b h9 ((qmem_moveRow_H_iff 0 (1,0) qo603 b).mp (hb (qmoveRow 0 (1,0) qo603) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))
          have h11 := qrootstep_11 b h10 ((qmem_moveRow_H_iff 1 (0,1) qo603 b).mp (hb (qmoveRow 1 (0,1) qo603) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))
          have h12 := qrootstep_12 b h11 ((qmem_moveRow_H_iff 4 (-1,0) qo603 b).mp (hb (qmoveRow 4 (-1,0) qo603) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))
          have h13 := qrootstep_13 b h12 ((qmem_moveRow_H_iff 5 (0,-1) qo603 b).mp (hb (qmoveRow 5 (0,-1) qo603) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))
          have h14 := qrootstep_14 b h13 ((qmem_moveRow_H_iff 2 (1,0) qo557 b).mp (hb (qmoveRow 2 (1,0) qo557) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))
          have h15 := qrootstep_15 b h14 ((qmem_moveRow_H_iff 3 (0,1) qo557 b).mp (hb (qmoveRow 3 (0,1) qo557) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))
          have h16 := qrootstep_16 b h15 ((qmem_moveRow_H_iff 0 (-1,0) qo615 b).mp (hb (qmoveRow 0 (-1,0) qo615) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))
          have h17 := qrootstep_17 b h16 ((qmem_moveRow_H_iff 1 (0,-1) qo615 b).mp (hb (qmoveRow 1 (0,-1) qo615) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))
          have h18 := qrootstep_18 b h17 ((qmem_moveRow_H_iff 2 (-1,0) qo615 b).mp (hb (qmoveRow 2 (-1,0) qo615) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))
          have h19 := qrootstep_19 b h18 ((qmem_moveRow_H_iff 3 (0,-1) qo615 b).mp (hb (qmoveRow 3 (0,-1) qo615) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))
          exact h19)
def qescape_A_bound : ∀ d ∈ qescapeChildren,d.A ⊆ {(0,-1),qorigin} := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qescape_common_bound (b : qCell) (hb : ∀ d ∈ qescapeChildren,b ∈ d.H) : b ∈ ({(0,-1),qorigin} : Finset qCell) := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (qescape_small_common b hb)
def qescape_child_height : ∀ d ∈ qescapeChildren,d.height ≤ 33 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qescape_missing_0 : (qplacementEquiv 4 (0,1)).symm (1,0) ∉ qo406.H := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qescape_missing_1 : (qplacementEquiv 6 (0,-2)).symm (1,0) ∉ qo406.H := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qescape_missing_2 : (qplacementEquiv 0 (0,1)).symm (1,0) ∉ qo533.H := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qescape_missing_3 : (qplacementEquiv 0 (0,1)).symm (1,0) ∉ qo584.H := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qescape_missing_4 : (qplacementEquiv 6 (0,-2)).symm (1,0) ∉ qo586.H := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qescape_missing_5 : (qplacementEquiv 6 (0,-2)).symm (1,0) ∉ qo587.H := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qescape_missing_6 : (qplacementEquiv 2 (0,1)).symm (1,0) ∉ qo590.H := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qescape_missing_7 : (qplacementEquiv 2 (0,-2)).symm (1,0) ∉ qo591.H := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qescape_missing_8 : (qplacementEquiv 0 (0,1)).symm (1,0) ∉ qo601.H := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qescape_missing_9 : (qplacementEquiv 2 (0,1)).symm (1,0) ∉ qo602.H := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qescape_missing_10 : (qplacementEquiv 5 (0,-2)).symm (1,0) ∉ qo611.H := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qescape_missing_11 : (qplacementEquiv 4 (1,-1)).symm (1,0) ∉ qo614.H := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qescape_child_missing : ∀ d ∈ qescapeChildren,(1,0) ∉ d.H := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| (
        simp only [qescapeChildren,List.forall_mem_cons,List.forall_mem_nil,and_true]
        exact ⟨fun h => qescape_missing_0 ((qmem_moveRow_H_iff 4 (0,1) qo406 (1,0)).mp h),
          fun h => qescape_missing_1 ((qmem_moveRow_H_iff 6 (0,-2) qo406 (1,0)).mp h),
          fun h => qescape_missing_2 ((qmem_moveRow_H_iff 0 (0,1) qo533 (1,0)).mp h),
          fun h => qescape_missing_3 ((qmem_moveRow_H_iff 0 (0,1) qo584 (1,0)).mp h),
          fun h => qescape_missing_4 ((qmem_moveRow_H_iff 6 (0,-2) qo586 (1,0)).mp h),
          fun h => qescape_missing_5 ((qmem_moveRow_H_iff 6 (0,-2) qo587 (1,0)).mp h),
          fun h => qescape_missing_6 ((qmem_moveRow_H_iff 2 (0,1) qo590 (1,0)).mp h),
          fun h => qescape_missing_7 ((qmem_moveRow_H_iff 2 (0,-2) qo591 (1,0)).mp h),
          fun h => qescape_missing_8 ((qmem_moveRow_H_iff 0 (0,1) qo601 (1,0)).mp h),
          fun h => qescape_missing_9 ((qmem_moveRow_H_iff 2 (0,1) qo602 (1,0)).mp h),
          fun h => qescape_missing_10 ((qmem_moveRow_H_iff 5 (0,-2) qo611 (1,0)).mp h),
          fun h => qescape_missing_11 ((qmem_moveRow_H_iff 4 (1,-1) qo614 (1,0)).mp h), by intro x hx; cases hx⟩)))
def qescape_diag_missing : (1,1) ∉ qescapeMemo.H := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          intro h
          obtain ⟨a,ha,he⟩ := Finset.mem_image.mp h
          have hae : a = (1,0) := by
            apply (qplacementEquiv 0 (0,1)).injective
            exact he.trans (by rfl)
          subst a
          have hn := qnot_mem_unionH qescapeChildren (1,0) qescape_child_missing
          exact (Finset.mem_insert.mp ha).elim (by decide) hn)
def qescape_rotation_missing (r : Fin 8) (b : qCell) (hr : qplacement r (0,0) (1,1) = b) :
    b ∉ (qmoveRow r (0,0) qescapeMemo).H := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          intro h
          have hm := (qmem_moveRow_H_iff r (0,0) qescapeMemo b).mp h
          have he : (qplacementEquiv r (0,0)).symm b = (1,1) := by
            rw [← hr]
            exact (qplacementEquiv r (0,0)).symm_apply_apply (1,1)
          exact qescape_diag_missing (he ▸ hm))
def qroot_A_bound : ∀ d ∈ qrootChildren,d.A ⊆ {qorigin} := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qroot_child_height : ∀ d ∈ qrootChildren,d.height ≤ 34 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))
def qroot_common_bound (b : qCell) (hb : ∀ d ∈ qrootChildren,b ∈ d.H) : b ∈ ({qorigin} : Finset qCell) := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          have hs := qroot_small_common b hb
          simp only [qrootI_19,Finset.mem_insert,Finset.mem_singleton] at hs
          rcases hs with rfl | rfl | rfl | rfl | rfl
          · exact False.elim (qescape_rotation_missing 6 (-1,-1) (by rfl) (hb (qmoveRow 6 (0,0) qescapeMemo) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))
          · exact False.elim (qescape_rotation_missing 3 (-1,1) (by rfl) (hb (qmoveRow 3 (0,0) qescapeMemo) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))
          · exact Finset.mem_singleton_self _
          · exact False.elim (qescape_rotation_missing 2 (1,-1) (by rfl) (hb (qmoveRow 2 (0,0) qescapeMemo) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))
          · exact False.elim (qescape_rotation_missing 0 (1,1) (by rfl) (hb (qmoveRow 0 (0,0) qescapeMemo) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))
def qgoal_translation_cancel (S : Finset qCell) :
    (S.image (qplacement 0 (0,-1))).image (qplacement 0 (0,1)) = S := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          rw [Finset.image_image]
          have hf : qplacement 0 (0,1) ∘ qplacement 0 (0,-1) = id := by
            funext p; ext <;> simp [qplacement,qorient]
          rw [hf,Finset.image_id])
def qempty_winning_of_opening_rows
    (h406 : Threat qGoal qo406.A qo406.H qo406.height)
    (h533 : Threat qGoal qo533.A qo533.H qo533.height)
    (h557 : Threat qGoal qo557.A qo557.H qo557.height)
    (h584 : Threat qGoal qo584.A qo584.H qo584.height)
    (h586 : Threat qGoal qo586.A qo586.H qo586.height)
    (h587 : Threat qGoal qo587.A qo587.H qo587.height)
    (h590 : Threat qGoal qo590.A qo590.H qo590.height)
    (h591 : Threat qGoal qo591.A qo591.H qo591.height)
    (h595 : Threat qGoal qo595.A qo595.H qo595.height)
    (h601 : Threat qGoal qo601.A qo601.H qo601.height)
    (h602 : Threat qGoal qo602.A qo602.H qo602.height)
    (h603 : Threat qGoal qo603.A qo603.H qo603.height)
    (h611 : Threat qGoal qo611.A qo611.H qo611.height)
    (h614 : Threat qGoal qo614.A qo614.H qo614.height)
    (h615 : Threat qGoal qo615.A qo615.H qo615.height)
    : Winning qGoal 35 ∅ ∅ := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          have hec : ∀ d ∈ qescapeChildren,Threat qGoal d.A d.H d.height := by
            intro d hd
            simp only [qescapeChildren,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hd
            rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact qmoveRow_threat _ _ _ h406
            · exact qmoveRow_threat _ _ _ h406
            · exact qmoveRow_threat _ _ _ h533
            · exact qmoveRow_threat _ _ _ h584
            · exact qmoveRow_threat _ _ _ h586
            · exact qmoveRow_threat _ _ _ h587
            · exact qmoveRow_threat _ _ _ h590
            · exact qmoveRow_threat _ _ _ h591
            · exact qmoveRow_threat _ _ _ h601
            · exact qmoveRow_threat _ _ _ h602
            · exact qmoveRow_threat _ _ _ h611
            · exact qmoveRow_threat _ _ _ h614
          have heraw : Threat qGoal {(0,-1)} qescapeRawH 34 := by
            refine threat_fork qGoal (fun h hG => qgoal_mono h hG) qorigin
              (qescapeChildren.map (fun d => (⟨d.A,d.H,d.height⟩ : ThreatData qCell)))
              (by simp [qescapeChildren]) 33 ?_ ?_ _ _ ?_ ?_ ?_ ?_
            · intro d hd; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
              exact hec e he
            · intro d hd; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
              exact qescape_child_height e he
            · intro d hd; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
              simpa only [ThreatData.threatDataA,Prod.fst,Finset.pair_comm qorigin (0,-1)] using qescape_A_bound e he
            · intro d hd; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
              intro x hx
              exact Finset.mem_insert_of_mem (qmem_unionH qescapeChildren e he hx)
            · exact Finset.mem_insert_self _ _
            · intro b hb
              simpa only [Finset.pair_comm qorigin (0,-1)] using qescape_common_bound b (by
                intro e he; exact hb ⟨e.A,e.H,e.height⟩ (List.mem_map.mpr ⟨e,he,rfl⟩))
          let raw : qR := ⟨{(0,-1)},qescapeRawH,34⟩
          have he := qmoveRow_threat 0 (0,1) raw heraw
          have hmove : qmoveRow 0 (0,1) raw = qescapeMemo := by
            apply qoext
            · decide +kernel
            · rfl
            · rfl
          rw [hmove] at he
          have hrc : ∀ d ∈ qrootChildren,Threat qGoal d.A d.H d.height := by
            intro d hd
            simp only [qrootChildren,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hd
            rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact qmoveRow_threat _ _ _ h557
            · exact qmoveRow_threat _ _ _ h557
            · exact qmoveRow_threat _ _ _ h595
            · exact qmoveRow_threat _ _ _ h595
            · exact qmoveRow_threat _ _ _ h595
            · exact qmoveRow_threat _ _ _ h595
            · exact qmoveRow_threat _ _ _ h595
            · exact qmoveRow_threat _ _ _ h595
            · exact qmoveRow_threat _ _ _ h595
            · exact qmoveRow_threat _ _ _ h595
            · exact qmoveRow_threat _ _ _ h603
            · exact qmoveRow_threat _ _ _ h603
            · exact qmoveRow_threat _ _ _ h603
            · exact qmoveRow_threat _ _ _ h603
            · exact qmoveRow_threat _ _ _ h557
            · exact qmoveRow_threat _ _ _ h557
            · exact qmoveRow_threat _ _ _ h615
            · exact qmoveRow_threat _ _ _ h615
            · exact qmoveRow_threat _ _ _ h615
            · exact qmoveRow_threat _ _ _ h615
            · exact qmoveRow_threat _ _ _ he
            · exact qmoveRow_threat _ _ _ he
            · exact qmoveRow_threat _ _ _ he
            · exact qmoveRow_threat _ _ _ he
          have hr : Threat qGoal ∅ (insert qorigin (qunionH qrootChildren)) 35 := by
            refine threat_fork qGoal (fun h hG => qgoal_mono h hG) qorigin
              (qrootChildren.map (fun d => (⟨d.A,d.H,d.height⟩ : ThreatData qCell)))
              (by simp [qrootChildren]) 34 ?_ ?_ _ _ ?_ ?_ ?_ ?_
            · intro d hd; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
              exact hrc e he
            · intro d hd; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd; exact qroot_child_height e he
            · intro d hd; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd; exact qroot_A_bound e he
            · intro d hd x hx; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
              exact Finset.mem_insert_of_mem (qmem_unionH qrootChildren e he hx)
            · exact Finset.mem_insert_self _ _
            · intro b hb
              exact qroot_common_bound b (by
                intro e he; exact hb ⟨e.A,e.H,e.height⟩ (List.mem_map.mpr ⟨e,he,rfl⟩))
          exact hr ∅ ∅ (Finset.Subset.refl _) (Finset.disjoint_empty_right _))
def qempty_winning_35 : Winning qGoal 35 ∅ ∅ := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          apply qempty_winning_of_opening_rows
          · have h := qr_threat (fun i hi hil => qe_valid_of_TableValid qtable_valid_probe i hi hil) 406 (by omega)
            rw [qmeq_406] at h
            exact h
          · have h := qr_threat (fun i hi hil => qe_valid_of_TableValid qtable_valid_probe i hi hil) 533 (by omega)
            rw [qmeq_533] at h
            exact h
          · have h := qr_threat (fun i hi hil => qe_valid_of_TableValid qtable_valid_probe i hi hil) 557 (by omega)
            rw [qmeq_557] at h
            exact h
          · have h := qr_threat (fun i hi hil => qe_valid_of_TableValid qtable_valid_probe i hi hil) 584 (by omega)
            rw [qmeq_584] at h
            exact h
          · have h := qr_threat (fun i hi hil => qe_valid_of_TableValid qtable_valid_probe i hi hil) 586 (by omega)
            rw [qmeq_586] at h
            exact h
          · have h := qr_threat (fun i hi hil => qe_valid_of_TableValid qtable_valid_probe i hi hil) 587 (by omega)
            rw [qmeq_587] at h
            exact h
          · have h := qr_threat (fun i hi hil => qe_valid_of_TableValid qtable_valid_probe i hi hil) 590 (by omega)
            rw [qmeq_590] at h
            exact h
          · have h := qr_threat (fun i hi hil => qe_valid_of_TableValid qtable_valid_probe i hi hil) 591 (by omega)
            rw [qmeq_591] at h
            exact h
          · have h := qr_threat (fun i hi hil => qe_valid_of_TableValid qtable_valid_probe i hi hil) 595 (by omega)
            rw [qmeq_595] at h
            exact h
          · have h := qr_threat (fun i hi hil => qe_valid_of_TableValid qtable_valid_probe i hi hil) 601 (by omega)
            rw [qmeq_601] at h
            exact h
          · have h := qr_threat (fun i hi hil => qe_valid_of_TableValid qtable_valid_probe i hi hil) 602 (by omega)
            rw [qmeq_602] at h
            exact h
          · have h := qr_threat (fun i hi hil => qe_valid_of_TableValid qtable_valid_probe i hi hil) 603 (by omega)
            rw [qmeq_603] at h
            exact h
          · have h := qr_threat (fun i hi hil => qe_valid_of_TableValid qtable_valid_probe i hi hil) 611 (by omega)
            rw [qmeq_611] at h
            exact h
          · have h := qr_threat (fun i hi hil => qe_valid_of_TableValid qtable_valid_probe i hi hil) 614 (by omega)
            rw [qmeq_614] at h
            exact h
          · have h := qr_threat (fun i hi hil => qe_valid_of_TableValid qtable_valid_probe i hi hil) 615 (by omega)
            rw [qmeq_615] at h
            exact h)
theorem snaky_winning_strategy_with_legal_states :
    ∃ σ : Policy Cell,
      (∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) ∧
      ∀ β : ℕ → Cell, LegalRepliesBeforeFinal σ 35 β ∅ ∅ →
        HasSnaky (playState σ 35 β ∅ ∅ 35).1 ∧
        (playState σ 35 β ∅ ∅ 35).1.card = 35 ∧
        Disjoint (playState σ 35 β ∅ ∅ 35).1 (playState σ 35 β ∅ ∅ 34).2 ∧
        ∀ k, k < 35 →
          Disjoint (playState σ 35 β ∅ ∅ k).1 (playState σ 35 β ∅ ∅ k).2 ∧
          (playState σ 35 β ∅ ∅ k).2.card = k := by
  exact ordinary_policy_of_winning HasSnaky 35 (by omega) qempty_winning_35
end OAI.SnakyConditional
