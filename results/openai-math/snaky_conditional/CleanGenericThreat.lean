import CleanOrdinaryBridge

namespace OAI.SnakyConditional.OrdinaryStrategy

variable {α : Type*} [DecidableEq α] [Infinite α]

lemma winning_of_goal (G : Finset α → Prop)
    (hG : ∀ {M M'}, M ⊆ M' → G M → G M')
    (n : ℕ) (M B : Finset α) (h : G M) : Winning G n M B := by
  induction n generalizing M B with
  | zero => exact h
  | succ n ih =>
      let a := freshCell M B
      have ha := freshCell_legal M B
      refine ⟨a, ha.1, ha.2, ?_⟩
      intro b hbM hbB
      exact ih (insert a M) (insert b B) (hG (Finset.subset_insert _ _) h)

lemma winning_mono_time (G : Finset α → Prop)
    (hG : ∀ {M M'}, M ⊆ M' → G M → G M')
    {n m : ℕ} (hnm : n ≤ m) (M B : Finset α) (h : Winning G n M B) :
    Winning G m M B := by
  induction n generalizing m M B with
  | zero => exact winning_of_goal G hG m M B h
  | succ n ih =>
      cases m with
      | zero => omega
      | succ m =>
          obtain ⟨a, haM, haB, hs⟩ := h
          refine ⟨a, haM, haB, ?_⟩
          intro b hbM hbB
          exact ih (by omega) _ _ (hs b hbM hbB)

def Threat (G : Finset α → Prop) (A H : Finset α) (n : ℕ) : Prop :=
  ∀ M B, A ⊆ M → Disjoint H B → Winning G n M B

lemma threat_leaf (G : Finset α → Prop)
    (hG : ∀ {M M'}, M ⊆ M' → G M → G M')
    (p : α) (S : Finset α) (hS : G S) : Threat G (S.erase p) S 1 := by
  intro M B hA hB
  by_cases hpM : p ∈ M
  · apply winning_of_goal G hG 1 M B
    apply hG ?_ hS
    intro x hx
    by_cases hxp : x = p
    · simpa [hxp] using hpM
    · exact hA (Finset.mem_erase.mpr ⟨hxp, hx⟩)
  · by_cases hpS : p ∈ S
    · have hpB : p ∉ B := fun h => Finset.disjoint_left.mp hB hpS h
      refine ⟨p, hpM, hpB, ?_⟩
      intro b hbM hbB
      change G (insert p M)
      apply hG ?_ hS
      intro x hx
      by_cases hxp : x = p
      · simp [hxp]
      · exact Finset.mem_insert_of_mem (hA (Finset.mem_erase.mpr ⟨hxp, hx⟩))
    · apply winning_of_goal G hG 1 M B
      apply hG ?_ hS
      intro x hx
      exact hA (Finset.mem_erase.mpr ⟨fun h => hpS (h ▸ hx), hx⟩)

lemma winning_map (G : Finset α → Prop) (e : α ≃ α)
    (hG : ∀ M, G M → G (M.image e))
    (n : ℕ) (M B : Finset α) (hw : Winning G n M B) :
    Winning G n (M.image e) (B.image e) := by
  induction n generalizing M B with
  | zero => exact hG M hw
  | succ n ih =>
      obtain ⟨a, haM, haB, hs⟩ := hw
      refine ⟨e a, ?_, ?_, ?_⟩
      · simpa using haM
      · simpa using haB
      · intro b hbM hbB
        have hbM' : e.symm b ∉ insert a M := by
          intro h
          apply hbM
          simpa only [Finset.image_insert, Equiv.apply_symm_apply] using
            (Finset.mem_image_of_mem e h)
        have hbB' : e.symm b ∉ B := by
          intro h
          apply hbB
          simpa only [Equiv.apply_symm_apply] using (Finset.mem_image_of_mem e h)
        simpa only [Finset.image_insert, Equiv.apply_symm_apply] using
          (ih (insert a M) (insert (e.symm b) B) (hs _ hbM' hbB'))

lemma threat_map (G : Finset α → Prop) (e : α ≃ α)
    (hG : ∀ M, G M → G (M.image e))
    (A H : Finset α) (n : ℕ) (hw : Threat G A H n) :
    Threat G (A.image e) (H.image e) n := by
  intro M B hAM hHB
  have hA : A ⊆ M.image e.symm := by
    intro a ha
    have h := hAM (Finset.mem_image_of_mem e ha)
    simpa only [Equiv.symm_apply_apply] using Finset.mem_image_of_mem e.symm h
  have hB : Disjoint H (B.image e.symm) := by
    apply Finset.disjoint_left.mpr
    intro a ha hab
    obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hab
    apply Finset.disjoint_left.mp hHB (Finset.mem_image_of_mem e ha)
    simpa [← hab] using hb
  have hh := winning_map G e hG n _ _ (hw _ _ hA hB)
  simpa only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply,
    Finset.image_id'] using hh

structure ThreatData (α : Type*) where
  A : Finset α
  H : Finset α
  height : ℕ

variable (G : Finset α → Prop)

lemma threat_fork (hG : ∀ {M M'}, M ⊆ M' → G M → G M')
    (p : α) (ds : List (ThreatData α)) (hne : ds ≠ []) (n : ℕ)
    (hs : ∀ d ∈ ds, Threat G d.A d.H d.height)
    (hh : ∀ d ∈ ds, d.height ≤ n)
    (A H : Finset α)
    (hA : ∀ d ∈ ds, d.A ⊆ insert p A)
    (hH : ∀ d ∈ ds, d.H ⊆ H) (hpH : p ∈ H)
    (hcommon : ∀ b, (∀ d ∈ ds, b ∈ d.H) → b ∈ insert p A) :
    Threat G A H (n + 1) := by
  intro M B hAM hHB
  have hMA : insert p A ⊆ insert p M := Finset.insert_subset_insert p hAM
  by_cases hpM : p ∈ M
  · obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil ds hne
    have hdA : d.A ⊆ M := by
      intro x hx
      rcases Finset.mem_insert.mp (hA d hd hx) with he | ha
      · simpa [he] using hpM
      · exact hAM ha
    have hdB : Disjoint d.H B := hHB.mono_left (hH d hd)
    exact winning_mono_time G hG (by have := hh d hd; omega) M B (hs d hd M B hdA hdB)
  · have hpB : p ∉ B := fun h => Finset.disjoint_left.mp hHB hpH h
    refine ⟨p, hpM, hpB, ?_⟩
    intro b hbM hbB
    have hex : ∃ d ∈ ds, b ∉ d.H := by
      by_contra hx
      push_neg at hx
      have hb := hcommon b hx
      exact hbM (hMA hb)
    obtain ⟨d, hd, hbd⟩ := hex
    have hdB : Disjoint d.H (insert b B) :=
      Finset.disjoint_insert_right.mpr ⟨hbd, hHB.mono_left (hH d hd)⟩
    exact winning_mono_time G hG (hh d hd) _ _
      (hs d hd (insert p M) (insert b B) (fun x hx => hMA (hA d hd hx)) hdB)

end OAI.SnakyConditional.OrdinaryStrategy
