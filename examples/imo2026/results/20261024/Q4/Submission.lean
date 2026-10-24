import Mathlib
set_option backward.isDefEq.respectTransparency false

namespace TriangleGame

/-- A triangle, viewed as the multiset of its three interior angles (in degrees):
positive reals summing to `180`. -/
def IsTriangle (s : Multiset ℝ) : Prop :=
  s.card = 3 ∧ (∀ x ∈ s, 0 < x) ∧ s.sum = 180

/-- A triangle `s` has an interior angle equal to `θ`. -/
def HasAngle (θ : ℝ) (s : Multiset ℝ) : Prop := θ ∈ s

/-- One admissible cut of the triangle `s`, producing children `L` and `R`.

We pick an apex angle `α` and the two base angles `β, γ` (so `s = {α, β, γ}`), and a
cut parameter `x` in the open interval `(γ, 180 - β)`. The resulting two triangles
have angle multisets `L = {β, x, 180 - β - x}` and `R = {γ, 180 - x, x - γ}`.
Ranging over all `α, β, γ` with `s = {α, β, γ}` captures all three apex choices and
both assignments of the two base angles. -/
def IsCut (s L R : Multiset ℝ) : Prop :=
  ∃ α β γ x : ℝ,
    s = {α, β, γ} ∧ γ < x ∧ x < 180 - β ∧
      L = {β, x, 180 - β - x} ∧ R = {γ, 180 - x, x - γ}

/-- The set of triangles from which Mulan can force, in finitely many steps, a
triangle with an interior angle equal to `θ`, no matter how Shan-Yu discards.

This is the least predicate closed under:
* (`win`) if the current triangle already has an angle equal to `θ`, Mulan has won;
* (`move`) if Mulan can make a cut producing children `L` and `R` from *both* of
  which she wins (so whichever one Shan-Yu keeps, she still wins), then she wins
  from the current triangle.

Membership means Mulan wins in finitely many steps. -/
inductive MulanWins (θ : ℝ) : Multiset ℝ → Prop
  | win {s : Multiset ℝ} (h : HasAngle θ s) : MulanWins θ s
  | move {s L R : Multiset ℝ} (hcut : IsCut s L R)
      (hL : MulanWins θ L) (hR : MulanWins θ R) : MulanWins θ s

/-- Mulan can guarantee victory for the value `θ`: from every valid starting
triangle she wins in finitely many steps regardless of Shan-Yu's play. -/
def MulanCanGuarantee (θ : ℝ) : Prop :=
  ∀ s : Multiset ℝ, IsTriangle s → MulanWins θ s

/-- **Main theorem.** For `0 < θ < 180`, Mulan can guarantee her victory in finitely
many steps, no matter how Shan-Yu plays, if and only if `θ = 180 / n` for some
integer `n ≥ 2`. -/
lemma self_mem_zmultiples (θ : ℝ) :
    θ ∈ AddSubgroup.zmultiples θ := by
  rw [AddSubgroup.mem_zmultiples_iff]
  exact ⟨1, by simp⟩
lemma wins_zmultiples_invariant (θ : ℝ) {s : Multiset ℝ}
    (hwin : MulanWins θ s) (hsum : s.sum = 180) :
    (180 : ℝ) ∈ AddSubgroup.zmultiples θ ∨
      ∃ a ∈ s, a ∈ AddSubgroup.zmultiples θ := by
  induction hwin with
  | win h =>
      exact Or.inr ⟨θ, h, self_mem_zmultiples θ⟩
  | @move s L R hcut hL hR ihL ihR =>
      rcases hcut with ⟨α, β, γ, x, hs, hx1, hx2, hLdef, hRdef⟩
      have hLsum : L.sum = 180 := by
        rw [hLdef]
        simp
      have hRsum : R.sum = 180 := by
        rw [hRdef]
        simp
      rcases ihL hLsum with h180 | ⟨a, haL, haH⟩
      · exact Or.inl h180
      rcases ihR hRsum with h180 | ⟨b, hbR, hbH⟩
      · exact Or.inl h180
      have haCases : a = β ∨ a = x ∨ a = 180 - β - x := by
        simpa [hLdef] using haL
      have hbCases : b = γ ∨ b = 180 - x ∨ b = x - γ := by
        simpa [hRdef] using hbR
      have hα : α = 180 - β - γ := by
        rw [hs] at hsum
        simp at hsum
        linarith
      rcases haCases with ha | ha | ha
      · rw [ha] at haH
        exact Or.inr ⟨β, by simp [hs], haH⟩
      · rw [ha] at haH
        rcases hbCases with hb | hb | hb
        · rw [hb] at hbH
          exact Or.inr ⟨γ, by simp [hs], hbH⟩
        · rw [hb] at hbH
          exact Or.inl (by
            convert (AddSubgroup.zmultiples θ).add_mem haH hbH using 1 <;> ring)
        · rw [hb] at hbH
          exact Or.inr ⟨γ, by simp [hs], by
            convert (AddSubgroup.zmultiples θ).sub_mem haH hbH using 1 <;> ring⟩
      · rw [ha] at haH
        rcases hbCases with hb | hb | hb
        · rw [hb] at hbH
          exact Or.inr ⟨γ, by simp [hs], hbH⟩
        · rw [hb] at hbH
          exact Or.inr ⟨β, by simp [hs], by
            convert (AddSubgroup.zmultiples θ).sub_mem hbH haH using 1 <;> ring⟩
        · rw [hb] at hbH
          exact Or.inr ⟨α, by simp [hs], by
            rw [hα]
            have h := (AddSubgroup.zmultiples θ).add_mem haH hbH
            convert h using 1 <;> ring⟩
lemma exists_of_180_mem_zmultiples (θ : ℝ) (hθ0 : 0 < θ) (hθ180 : θ < 180)
    (h180mem : (180 : ℝ) ∈ AddSubgroup.zmultiples θ) :
    ∃ n : ℕ, 2 ≤ n ∧ θ = 180 / n := by
  rw [AddSubgroup.mem_zmultiples_iff] at h180mem
  rcases h180mem with ⟨z, hz⟩
  have hzpos : 0 < z := by
    have hzposR : (0 : ℝ) < (z : ℝ) := by
      rw [zsmul_eq_mul] at hz
      nlinarith
    exact_mod_cast hzposR
  rcases Int.eq_ofNat_of_zero_le (le_of_lt hzpos) with ⟨n, rfl⟩
  have hnθ : (n : ℝ) * θ = 180 := by
    simpa [zsmul_eq_mul] using hz
  have hn0 : n ≠ 0 := by
    intro hn
    subst n
    norm_num at hnθ
  have hn1 : n ≠ 1 := by
    intro hn
    subst n
    norm_num at hnθ
    linarith
  refine ⟨n, by omega, ?_⟩
  apply (eq_div_iff (by exact_mod_cast hn0)).2
  nlinarith
lemma guarantee_implies_exists (θ : ℝ) (hθ0 : 0 < θ) (hθ180 : θ < 180)
    (hguar : MulanCanGuarantee θ) :
    ∃ n : ℕ, 2 ≤ n ∧ θ = 180 / n := by
  let s : Multiset ℝ := {(60 : ℝ), 60, 60}
  have hs : IsTriangle s := by
    refine ⟨by simp [s], ?_, by norm_num [s]⟩
    intro x hx
    simp [s] at hx
    norm_num [hx]
  have hwin := hguar s hs
  rcases wins_zmultiples_invariant θ hwin hs.2.2 with h180mem | ⟨a, ha, haH⟩
  · exact exists_of_180_mem_zmultiples θ hθ0 hθ180 h180mem
  · have ha60 : a = 60 := by simpa [s] using ha
    rw [ha60] at haH
    have h180mem : (180 : ℝ) ∈ AddSubgroup.zmultiples θ := by
      have hz3 := (AddSubgroup.zmultiples θ).zsmul_mem haH (3 : ℤ)
      convert hz3 using 1 <;> norm_num
    exact exists_of_180_mem_zmultiples θ hθ0 hθ180 h180mem
lemma wins_explicit_multiple (θ : ℝ) (hθ : 0 < θ) :
    ∀ m : ℕ, 1 ≤ m → ∀ a b : ℝ, 0 < a → 0 < b →
      (m : ℝ) * θ + a + b = 180 → MulanWins θ {a, b, (m : ℝ) * θ} := by
  intro m
  induction m with
  | zero => omega
  | succ m ih =>
      intro hm a b ha hb hsum
      by_cases hm0 : m = 0
      · subst m
        apply MulanWins.win
        simp [HasAngle]
      · have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
        let L : Multiset ℝ := {a, b + θ, 180 - a - (b + θ)}
        let R : Multiset ℝ := {b, 180 - (b + θ), (b + θ) - b}
        apply MulanWins.move (L := L) (R := R)
        · refine ⟨(Nat.succ m : ℕ) * θ, a, b, b + θ, ?_, by linarith, ?_, rfl, rfl⟩
          · simp only [Nat.cast_succ]
            rw [add_mul]
            calc
              {a, b, (m : ℝ) * θ + 1 * θ} = {a, (m : ℝ) * θ + 1 * θ, b} :=
                congrArg (Multiset.cons a) (Multiset.cons_swap _ _ 0)
              _ = {(m : ℝ) * θ + 1 * θ, a, b} := Multiset.cons_swap _ _ _
          · norm_num [Nat.cast_succ] at hsum
            have hmcast : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
            nlinarith
        · have hsum' : (m : ℝ) * θ + a + (b + θ) = 180 := by
            norm_num [Nat.cast_succ] at hsum
            linarith
          have hrec := ih hmpos a (b + θ) ha (by linarith) hsum'
          dsimp [L]
          rw [show 180 - a - (b + θ) = (m : ℝ) * θ by
            norm_num [Nat.cast_succ] at hsum
            linarith]
          exact hrec
        · apply MulanWins.win
          simp [R, HasAngle]
lemma exists_nat_mul_between (θ α γ : ℝ) (hθ : 0 < θ) (hγ : 0 ≤ γ) (hα : θ < α) :
    ∃ k : ℕ, γ < (k : ℝ) * θ ∧ (k : ℝ) * θ < γ + α := by
  let k : ℕ := ⌊γ / θ⌋₊ + 1
  have hdiv : 0 ≤ γ / θ := div_nonneg hγ hθ.le
  have hlo_div : γ / θ < (k : ℝ) := by
    simpa [k, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (γ / θ)
  have hhi_div : ((⌊γ / θ⌋₊ : ℕ) : ℝ) ≤ γ / θ := Nat.floor_le hdiv
  have hθne : θ ≠ 0 := ne_of_gt hθ
  have hlo := mul_lt_mul_of_pos_right hlo_div hθ
  have hhi := mul_le_mul_of_nonneg_right hhi_div hθ.le
  rw [div_mul_cancel₀ γ hθne] at hlo hhi
  refine ⟨k, hlo, ?_⟩
  dsimp [k]
  push_cast
  nlinarith
lemma win_two_bases_lt (θ α β γ : ℝ) (hθ : 0 < θ)
    (hβ : β < θ) (hγ : γ < θ) (htotal : 2 * θ = 180) :
    MulanWins θ {α, β, γ} := by
  let L : Multiset ℝ := {β, θ, 180 - β - θ}
  let R : Multiset ℝ := {γ, 180 - θ, θ - γ}
  apply MulanWins.move (L := L) (R := R)
  · exact ⟨α, β, γ, θ, rfl, hγ, by linarith, rfl, rfl⟩
  · apply MulanWins.win
    simp [L, HasAngle]
  · apply MulanWins.win
    simp [R, HasAngle, show 180 - θ = θ by linarith]
lemma win_apex_gt (θ : ℝ) (hθ : 0 < θ) (n : ℕ) (htotal : (n : ℝ) * θ = 180)
    (α β γ : ℝ) (hα : θ < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hsum : α + β + γ = 180) : MulanWins θ {α, β, γ} := by
  obtain ⟨k, hklo, hkhi⟩ := exists_nat_mul_between θ α γ hθ hγ.le hα
  have hkpos : 1 ≤ k := by
    have : 0 < (k : ℝ) := by nlinarith
    exact_mod_cast this
  have hklt : k < n := by
    have hkn : (k : ℝ) * θ < (n : ℝ) * θ := by
      rw [htotal]
      linarith
    have hcast : (k : ℝ) < (n : ℝ) := by nlinarith
    exact_mod_cast hcast
  have hnkpos : 1 ≤ n - k := Nat.sub_pos_iff_lt.mpr hklt
  let L : Multiset ℝ := {β, (k : ℝ) * θ, 180 - β - (k : ℝ) * θ}
  let R : Multiset ℝ := {γ, 180 - (k : ℝ) * θ, (k : ℝ) * θ - γ}
  apply MulanWins.move (L := L) (R := R)
  · exact ⟨α, β, γ, (k : ℝ) * θ, rfl, hklo, by linarith, rfl, rfl⟩
  · have hthird : 0 < 180 - β - (k : ℝ) * θ := by linarith
    have hrec := wins_explicit_multiple θ hθ k hkpos β
      (180 - β - (k : ℝ) * θ) hβ hthird (by ring)
    dsimp [L]
    change MulanWins θ
      (β ::ₘ ((k : ℝ) * θ) ::ₘ (180 - β - (k : ℝ) * θ) ::ₘ 0)
    rw [Multiset.cons_swap ((k : ℝ) * θ) (180 - β - (k : ℝ) * θ) 0]
    exact hrec
  · have hdiff : 0 < (k : ℝ) * θ - γ := by linarith
    have hmultiple : ((n - k : ℕ) : ℝ) * θ = 180 - (k : ℝ) * θ := by
      rw [Nat.cast_sub hklt.le]
      linarith
    have hrec := wins_explicit_multiple θ hθ (n - k) hnkpos γ
      ((k : ℝ) * θ - γ) hγ hdiff (by rw [hmultiple]; ring)
    dsimp [R]
    rw [← hmultiple]
    change MulanWins θ
      (γ ::ₘ (((n - k : ℕ) : ℝ) * θ) ::ₘ ((k : ℝ) * θ - γ) ::ₘ 0)
    rw [Multiset.cons_swap (((n - k : ℕ) : ℝ) * θ) ((k : ℝ) * θ - γ) 0]
    exact hrec
lemma exists_implies_guarantee (θ : ℝ) (hθ0 : 0 < θ) :
    ∀ n : ℕ, 2 ≤ n → θ = 180 / n → MulanCanGuarantee θ := by
  intro n hn hθn s hs
  have hn0 : n ≠ 0 := by omega
  have htotal : (n : ℝ) * θ = 180 := by
    rw [hθn]
    field_simp
  rcases Multiset.card_eq_three.mp hs.1 with ⟨a, b, c, rfl⟩
  have ha : 0 < a := hs.2.1 a (by simp)
  have hb : 0 < b := hs.2.1 b (by simp)
  have hc : 0 < c := hs.2.1 c (by simp)
  have hsum : a + b + c = 180 := by simpa [add_assoc] using hs.2.2
  by_cases haθ : a = θ
  · apply MulanWins.win
    simp [HasAngle, haθ]
  by_cases hbθ : b = θ
  · apply MulanWins.win
    simp [HasAngle, hbθ]
  by_cases hcθ : c = θ
  · apply MulanWins.win
    simp [HasAngle, hcθ]
  by_cases hn2 : n = 2
  · subst n
    have htwo : 2 * θ = 180 := by norm_num at htotal ⊢; exact htotal
    rcases lt_or_gt_of_ne haθ with ha_lt | ha_gt
    · rcases lt_or_gt_of_ne hbθ with hb_lt | hb_gt
      · have h := win_two_bases_lt θ c a b hθ0 ha_lt hb_lt htwo
        change MulanWins θ (a ::ₘ b ::ₘ c ::ₘ 0)
        rw [Multiset.cons_swap b c 0]
        rw [Multiset.cons_swap a c (b ::ₘ 0)]
        exact h
      · have hc_lt : c < θ := by nlinarith
        have h := win_two_bases_lt θ b a c hθ0 ha_lt hc_lt htwo
        change MulanWins θ (a ::ₘ b ::ₘ c ::ₘ 0)
        rw [Multiset.cons_swap a b (c ::ₘ 0)]
        exact h
    · have hb_lt : b < θ := by nlinarith
      have hc_lt : c < θ := by nlinarith
      exact win_two_bases_lt θ a b c hθ0 hb_lt hc_lt htwo
  · have hn3 : 3 ≤ n := by omega
    have hncast : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
    have hgt : θ < a ∨ θ < b ∨ θ < c := by
      by_contra h
      push_neg at h
      have ha_lt : a < θ := lt_of_le_of_ne h.1 haθ
      have hb_lt : b < θ := lt_of_le_of_ne h.2.1 hbθ
      have hc_lt : c < θ := lt_of_le_of_ne h.2.2 hcθ
      nlinarith
    rcases hgt with ha_gt | hb_gt | hc_gt
    · exact win_apex_gt θ hθ0 n htotal a b c ha_gt hb hc hsum
    · have h := win_apex_gt θ hθ0 n htotal b a c hb_gt ha hc (by linarith)
      change MulanWins θ (a ::ₘ b ::ₘ c ::ₘ 0)
      rw [Multiset.cons_swap a b (c ::ₘ 0)]
      exact h
    · have h := win_apex_gt θ hθ0 n htotal c a b hc_gt ha hb (by linarith)
      change MulanWins θ (a ::ₘ b ::ₘ c ::ₘ 0)
      rw [Multiset.cons_swap b c 0]
      rw [Multiset.cons_swap a c (b ::ₘ 0)]
      exact h
theorem main_theorem (θ : ℝ) (hθ0 : 0 < θ) (hθ180 : θ < 180) :
    MulanCanGuarantee θ ↔ ∃ n : ℕ, 2 ≤ n ∧ θ = 180 / n := by
  constructor
  · exact guarantee_implies_exists θ hθ0 hθ180
  · rintro ⟨n, hn, hθn⟩
    exact exists_implies_guarantee θ hθ0 n hn hθn
end TriangleGame
