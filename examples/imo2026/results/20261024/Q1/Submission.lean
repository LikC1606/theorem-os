import Mathlib
set_option backward.isDefEq.respectTransparency false

/-- A *board* is a finite multiset of natural numbers.  The full board discipline
(entries `≥ 1`, cardinality `2026`) is captured by the predicate `IsInitial`. -/
abbrev Board := Multiset ℕ

/-- An *initial board*: exactly `2026` entries, each strictly greater than `1`. -/
def IsInitial (B : Board) : Prop :=
  Multiset.card B = 2026 ∧ ∀ a ∈ B, 1 < a

/-- A single *move*: pick two entries `m, n` (from two distinct positions,
modelled as two separate elements of the multiset) both `> 1`, remove them and
insert `gcd(m, n)` and `lcm(m, n) / gcd(m, n)`.  Using `m ::ₘ n ::ₘ s` for the
source board automatically encodes that the two chosen positions are distinct
(they are two separate multiset elements, whose *values* may coincide). -/
def Move (B B' : Board) : Prop :=
  ∃ (m n : ℕ) (s : Board), 1 < m ∧ 1 < n ∧
    B = m ::ₘ n ::ₘ s ∧
    B' = Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s

/-- A board is *terminal* when at most one entry is `> 1`, so no move is possible. -/
def IsTerminal (B : Board) : Prop :=
  Multiset.card (B.filter (fun a => 1 < a)) ≤ 1

/-- A board has a *unique large entry* when exactly one entry is `> 1`. -/
def HasUniqueLarge (B : Board) : Prop :=
  Multiset.card (B.filter (fun a => 1 < a)) = 1

/-- `Reachable B B'` : `B'` can be obtained from `B` by a finite sequence of moves
(the reflexive–transitive closure of `Move`).  A finite play from `B` to a
terminal board `B'` is precisely a witness of `Reachable B B'` with `IsTerminal B'`. -/
def Reachable (B B' : Board) : Prop := Relation.ReflTransGen Move B B'

/-- The exponent `g_p` for a prime `p` and board `B`: the `gcd` of the `p`-adic
valuations of the entries of `B`.  Since `gcd(a, 0) = a`, valuations equal to `0`
(entries not divisible by `p`) do not affect this gcd, so `gExp p B` is the gcd of
the *positive* `p`-adic valuations occurring in `B`. -/
noncomputable def gExp (p : ℕ) (B : Board) : ℕ :=
  (B.map (fun a => padicValNat p a)).gcd

/-- The claimed invariant terminal value
`M = ∏_{p ∣ ∏ B} p ^ gExp p B`, the product over all primes dividing some entry
of `B` of `p` raised to the gcd of the `p`-adic valuations. -/
noncomputable def Mval (B : Board) : ℕ :=
  ∏ p ∈ B.prod.primeFactors, p ^ gExp p B

/-- **Statement (a), part 1 — termination.**  There is no infinite play starting
from an initial board `B₀`: no infinite sequence of boards can start at `B₀` and
have every consecutive pair related by a `Move`. -/
theorem statement_a_termination (B₀ : Board) (hB₀ : IsInitial B₀) :
    ¬ ∃ f : ℕ → Board, f 0 = B₀ ∧ ∀ k, Move (f k) (f (k + 1)) := by
  let largeCount (B : Board) := Multiset.card (B.filter (fun a => 1 < a))
  let measure (B : Board) := B.prod + largeCount B
  have move_preserves_pos : ∀ {B B' : Board},
      (∀ a ∈ B, 0 < a) → Move B B' → ∀ a ∈ B', 0 < a := by
    intro B B' hpos hstep
    rcases hstep with ⟨m, n, s, hm, hn, rfl, rfl⟩
    have hgpos : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n (by omega)
    have hlpos : 0 < Nat.lcm m n := Nat.lcm_pos (by omega) (by omega)
    have hgdl : Nat.gcd m n ∣ Nat.lcm m n :=
      (Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n)
    have hqpos : 0 < Nat.lcm m n / Nat.gcd m n :=
      Nat.div_pos (Nat.le_of_dvd hlpos hgdl) hgpos
    intro a ha
    simp only [Multiset.mem_cons] at ha ⊢
    rcases ha with rfl | rfl | ha
    · exact hgpos
    · exact hqpos
    · exact hpos a (by simp [ha])
  have measure_lt : ∀ {B B' : Board},
      (∀ a ∈ B, 0 < a) → Move B B' → measure B' < measure B := by
    intro B B' hpos hstep
    rcases hstep with ⟨m, n, s, hm, hn, rfl, rfl⟩
    let g := Nat.gcd m n
    let l := Nat.lcm m n
    let q := l / g
    let c := largeCount s
    change measure (g ::ₘ q ::ₘ s) < measure (m ::ₘ n ::ₘ s)
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left n (by omega)
    have hlpos : 0 < l := Nat.lcm_pos (by omega) (by omega)
    have hgdl : g ∣ l := (Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n)
    have hgq : g * q = l := Nat.mul_div_cancel' hgdl
    have hspos : 0 < s.prod := Multiset.prod_pos (by
      intro a ha
      exact hpos a (by simp [ha]))
    have hnewprod : (g ::ₘ q ::ₘ s).prod = l * s.prod := by
      simp only [Multiset.prod_cons]
      rw [← mul_assoc, hgq]
    have holdprod : (m ::ₘ n ::ₘ s).prod = g * (l * s.prod) := by
      simp only [Multiset.prod_cons]
      rw [← mul_assoc, ← Nat.gcd_mul_lcm m n]
      simp only [g, l, mul_assoc]
    have holdcount : largeCount (m ::ₘ n ::ₘ s) = 2 + c := by
      simp [largeCount, c, hm, hn] <;> omega
    have hnewcount_le : largeCount (g ::ₘ q ::ₘ s) ≤ 2 + c := by
      by_cases hg : 1 < g <;> by_cases hq : 1 < q <;>
        simp [largeCount, c, hg, hq] <;> omega
    by_cases hg1 : g = 1
    · have hml : m ≤ l := Nat.le_of_dvd hlpos (Nat.dvd_lcm_left m n)
      have hqgt : 1 < q := by simp [q, hg1]; omega
      have hnewcount : largeCount (g ::ₘ q ::ₘ s) = 1 + c := by
        simp [largeCount, c, hg1, hqgt] <;> omega
      simp only [measure]
      rw [hnewprod, holdprod, hnewcount, holdcount, hg1, one_mul]
      omega
    · have hggt : 1 < g := by omega
      have hcorepos : 0 < l * s.prod := Nat.mul_pos hlpos hspos
      have hprodlt : l * s.prod < g * (l * s.prod) := by nlinarith
      simp only [measure]
      rw [hnewprod, holdprod, holdcount]
      omega
  rintro ⟨f, hf0, hmove⟩
  have hpos : ∀ k a, a ∈ f k → 0 < a := by
    intro k
    induction k with
    | zero =>
        intro a ha
        rw [hf0] at ha
        exact (hB₀.2 a ha).trans' Nat.zero_lt_one
    | succ k ih =>
        exact move_preserves_pos ih (by simpa [Nat.add_comm] using hmove k)
  have hdec : ∀ k, measure (f (k + 1)) < measure (f k) := by
    intro k
    exact measure_lt (hpos k) (hmove k)
  have hbound : ∀ k, measure (f k) + k ≤ measure (f 0) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hd := hdec k
        omega
  have := hbound (measure (f 0) + 1)
  omega
/-- **Statement (a), part 2 — unique large entry.**  Any terminal board reachable
from an initial board `B₀` has exactly one entry `> 1`. -/
theorem statement_a_unique_large (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B') :
    HasUniqueLarge B' := by
  have move_has_large : ∀ {B C : Board}, Move B C →
      0 < Multiset.card (C.filter (fun a => 1 < a)) := by
    intro B C hmove
    rcases hmove with ⟨m, n, s, hm, hn, hB, rfl⟩
    by_cases hg : 1 < Nat.gcd m n
    · rw [Multiset.card_pos_iff_exists_mem]
      exact ⟨Nat.gcd m n, by simp [hg]⟩
    · have hgpos : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n (by omega)
      have hgeq : Nat.gcd m n = 1 := by omega
      have hlcm0 : Nat.lcm m n ≠ 0 := Nat.lcm_ne_zero (by omega) (by omega)
      have hmlcm : m ≤ Nat.lcm m n :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero hlcm0) (Nat.dvd_lcm_left m n)
      rw [Multiset.card_pos_iff_exists_mem]
      refine ⟨Nat.lcm m n / Nat.gcd m n, ?_⟩
      simp [hgeq, hm.trans_le hmlcm]
  have hpos : 0 < Multiset.card (B'.filter (fun a => 1 < a)) := by
    change Relation.ReflTransGen Move B₀ B' at hreach
    rcases hreach.cases_tail with hEq | ⟨C, hBC, hmove⟩
    · subst B'
      rw [Multiset.card_pos_iff_exists_mem]
      have hne : B₀ ≠ 0 := by
        intro hzero
        have := hB₀.1
        simp [hzero] at this
      obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp
        (Multiset.card_pos.mpr hne)
      exact ⟨a, Multiset.mem_filter.mpr ⟨ha, hB₀.2 a ha⟩⟩
    · exact move_has_large hmove
  change Multiset.card (B'.filter (fun a => 1 < a)) = 1
  change Multiset.card (B'.filter (fun a => 1 < a)) ≤ 1 at hterm
  omega
/-- **Statement (b) — invariance of `M`.**  Any two terminal boards reachable from
the same initial board `B₀` have the same set of entries `> 1`; since (by (a)) each
has exactly one such entry, this says the terminal value `M` is the same for both. -/
theorem statement_b_invariance (B₀ : Board) (hB₀ : IsInitial B₀)
    (B₁ B₂ : Board) (h₁ : Reachable B₀ B₁) (h₂ : Reachable B₀ B₂)
    (t₁ : IsTerminal B₁) (t₂ : IsTerminal B₂) :
    ∀ M, (1 < M ∧ M ∈ B₁) ↔ (1 < M ∧ M ∈ B₂) := by
  have factorGCD_euclid (a b c : ℕ) :
      Nat.gcd a (Nat.gcd b c) =
        Nat.gcd (min a b) (Nat.gcd (max a b - min a b) c) := by
    rcases le_total a b with hab | hba
    · rw [min_eq_left hab, max_eq_right hab]
      calc
        Nat.gcd a (Nat.gcd b c) = Nat.gcd (Nat.gcd a b) c := (Nat.gcd_assoc _ _ _).symm
        _ = Nat.gcd (Nat.gcd a (b - a)) c :=
          congrArg (fun x => Nat.gcd x c) (Nat.gcd_sub_self_right hab).symm
        _ = Nat.gcd a (Nat.gcd (b - a) c) := Nat.gcd_assoc _ _ _
    · rw [min_eq_right hba, max_eq_left hba]
      calc
        Nat.gcd a (Nat.gcd b c) = Nat.gcd (Nat.gcd a b) c := (Nat.gcd_assoc _ _ _).symm
        _ = Nat.gcd (Nat.gcd b a) c :=
          congrArg (fun x => Nat.gcd x c) (Nat.gcd_comm a b)
        _ = Nat.gcd (Nat.gcd b (a - b)) c :=
          congrArg (fun x => Nat.gcd x c) (Nat.gcd_sub_self_right hba).symm
        _ = Nat.gcd b (Nat.gcd (a - b) c) := Nat.gcd_assoc _ _ _
  have move_factorization_step (p m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
      (Nat.gcd m n).factorization p = min (m.factorization p) (n.factorization p) ∧
      (Nat.lcm m n / Nat.gcd m n).factorization p =
        max (m.factorization p) (n.factorization p) -
          min (m.factorization p) (n.factorization p) := by
    constructor
    · rw [Nat.factorization_gcd hm hn]
      rfl
    · rw [Nat.factorization_div (dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)),
        Nat.factorization_lcm hm hn, Nat.factorization_gcd hm hn]
      rfl
  let factorGCD (p : ℕ) (B : Board) : ℕ :=
    (B.map fun a => a.factorization p).gcd
  have factorGCD_move {B B' : Board} (h : Move B B') (p : ℕ) :
      factorGCD p B = factorGCD p B' := by
    rcases h with ⟨m, n, s, hm, hn, rfl, rfl⟩
    have hfac := move_factorization_step p m n (by omega) (by omega)
    simp only [factorGCD, Multiset.map_cons, Multiset.gcd_cons]
    rw [hfac.1, hfac.2]
    exact factorGCD_euclid _ _ _
  have factorGCD_reachable {B B' : Board} (h : Reachable B B') (p : ℕ) :
      factorGCD p B = factorGCD p B' := by
    unfold Reachable at h
    induction h with
    | refl => rfl
    | tail h hmove ih => exact ih.trans (factorGCD_move hmove p)
  have factorGCD_terminal {B : Board} (t : IsTerminal B)
      {M : ℕ} (hM : 1 < M) (hmem : M ∈ B) (p : ℕ) :
      factorGCD p B = M.factorization p := by
    have hcons : M ::ₘ B.erase M = B := Multiset.cons_erase hmem
    rw [← hcons] at t ⊢
    simp only [IsTerminal, Multiset.filter_cons_of_pos _ hM, Multiset.card_cons] at t
    have hcard : Multiset.card ((B.erase M).filter (fun z => 1 < z)) = 0 := by
      apply Nat.eq_zero_of_le_zero
      exact Nat.le_of_add_le_add_right t
    simp only [factorGCD, Multiset.map_cons, Multiset.gcd_cons]
    have hzero : ((B.erase M).map fun a => a.factorization p).gcd = 0 := by
      apply (Multiset.gcd_eq_zero_iff _).mpr
      intro x hx
      rcases Multiset.mem_map.mp hx with ⟨a, ha, rfl⟩
      have hnot : ¬ 1 < a := by
        intro ha1
        have haFilter : a ∈ (B.erase M).filter (fun z => 1 < z) :=
          Multiset.mem_filter.mpr ⟨ha, ha1⟩
        have hempty := Multiset.card_eq_zero.mp hcard
        rw [hempty] at haFilter
        simp at haFilter
      have ha01 : a = 0 ∨ a = 1 := by omega
      rcases ha01 with rfl | rfl <;> simp
    simp [hzero]
  have initial_large_exists : ∃ M, 1 < M ∧ M ∈ B₀ := by
    have hcardpos : 0 < Multiset.card B₀ := by
      rw [hB₀.1]
      norm_num
    have hne : B₀ ≠ 0 := Multiset.card_pos.mp hcardpos
    obtain ⟨M, hMmem⟩ := Multiset.exists_mem_of_ne_zero hne
    exact ⟨M, hB₀.2 M hMmem, hMmem⟩
  have move_large {B B' : Board} (h : Move B B') : ∃ M, 1 < M ∧ M ∈ B' := by
    rcases h with ⟨m, n, s, hm, hn, rfl, rfl⟩
    by_cases hg : 1 < Nat.gcd m n
    · exact ⟨Nat.gcd m n, hg, by simp⟩
    · have hgpos : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n (by omega)
      have hgone : Nat.gcd m n = 1 := by omega
      have hmlcm : m ≤ Nat.lcm m n :=
        Nat.le_of_dvd (Nat.lcm_pos (by omega) (by omega)) (Nat.dvd_lcm_left m n)
      have hlcm : 1 < Nat.lcm m n := lt_of_lt_of_le hm hmlcm
      have hquot : 1 < Nat.lcm m n / Nat.gcd m n := by simpa [hgone] using hlcm
      exact ⟨Nat.lcm m n / Nat.gcd m n, hquot, by simp⟩
  have reachable_large {B : Board} (h : Reachable B₀ B) : ∃ M, 1 < M ∧ M ∈ B := by
    unfold Reachable at h
    induction h with
    | refl => exact initial_large_exists
    | tail h hmove ih => exact move_large hmove
  obtain ⟨N₁, hN₁, hN₁mem⟩ := reachable_large h₁
  obtain ⟨N₂, hN₂, hN₂mem⟩ := reachable_large h₂
  intro M
  constructor
  · rintro ⟨hM, hMmem⟩
    have hMN₂ : M = N₂ := Nat.eq_of_factorization_eq (by omega) (by omega) fun p => by
      calc
        M.factorization p = factorGCD p B₁ := (factorGCD_terminal t₁ hM hMmem p).symm
        _ = factorGCD p B₀ := (factorGCD_reachable h₁ p).symm
        _ = factorGCD p B₂ := factorGCD_reachable h₂ p
        _ = N₂.factorization p := factorGCD_terminal t₂ hN₂ hN₂mem p
    exact ⟨hM, hMN₂ ▸ hN₂mem⟩
  · rintro ⟨hM, hMmem⟩
    have hMN₁ : M = N₁ := Nat.eq_of_factorization_eq (by omega) (by omega) fun p => by
      calc
        M.factorization p = factorGCD p B₂ := (factorGCD_terminal t₂ hM hMmem p).symm
        _ = factorGCD p B₀ := (factorGCD_reachable h₂ p).symm
        _ = factorGCD p B₁ := factorGCD_reachable h₁ p
        _ = N₁.factorization p := factorGCD_terminal t₁ hN₁ hN₁mem p
    exact ⟨hM, hMN₁ ▸ hN₁mem⟩
/-- **Value of `M` (correctness of the explicit formula).**  For any terminal board
`B'` reachable from an initial board `B₀`, the unique entry `M > 1` of `B'` equals
the invariant `Mval B₀`. -/
lemma factorization_gcd_sub_shift (a b c : ℕ) :
    Nat.gcd a (Nat.gcd b c) =
      Nat.gcd (min a b) (Nat.gcd (max a b - min a b) c) := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_right hab]
    calc
      Nat.gcd a (Nat.gcd b c) = Nat.gcd (Nat.gcd a b) c := (Nat.gcd_assoc _ _ _).symm
      _ = Nat.gcd (Nat.gcd a (b - a)) c :=
        congrArg (fun x => Nat.gcd x c) (Nat.gcd_sub_self_right hab).symm
      _ = Nat.gcd a (Nat.gcd (b - a) c) := Nat.gcd_assoc _ _ _
  · rw [min_eq_right hba, max_eq_left hba]
    calc
      Nat.gcd a (Nat.gcd b c) = Nat.gcd (Nat.gcd a b) c := (Nat.gcd_assoc _ _ _).symm
      _ = Nat.gcd (Nat.gcd b a) c :=
        congrArg (fun x => Nat.gcd x c) (Nat.gcd_comm a b)
      _ = Nat.gcd (Nat.gcd b (a - b)) c :=
        congrArg (fun x => Nat.gcd x c) (Nat.gcd_sub_self_right hba).symm
      _ = Nat.gcd b (Nat.gcd (a - b) c) := Nat.gcd_assoc _ _ _
lemma move_padic_pair (p m n : ℕ) (hp : p.Prime) (hm : m ≠ 0) (hn : n ≠ 0) :
    Nat.gcd (padicValNat p (Nat.gcd m n))
        (padicValNat p (Nat.lcm m n / Nat.gcd m n)) =
      Nat.gcd (padicValNat p m) (padicValNat p n) := by
  let x := padicValNat p m
  let y := padicValNat p n
  have hd : Nat.gcd m n ∣ Nat.lcm m n :=
    (Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n)
  have hvg : padicValNat p (Nat.gcd m n) = min x y := by
    rw [← Nat.factorization_def (Nat.gcd m n) hp, Nat.factorization_gcd hm hn]
    simp [x, y, Nat.factorization_def m hp, Nat.factorization_def n hp]
  have hvq : padicValNat p (Nat.lcm m n / Nat.gcd m n) = max x y - min x y := by
    rw [← Nat.factorization_def (Nat.lcm m n / Nat.gcd m n) hp,
      Nat.factorization_div hd, Nat.factorization_lcm hm hn, Nat.factorization_gcd hm hn]
    simp [x, y, Nat.factorization_def m hp, Nat.factorization_def n hp]
  rw [hvg, hvq]
  by_cases hxy : x ≤ y
  · rw [min_eq_left hxy, max_eq_right hxy, Nat.gcd_sub_self_right hxy]
  · have hyx : y ≤ x := Nat.le_of_not_ge hxy
    rw [min_eq_right hyx, max_eq_left hyx, Nat.gcd_comm y (x - y),
      Nat.gcd_sub_self_left hyx]
lemma primeFactors_lcm_of_pos (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    (Nat.lcm m n).primeFactors = m.primeFactors ∪ n.primeFactors := by
  rw [← Nat.support_factorization, Nat.factorization_lcm hm hn,
    Finsupp.support_sup, Nat.support_factorization, Nat.support_factorization]
lemma move_gExp_invariant (p : ℕ) (hp : p.Prime) {B C : Board}
    (hmove : Move B C) : gExp p C = gExp p B := by
  rcases hmove with ⟨m, n, s, hm, hn, rfl, rfl⟩
  unfold gExp
  simp only [Multiset.map_cons, Multiset.gcd_cons, gcd_eq_nat_gcd]
  rw [← Nat.gcd_assoc,
    move_padic_pair p m n hp (by omega) (by omega), Nat.gcd_assoc]
lemma move_primeFactors_invariant {B C : Board} (hmove : Move B C) :
    C.prod.primeFactors = B.prod.primeFactors := by
  rcases hmove with ⟨m, n, s, hm, hn, rfl, rfl⟩
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  by_cases hs0 : s.prod = 0
  · simp [Multiset.prod_cons, hs0]
  · have hl0 : Nat.lcm m n ≠ 0 := Nat.lcm_ne_zero hm0 hn0
    have hd : Nat.gcd m n ∣ Nat.lcm m n :=
      (Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n)
    have hcollapse :
        Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n * s.prod) =
          Nat.lcm m n * s.prod := by
      rw [← Nat.mul_assoc, Nat.mul_div_cancel' hd]
    simp only [Multiset.prod_cons]
    rw [hcollapse, ← Nat.mul_assoc m n s.prod, Nat.primeFactors_mul hl0 hs0,
      Nat.primeFactors_mul (mul_ne_zero hm0 hn0) hs0,
      Nat.primeFactors_mul hm0 hn0, primeFactors_lcm_of_pos m n hm0 hn0]
lemma move_Mval_invariant {B C : Board} (hmove : Move B C) : Mval C = Mval B := by
  unfold Mval
  apply Finset.prod_congr (move_primeFactors_invariant hmove)
  intro p hp
  rw [move_gExp_invariant p (Nat.prime_of_mem_primeFactors hp) hmove]
lemma reachable_Mval_invariant {B C : Board} (hreach : Reachable B C) :
    Mval C = Mval B := by
  unfold Reachable at hreach
  induction hreach with
  | refl => rfl
  | tail h hmove ih => exact (move_Mval_invariant hmove).trans ih
lemma move_preserves_positive {B C : Board} (hmove : Move B C)
    (hpos : ∀ a ∈ B, 0 < a) : ∀ a ∈ C, 0 < a := by
  rcases hmove with ⟨m, n, s, hm, hn, rfl, rfl⟩
  intro a ha
  simp only [Multiset.mem_cons] at ha
  rcases ha with rfl | rfl | ha
  · exact Nat.gcd_pos_of_pos_left n (by omega)
  · have hm0 : m ≠ 0 := by omega
    have hn0 : n ≠ 0 := by omega
    have hgpos : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n (by omega)
    have hlpos : 0 < Nat.lcm m n := Nat.pos_of_ne_zero (Nat.lcm_ne_zero hm0 hn0)
    have hd : Nat.gcd m n ∣ Nat.lcm m n :=
      (Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n)
    exact Nat.div_pos (Nat.le_of_dvd hlpos hd) hgpos
  · exact hpos a (by simp [ha])
lemma reachable_preserves_positive {B C : Board} (hreach : Reachable B C)
    (hpos : ∀ a ∈ B, 0 < a) : ∀ a ∈ C, 0 < a := by
  unfold Reachable at hreach
  induction hreach with
  | refl => exact hpos
  | tail h hmove ih => exact move_preserves_positive hmove ih
lemma terminal_gExp_eq (B : Board) (M p : ℕ) (hterm : IsTerminal B)
    (hM : 1 < M) (hMem : M ∈ B) : gExp p B = padicValNat p M := by
  have hcons : M ::ₘ B.erase M = B := Multiset.cons_erase hMem
  rw [← hcons] at hterm ⊢
  simp only [IsTerminal, Multiset.filter_cons_of_pos _ hM, Multiset.card_cons] at hterm
  have hcard : Multiset.card ((B.erase M).filter (fun z => 1 < z)) = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact Nat.le_of_add_le_add_right hterm
  unfold gExp
  simp only [Multiset.map_cons, Multiset.gcd_cons, gcd_eq_nat_gcd]
  have hzero : ((B.erase M).map fun a => padicValNat p a).gcd = 0 := by
    apply (Multiset.gcd_eq_zero_iff _).mpr
    intro x hx
    rcases Multiset.mem_map.mp hx with ⟨a, ha, rfl⟩
    have hnot : ¬ 1 < a := by
      intro ha1
      have haFilter : a ∈ (B.erase M).filter (fun z => 1 < z) :=
        Multiset.mem_filter.mpr ⟨ha, ha1⟩
      have hempty := Multiset.card_eq_zero.mp hcard
      rw [hempty] at haFilter
      simp at haFilter
    have ha01 : a = 0 ∨ a = 1 := by omega
    rcases ha01 with rfl | rfl <;> simp
  simp [hzero]
lemma terminal_prod_eq (B : Board) (M : ℕ) (hterm : IsTerminal B)
    (hM : 1 < M) (hMem : M ∈ B) (hpos : ∀ a ∈ B, 0 < a) : B.prod = M := by
  have hcons : M ::ₘ B.erase M = B := Multiset.cons_erase hMem
  rw [← hcons] at hterm
  simp only [IsTerminal, Multiset.filter_cons_of_pos _ hM, Multiset.card_cons] at hterm
  have hcard : Multiset.card ((B.erase M).filter (fun z => 1 < z)) = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact Nat.le_of_add_le_add_right hterm
  have hall : ∀ a ∈ B.erase M, a = 1 := by
    intro a ha
    have haB : a ∈ B := by
      rw [← hcons]
      simp [ha]
    have hapos : 0 < a := hpos a haB
    have hnot : ¬ 1 < a := by
      intro ha1
      have haFilter : a ∈ (B.erase M).filter (fun z => 1 < z) :=
        Multiset.mem_filter.mpr ⟨ha, ha1⟩
      have hempty := Multiset.card_eq_zero.mp hcard
      rw [hempty] at haFilter
      simp at haFilter
    omega
  have hprod : (B.erase M).prod = 1 := Multiset.prod_eq_one hall
  rw [← hcons, Multiset.prod_cons, hprod, mul_one]
lemma terminal_Mval_eq (B : Board) (M : ℕ) (hterm : IsTerminal B)
    (hM : 1 < M) (hMem : M ∈ B) (hpos : ∀ a ∈ B, 0 < a) : Mval B = M := by
  have hprod := terminal_prod_eq B M hterm hM hMem hpos
  unfold Mval
  rw [hprod]
  calc
    (∏ p ∈ M.primeFactors, p ^ gExp p B) =
        ∏ p ∈ M.primeFactors, p ^ M.factorization p := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [terminal_gExp_eq B M p hterm hM hMem]
      rw [← Nat.factorization_def M (Nat.prime_of_mem_primeFactors hp)]
    _ = M := by
      rw [← Nat.prod_factorization_eq_prod_primeFactors]
      exact Nat.prod_factorization_pow_eq_self (by omega)
theorem terminal_value_eq_Mval (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B')
    (M : ℕ) (hM : 1 < M) (hMem : M ∈ B') :
    M = Mval B₀ := by
  have hpos0 : ∀ a ∈ B₀, 0 < a := by
    intro a ha
    exact (hB₀.2 a ha).trans' Nat.zero_lt_one
  have hpos' : ∀ a ∈ B', 0 < a := reachable_preserves_positive hreach hpos0
  have hterminal := terminal_Mval_eq B' M hterm hM hMem hpos'
  have hinvariant := reachable_Mval_invariant hreach
  exact hterminal.symm.trans hinvariant
/-- The invariant terminal value is itself `> 1`, since all initial entries exceed
`1`. -/
theorem Mval_gt_one (B₀ : Board) (hB₀ : IsInitial B₀) : 1 < Mval B₀ := by
  have hcard : 0 < Multiset.card B₀ := by rw [hB₀.1]; norm_num
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp hcard
  have hprod : 1 < B₀.prod := by
    exact lt_of_lt_of_le (hB₀.2 a ha)
      (Multiset.single_le_prod (fun x hx => (hB₀.2 x hx).le) a ha)
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hprod
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  haveI : Fact p.Prime := ⟨hpprime⟩
  obtain ⟨b, hb, hpdiv⟩ := hpprime.prime.exists_mem_multiset_dvd
    (Nat.dvd_of_mem_primeFactors hp)
  have hval : padicValNat p b ≠ 0 := by
    have hval_le : 1 ≤ padicValNat p b :=
      one_le_padicValNat_of_dvd
        (Nat.ne_of_gt (Nat.zero_lt_one.trans (hB₀.2 b hb))) hpdiv
    omega
  have hgexp : gExp p B₀ ≠ 0 := by
    rw [gExp, Multiset.gcd_ne_zero_iff]
    have hmem : padicValNat p b ∈ B₀.map (fun a => padicValNat p a) := by
      exact Multiset.mem_map.mpr ⟨b, hb, rfl⟩
    exact ⟨padicValNat p b, hmem, hval⟩
  have hall : ∀ q ∈ B₀.prod.primeFactors, 1 ≤ q ^ gExp q B₀ := by
    intro q hq
    exact Nat.one_le_pow (gExp q B₀) q (Nat.prime_of_mem_primeFactors hq).pos
  rw [Mval]
  exact (Finset.one_lt_prod_iff_of_one_le hall).2
    ⟨p, hp, Nat.one_lt_pow hgexp hpprime.one_lt⟩
