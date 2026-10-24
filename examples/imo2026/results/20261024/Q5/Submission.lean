import Mathlib
set_option backward.isDefEq.respectTransparency false

/-- The subtype of positive real numbers, representing `\mathbb{R}_{>0}`. -/
abbrev PositiveReal : Type := {x : ℝ // 0 < x}

/-- The two-sided inequality defining admissible functions on positive real numbers. -/
def IsAdmissible (f : PositiveReal → PositiveReal) : Prop :=
  ∀ x y : PositiveReal,
    Real.sqrt (((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2) ≥
        ((f x : ℝ) + (y : ℝ)) / 2 ∧
      ((f x : ℝ) + (y : ℝ)) / 2 ≥
        Real.sqrt ((x : ℝ) * (f y : ℝ))

def increment (f : PositiveReal → PositiveReal) (x : PositiveReal) : ℝ :=
  (f x : ℝ) - (x : ℝ)
theorem admissible_sq_bounds {f : PositiveReal → PositiveReal}
    (hf : IsAdmissible f) (x y : PositiveReal) :
    4 * (x : ℝ) * (f y : ℝ) ≤ ((f x : ℝ) + (y : ℝ)) ^ 2 ∧
      ((f x : ℝ) + (y : ℝ)) ^ 2 ≤ 2 * (x : ℝ) ^ 2 + 2 * (f y : ℝ) ^ 2 := by
  have hx : 0 < (x : ℝ) := x.property
  have hy : 0 < (y : ℝ) := y.property
  have hfy : 0 < (f y : ℝ) := (f y).property
  have hfx : 0 < (f x : ℝ) := (f x).property
  have hrad₁ : 0 ≤ ((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2 := by positivity
  have hrad₂ : 0 ≤ (x : ℝ) * (f y : ℝ) := by positivity
  have hroot₁ := Real.sq_sqrt hrad₁
  have hroot₂ := Real.sq_sqrt hrad₂
  have hmid₁ := (hf x y).1
  have hmid₂ := (hf x y).2
  have h₁ : (x : ℝ) * (f y : ℝ) ≤ (((f x : ℝ) + (y : ℝ)) / 2) ^ 2 := by
    have hprod := mul_nonneg
      (sub_nonneg.mpr hmid₂)
      (add_nonneg (Real.sqrt_nonneg ((x : ℝ) * (f y : ℝ)))
        (by positivity : 0 ≤ ((f x : ℝ) + (y : ℝ)) / 2))
    nlinarith [hroot₂]
  have h₂ : (((f x : ℝ) + (y : ℝ)) / 2) ^ 2 ≤
      ((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2 := by
    have hprod := mul_nonneg
      (sub_nonneg.mpr hmid₁)
      (add_nonneg
        (Real.sqrt_nonneg (((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2))
        (by positivity : 0 ≤ ((f x : ℝ) + (y : ℝ)) / 2))
    nlinarith [hroot₁]
  constructor <;> nlinarith [h₁, h₂]
theorem admissible_forced_orbit {f : PositiveReal → PositiveReal}
    (hf : IsAdmissible f) (y : PositiveReal) :
    (f (f y) : ℝ) + (y : ℝ) = 2 * (f y : ℝ) := by
  have hsqrt : Real.sqrt (((f y : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2) = (f y : ℝ) := by
    rw [show ((f y : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2 = (f y : ℝ) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_pos (f y).property]
  have h := hf (f y) y
  change Real.sqrt (((f y : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2) ≥
      ((f (f y) : ℝ) + (y : ℝ)) / 2 ∧
    ((f (f y) : ℝ) + (y : ℝ)) / 2 ≥
      Real.sqrt ((f y : ℝ) * (f y : ℝ)) at h
  have hsqrt₂ : Real.sqrt ((f y : ℝ) * (f y : ℝ)) = (f y : ℝ) := by
    rw [show (f y : ℝ) * (f y : ℝ) = (f y : ℝ) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_pos (f y).property]
  rw [hsqrt, hsqrt₂] at h
  linarith
theorem increment_f_invariant {f : PositiveReal → PositiveReal}
    (hf : IsAdmissible f) (x : PositiveReal) :
    increment f (f x) = increment f x := by
  have h := admissible_forced_orbit hf x
  simp only [increment]
  linarith
def positiveIterate (f : PositiveReal → PositiveReal) (x : PositiveReal) :
    ℕ → PositiveReal
  | 0 => x
  | n + 1 => f (positiveIterate f x n)
theorem positiveIterate_facts {f : PositiveReal → PositiveReal}
    (hf : IsAdmissible f) (x : PositiveReal) (n : ℕ) :
    increment f (positiveIterate f x n) = increment f x ∧
      (positiveIterate f x n : ℝ) = (x : ℝ) + n * increment f x := by
  induction n with
  | zero => simp [positiveIterate, increment]
  | succ n ih =>
      let z := positiveIterate f x n
      have hInv := increment_f_invariant hf z
      have hStep : (f z : ℝ) = (z : ℝ) + increment f z := by
        simp [increment]
      constructor
      · simpa [positiveIterate, z] using hInv.trans ih.1
      · rw [show positiveIterate f x (n + 1) = f z by rfl, hStep, ih.1, ih.2]
        push_cast
        ring
theorem admissible_increment_nonneg {f : PositiveReal → PositiveReal}
    (hf : IsAdmissible f) (x : PositiveReal) : 0 ≤ increment f x := by
  by_contra hneg
  have hq : 0 < -increment f x := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((x : ℝ) / (-increment f x))
  have hn' : (x : ℝ) < (n : ℝ) * (-increment f x) :=
    (div_lt_iff₀ hq).mp hn
  have hfacts := positiveIterate_facts hf x n
  have hpos := (positiveIterate f x n).property
  rw [hfacts.2] at hpos
  nlinarith
theorem positive_increments_eq {f : PositiveReal → PositiveReal}
    (hf : IsAdmissible f) (x y : PositiveReal)
    (hx : 0 < increment f x) (hy : 0 < increment f y) :
    increment f x = increment f y := by
  let p := increment f x
  let q := increment f y
  rcases lt_trichotomy p q with hpq | heq | hpq
  · let K := max (y : ℝ) ((p + q) ^ 2 / (4 * (q - p)))
    obtain ⟨n, hn⟩ := exists_nat_gt ((K - (x : ℝ)) / p)
    have hXbig : K < (x : ℝ) + (n : ℝ) * p := by
      have hmul : K - (x : ℝ) < (n : ℝ) * p := by
        simpa [p] using (div_lt_iff₀ hx).mp hn
      linarith
    let Xp := positiveIterate f x n
    let Yp := positiveIterate f y (Nat.floor (((Xp : ℝ) - (y : ℝ)) / q))
    let X := (Xp : ℝ)
    let Y := (Yp : ℝ)
    let m := Nat.floor ((X - (y : ℝ)) / q)
    have hXcoord : X = (x : ℝ) + (n : ℝ) * p := by
      simpa [X, p] using (positiveIterate_facts hf x n).2
    have hXgtY : (y : ℝ) < X := by
      have : (y : ℝ) ≤ K := le_max_left _ _
      rw [hXcoord]
      linarith [hXbig]
    have hquot : 0 ≤ (X - (y : ℝ)) / q := by positivity
    have hfloorlo := Nat.floor_le hquot
    have hfloorhi := Nat.lt_floor_add_one ((X - (y : ℝ)) / q)
    have hYcoord : Y = (y : ℝ) + (m : ℝ) * q := by
      have hyfacts := positiveIterate_facts hf y m
      simpa [Yp, Y, m, q] using hyfacts.2
    have hYle : Y ≤ X := by
      have hmul := (le_div_iff₀ hy).mp hfloorlo
      rw [hYcoord]
      linarith
    have hXltYq : X < Y + q := by
      have hmul := (div_lt_iff₀ hy).mp hfloorhi
      rw [hYcoord]
      nlinarith
    let r := X - Y
    have hrlo : 0 ≤ r := by dsimp [r]; linarith
    have hrhi : r < q := by dsimp [r]; linarith
    have hXfacts := positiveIterate_facts hf x n
    have hYfacts := positiveIterate_facts hf y m
    have hfx : (f Xp : ℝ) = X + p := by
      have hi : (f Xp : ℝ) - (Xp : ℝ) = (f x : ℝ) - (x : ℝ) := by
        simpa [increment] using hXfacts.1
      change (f Xp : ℝ) = (Xp : ℝ) + ((f x : ℝ) - (x : ℝ))
      nlinarith [hi]
    have hfy : (f Yp : ℝ) = Y + q := by
      have hi : (f Yp : ℝ) - (Yp : ℝ) = (f y : ℝ) - (y : ℝ) := by
        simpa [increment] using hYfacts.1
      change (f Yp : ℝ) = (Yp : ℝ) + ((f y : ℝ) - (y : ℝ))
      nlinarith [hi]
    have hsq := admissible_sq_bounds hf Xp Yp
    have hlow : 4 * X * (Y + q) ≤ (X + p + Y) ^ 2 := by
      simpa [hfx, hfy] using hsq.1
    have hL : 0 ≤ 4 * X * (p - q) + (r - p) ^ 2 := by
      have hid : (X + p + Y) ^ 2 - 4 * X * (Y + q) =
          4 * X * (p - q) + (r - p) ^ 2 := by
        dsimp [r]
        ring
      rw [← hid]
      linarith [hlow]
    have hrp₁ : 0 ≤ (p + q) - (r - p) := by linarith
    have hrp₂ : 0 ≤ (p + q) + (r - p) := by linarith
    have hrp : (r - p) ^ 2 ≤ (p + q) ^ 2 := by
      have hmul := mul_nonneg hrp₁ hrp₂
      have hid : (p + q) ^ 2 - (r - p) ^ 2 =
          ((p + q) - (r - p)) * ((p + q) + (r - p)) := by ring
      have hdiff : 0 ≤ (p + q) ^ 2 - (r - p) ^ 2 := by rw [hid]; exact hmul
      linarith
    have hratio : (p + q) ^ 2 / (4 * (q - p)) < X := by
      have hK : (p + q) ^ 2 / (4 * (q - p)) ≤ K := le_max_right _ _
      rw [hXcoord]
      linarith [hXbig]
    have hmul := (div_lt_iff₀ (by linarith : 0 < 4 * (q - p))).mp hratio
    have hbound : 4 * X * (q - p) ≤ (r - p) ^ 2 := by
      have hid : 4 * X * (q - p) = -(4 * X * (p - q)) := by ring
      rw [hid]
      linarith [hL]
    have hstrict : (p + q) ^ 2 < 4 * X * (q - p) := by
      calc
        (p + q) ^ 2 < X * (4 * (q - p)) := hmul
        _ = 4 * X * (q - p) := by ring
    have : 4 * X * (q - p) ≤ (p + q) ^ 2 := le_trans hbound hrp
    linarith
  · exact heq
  · let K := max (y : ℝ) ((3 * q ^ 2 + 2 * p * q) / (4 * (p - q)))
    obtain ⟨n, hn⟩ := exists_nat_gt ((K - (x : ℝ)) / p)
    have hXbig : K < (x : ℝ) + (n : ℝ) * p := by
      have hmul : K - (x : ℝ) < (n : ℝ) * p := by
        simpa [p] using (div_lt_iff₀ hx).mp hn
      linarith
    let Xp := positiveIterate f x n
    let Yp := positiveIterate f y (Nat.floor (((Xp : ℝ) - (y : ℝ)) / q))
    let X := (Xp : ℝ)
    let Y := (Yp : ℝ)
    let m := Nat.floor ((X - (y : ℝ)) / q)
    have hXcoord : X = (x : ℝ) + (n : ℝ) * p := by
      simpa [X, p] using (positiveIterate_facts hf x n).2
    have hXgtY : (y : ℝ) < X := by
      have : (y : ℝ) ≤ K := le_max_left _ _
      rw [hXcoord]
      linarith [hXbig]
    have hquot : 0 ≤ (X - (y : ℝ)) / q := by positivity
    have hfloorlo := Nat.floor_le hquot
    have hfloorhi := Nat.lt_floor_add_one ((X - (y : ℝ)) / q)
    have hYcoord : Y = (y : ℝ) + (m : ℝ) * q := by
      have hyfacts := positiveIterate_facts hf y m
      simpa [Yp, Y, m, q] using hyfacts.2
    have hYle : Y ≤ X := by
      have hmul := (le_div_iff₀ hy).mp hfloorlo
      rw [hYcoord]
      linarith
    have hXltYq : X < Y + q := by
      have hmul := (div_lt_iff₀ hy).mp hfloorhi
      rw [hYcoord]
      nlinarith
    let r := X - Y
    have hrlo : 0 ≤ r := by dsimp [r]; linarith
    have hrhi : r < q := by dsimp [r]; linarith
    have hXfacts := positiveIterate_facts hf x n
    have hYfacts := positiveIterate_facts hf y m
    have hfx : (f Xp : ℝ) = X + p := by
      have hi : (f Xp : ℝ) - (Xp : ℝ) = (f x : ℝ) - (x : ℝ) := by
        simpa [increment] using hXfacts.1
      change (f Xp : ℝ) = (Xp : ℝ) + ((f x : ℝ) - (x : ℝ))
      nlinarith [hi]
    have hfy : (f Yp : ℝ) = Y + q := by
      have hi : (f Yp : ℝ) - (Yp : ℝ) = (f y : ℝ) - (y : ℝ) := by
        simpa [increment] using hYfacts.1
      change (f Yp : ℝ) = (Yp : ℝ) + ((f y : ℝ) - (y : ℝ))
      nlinarith [hi]
    have hsq := admissible_sq_bounds hf Xp Yp
    have hupp : (X + p + Y) ^ 2 ≤ 2 * X ^ 2 + 2 * (Y + q) ^ 2 := by
      simpa [hfx, hfy] using hsq.2
    have hU : 0 ≤ 4 * X * (q - p) +
        (r ^ 2 - 4 * q * r + 2 * q ^ 2 + 2 * p * r - p ^ 2) := by
      have hid : 2 * X ^ 2 + 2 * (Y + q) ^ 2 - (X + p + Y) ^ 2 =
          4 * X * (q - p) +
            (r ^ 2 - 4 * q * r + 2 * q ^ 2 + 2 * p * r - p ^ 2) := by
        dsimp [r]
        ring
      rw [← hid]
      linarith [hupp]
    have hqrsq : r ^ 2 ≤ q ^ 2 := by
      have hqpos : 0 < q := by simpa [q] using hy
      have hmul := mul_nonneg (sub_nonneg.mpr (le_of_lt hrhi))
        (add_nonneg (le_of_lt hqpos) hrlo)
      have hid : q ^ 2 - r ^ 2 = (q - r) * (q + r) := by ring
      have hdiff : 0 ≤ q ^ 2 - r ^ 2 := by rw [hid]; exact hmul
      linarith
    have hpr : p * r ≤ p * q := by
      calc
        p * r ≤ p * r + p * (q - r) := le_add_of_nonneg_right
          (mul_nonneg (le_of_lt hx) (sub_nonneg.mpr (le_of_lt hrhi)))
        _ = p * q := by ring
    have hR : r ^ 2 - 4 * q * r + 2 * q ^ 2 + 2 * p * r - p ^ 2 ≤
        3 * q ^ 2 + 2 * p * q := by
      have hqpos : 0 < q := by simpa [q] using hy
      have hqr : 0 ≤ q * r := mul_nonneg (le_of_lt hqpos) hrlo
      have hp2 : 0 ≤ p ^ 2 := sq_nonneg p
      have hp_pos : 0 < p := by simpa [p] using hx
      have hpr' : 0 ≤ p * (q - r) :=
        mul_nonneg (le_of_lt hp_pos) (sub_nonneg.mpr (le_of_lt hrhi))
      have hid : (3 * q ^ 2 + 2 * p * q) -
          (r ^ 2 - 4 * q * r + 2 * q ^ 2 + 2 * p * r - p ^ 2) =
          (q ^ 2 - r ^ 2) + 4 * q * r + 2 * p * (q - r) + p ^ 2 := by ring
      have hdiff : 0 ≤ (3 * q ^ 2 + 2 * p * q) -
          (r ^ 2 - 4 * q * r + 2 * q ^ 2 + 2 * p * r - p ^ 2) := by
        rw [hid]
        linarith [hqrsq, hqr, hpr', hp2]
      linarith
    have hratio : (3 * q ^ 2 + 2 * p * q) / (4 * (p - q)) < X := by
      have hK : (3 * q ^ 2 + 2 * p * q) / (4 * (p - q)) ≤ K := le_max_right _ _
      rw [hXcoord]
      linarith [hXbig]
    have hmul := (div_lt_iff₀ (by linarith : 0 < 4 * (p - q))).mp hratio
    have hbound : 4 * X * (p - q) ≤
        r ^ 2 - 4 * q * r + 2 * q ^ 2 + 2 * p * r - p ^ 2 := by
      have hid : 4 * X * (p - q) = -(4 * X * (q - p)) := by ring
      rw [hid]
      linarith [hU]
    have hstrict : 3 * q ^ 2 + 2 * p * q < 4 * X * (p - q) := by
      calc
        3 * q ^ 2 + 2 * p * q < X * (4 * (p - q)) := hmul
        _ = 4 * X * (p - q) := by ring
    have : 4 * X * (p - q) ≤ 3 * q ^ 2 + 2 * p * q := le_trans hbound hR
    linarith
theorem fixed_inputs_downward_closed {f : PositiveReal → PositiveReal}
    (hf : IsAdmissible f) (a t : PositiveReal)
    (ha : increment f a = 0) (ht : 0 < (t : ℝ)) (hta : (t : ℝ) < (a : ℝ)) :
    increment f t = 0 := by
  have htnonneg := admissible_increment_nonneg hf t
  by_contra htnz
  have hq : 0 < increment f t := lt_of_le_of_ne htnonneg (Ne.symm htnz)
  let q := increment f t
  have hqpos : 0 < q := by simpa [q] using hq
  have hfix : (f a : ℝ) = (a : ℝ) := by
    dsimp [increment] at ha
    linarith
  have hstep : (f t : ℝ) = (t : ℝ) + q := by
    dsimp [q, increment]
    ring
  have hlow := (admissible_sq_bounds hf a t).1
  rw [hfix, hstep] at hlow
  have hsep : 4 * (a : ℝ) * q ≤ ((a : ℝ) - (t : ℝ)) ^ 2 := by nlinarith [hlow]
  have hdiff : 0 < (a : ℝ) ^ 2 - ((a : ℝ) - (t : ℝ)) ^ 2 := by
    have hprod : 0 < (t : ℝ) * (2 * (a : ℝ) - (t : ℝ)) :=
      mul_pos ht (by linarith)
    nlinarith [hprod]
  have hqsmall : q < (a : ℝ) / 4 := by nlinarith [hsep, hdiff]
  let m := Nat.floor (((a : ℝ) - (t : ℝ)) / q)
  let uSub := positiveIterate f t m
  let u := (uSub : ℝ)
  have hquot : 0 ≤ ((a : ℝ) - (t : ℝ)) / q := by positivity
  have hfloorlo := Nat.floor_le hquot
  have hfloorhi := Nat.lt_floor_add_one (((a : ℝ) - (t : ℝ)) / q)
  have hmul₁ : (m : ℝ) * q ≤ (a : ℝ) - (t : ℝ) :=
    (le_div_iff₀ hqpos).mp hfloorlo
  have hmul₂ : (a : ℝ) - (t : ℝ) < ((m : ℝ) + 1) * q :=
    (div_lt_iff₀ hqpos).mp hfloorhi
  have hufacts := positiveIterate_facts hf t m
  have hucoord : u = (t : ℝ) + (m : ℝ) * q := by
    simpa [u, uSub, m, q] using hufacts.2
  have hu_le : u ≤ (a : ℝ) := by rw [hucoord]; linarith
  have hau_lt : (a : ℝ) < u + q := by
    rw [hucoord]
    nlinarith [hmul₂]
  have huf : (f uSub : ℝ) = u + q := by
    have hi : (f uSub : ℝ) - (uSub : ℝ) = (f t : ℝ) - (t : ℝ) := by
      simpa [increment] using hufacts.1
    change (f uSub : ℝ) = (uSub : ℝ) + ((f t : ℝ) - (t : ℝ))
    rw [hstep]
    nlinarith [hi]
  have hlow₂ := (admissible_sq_bounds hf a uSub).1
  rw [hfix, huf] at hlow₂
  have hsep₂ : 4 * (a : ℝ) * q ≤ ((a : ℝ) - u) ^ 2 := by nlinarith [hlow₂]
  have hrem : ((a : ℝ) - u) ^ 2 < q ^ 2 := by
    have hleft : 0 < q - ((a : ℝ) - u) := by linarith [hau_lt]
    have hright : 0 < q + ((a : ℝ) - u) := by positivity
    have hprod : 0 < (q - ((a : ℝ) - u)) * (q + ((a : ℝ) - u)) :=
      mul_pos hleft hright
    nlinarith [hprod]
  have hqsmall' : q < 4 * (a : ℝ) := by linarith [hqsmall]
  have hsqsmall : q ^ 2 < 4 * (a : ℝ) * q := by
    have := mul_lt_mul_of_pos_right hqsmall' hqpos
    nlinarith [this]
  linarith
theorem fixed_excludes_positive_increment {f : PositiveReal → PositiveReal}
    (hf : IsAdmissible f) (a y : PositiveReal)
    (ha : increment f a = 0) (hy : 0 < increment f y) : False := by
  let S : Set ℝ := {r | ∃ x : PositiveReal, (x : ℝ) = r ∧ increment f x = 0}
  have hSne : S.Nonempty := by
    refine ⟨(a : ℝ), ?_⟩
    change ∃ x : PositiveReal, (x : ℝ) = (a : ℝ) ∧ increment f x = 0
    exact ⟨a, rfl, ha⟩
  have hSbound : ∀ r ∈ S, r ≤ (y : ℝ) := by
    intro r hr
    rcases hr with ⟨x, hxr, hxfix⟩
    by_contra hnot
    have hyx : (y : ℝ) < (x : ℝ) := by rw [hxr]; exact lt_of_not_ge hnot
    have hyfix := fixed_inputs_downward_closed hf x y hxfix y.property hyx
    exact (ne_of_gt hy) hyfix
  have hBdd : BddAbove S := ⟨(y : ℝ), hSbound⟩
  let α := sSup S
  have ha_mem : (a : ℝ) ∈ S := by
    change ∃ x : PositiveReal, (x : ℝ) = (a : ℝ) ∧ increment f x = 0
    exact ⟨a, rfl, ha⟩
  have ha_le : (a : ℝ) ≤ α := le_csSup hBdd ha_mem
  have hαpos : 0 < α := lt_of_lt_of_le a.property ha_le
  have hc : 0 < increment f y := hy
  let c := increment f y
  let η := min 1 (min (α / 4) (α * c / 8))
  have hηpos : 0 < η := by
    dsimp [η]
    positivity
  have hη1 : η ≤ 1 := by dsimp [η]; exact le_trans (min_le_left _ _) le_rfl
  have hη2 : η ≤ α / 4 := by
    dsimp [η]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hη3 : η ≤ α * c / 8 := by
    dsimp [η]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hsmall : α - η < α := by linarith
  obtain ⟨r, hrmem, hrgt⟩ := exists_lt_of_lt_csSup hSne hsmall
  have hrmem' : r ∈ S := hrmem
  rcases hrmem with ⟨t, htr, htfix⟩
  have htgt : α - η < (t : ℝ) := by rw [htr]; exact hrgt
  have ht_le : (t : ℝ) ≤ α := by
    change (t : ℝ) ≤ sSup S
    rw [htr]
    exact le_csSup hBdd hrmem'
  let z : PositiveReal := ⟨α + η, by linarith [hαpos, hηpos]⟩
  have hzc : (z : ℝ) = α + η := rfl
  have hzpos : 0 < increment f z := by
    have hnz : increment f z ≠ 0 := by
      intro hz
      have hzmem : (z : ℝ) ∈ S := by
        change ∃ x : PositiveReal, (x : ℝ) = (z : ℝ) ∧ increment f x = 0
        exact ⟨z, rfl, hz⟩
      have hzle := le_csSup hBdd hzmem
      rw [hzc] at hzle
      linarith [hηpos]
    have hnonneg := admissible_increment_nonneg hf z
    exact lt_of_le_of_ne hnonneg (Ne.symm hnz)
  have hcommon := positive_increments_eq hf y z hy hzpos
  have hzinc : increment f z = c := by dsimp [c]; exact hcommon.symm
  have hfix_t : (f t : ℝ) = (t : ℝ) := by
    dsimp [increment] at htfix
    linarith
  have hstep_z : (f z : ℝ) = (z : ℝ) + c := by
    dsimp [increment] at hzinc
    dsimp [c] at hzinc
    linarith
  have hlow := (admissible_sq_bounds hf t z).1
  rw [hfix_t, hstep_z] at hlow
  have hsep : 4 * (t : ℝ) * c ≤ ((z : ℝ) - (t : ℝ)) ^ 2 := by
    rw [hzc]
    nlinarith [hlow]
  have hdistpos : 0 < (z : ℝ) - (t : ℝ) := by rw [hzc]; linarith
  have hdistlt : (z : ℝ) - (t : ℝ) < 2 * η := by rw [hzc]; linarith
  have hsqdist : ((z : ℝ) - (t : ℝ)) ^ 2 < 4 * η ^ 2 := by
    have hprod : 0 < (2 * η - ((z : ℝ) - (t : ℝ))) *
        (2 * η + ((z : ℝ) - (t : ℝ))) :=
      mul_pos (by linarith [hdistlt]) (by linarith [hηpos, hdistpos])
    nlinarith [hprod]
  have hηsq : η ^ 2 ≤ η := by
    have hprod := mul_nonneg (le_of_lt hηpos) (sub_nonneg.mpr hη1)
    nlinarith [hprod]
  have hsqsmall : 4 * η ^ 2 ≤ α * c / 2 := by nlinarith [hηsq, hη3]
  have htlarge : α / 2 < (t : ℝ) := by linarith [htgt, hη2]
  have hrhs : α * c / 2 < 4 * (t : ℝ) * c := by
    have hprod : 0 < (2 * (t : ℝ) - α) * c :=
      mul_pos (by linarith [htlarge]) hy
    nlinarith [hprod]
  linarith
theorem admissible_increment_classification {f : PositiveReal → PositiveReal}
    (hf : IsAdmissible f) :
    (∀ x : PositiveReal, increment f x = 0) ∨
      ∃ c : ℝ, 0 < c ∧ ∀ x : PositiveReal, increment f x = c := by
  by_cases hfixed : ∃ a : PositiveReal, increment f a = 0
  · obtain ⟨a, ha⟩ := hfixed
    left
    intro x
    have hnonneg := admissible_increment_nonneg hf x
    by_contra hx
    have hxpos : 0 < increment f x := lt_of_le_of_ne hnonneg (Ne.symm hx)
    exact fixed_excludes_positive_increment hf a x ha hxpos
  · right
    let x₀ : PositiveReal := ⟨1, by norm_num⟩
    have hnonneg := admissible_increment_nonneg hf x₀
    have hne : increment f x₀ ≠ 0 := by
      intro hzero
      exact hfixed ⟨x₀, hzero⟩
    have hc : 0 < increment f x₀ := lt_of_le_of_ne hnonneg (Ne.symm hne)
    refine ⟨increment f x₀, hc, ?_⟩
    intro x
    have hnonnegx := admissible_increment_nonneg hf x
    have hne_x : increment f x ≠ 0 := by
      intro hzero
      exact hfixed ⟨x, hzero⟩
    have hxpos : 0 < increment f x := lt_of_le_of_ne hnonnegx (Ne.symm hne_x)
    exact (positive_increments_eq hf x₀ x hc hxpos).symm
theorem arithmetic_mean_le_rms (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) / 2 ≤ Real.sqrt ((a ^ 2 + b ^ 2) / 2) := by
  have hrad : 0 ≤ (a ^ 2 + b ^ 2) / 2 := by positivity
  have hmean : 0 ≤ (a + b) / 2 := by positivity
  have hsquare : ((a + b) / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 2 := by
    nlinarith [sq_nonneg (a - b)]
  by_contra hnot
  have hgt : Real.sqrt ((a ^ 2 + b ^ 2) / 2) < (a + b) / 2 := lt_of_not_ge hnot
  have hmeanpos : 0 < (a + b) / 2 := by
    have hsqrtpos : 0 ≤ Real.sqrt ((a ^ 2 + b ^ 2) / 2) := Real.sqrt_nonneg _
    linarith
  have hprod : 0 < ((a + b) / 2 - Real.sqrt ((a ^ 2 + b ^ 2) / 2)) *
      ((a + b) / 2 + Real.sqrt ((a ^ 2 + b ^ 2) / 2)) :=
    mul_pos (by linarith) (by linarith [Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2)])
  nlinarith [Real.sq_sqrt hrad, hprod]
theorem geometric_mean_le_arithmetic_mean (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  have hrad : 0 ≤ a * b := mul_nonneg ha hb
  have hmean : 0 ≤ (a + b) / 2 := by positivity
  have hsquare : a * b ≤ ((a + b) / 2) ^ 2 := by
    nlinarith [sq_nonneg (a - b)]
  by_contra hnot
  have hgt : (a + b) / 2 < Real.sqrt (a * b) := lt_of_not_ge hnot
  have hsqrtpos : 0 < Real.sqrt (a * b) := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg _
    linarith
  have hprod : 0 < (Real.sqrt (a * b) - (a + b) / 2) *
      (Real.sqrt (a * b) + (a + b) / 2) :=
    mul_pos (by linarith) (by linarith [hmean])
  nlinarith [Real.sq_sqrt hrad, hprod]
theorem main_theorem (f : PositiveReal → PositiveReal) :
    IsAdmissible f ↔
      ∃ c : ℝ, 0 ≤ c ∧ ∀ x : PositiveReal, (f x : ℝ) = (x : ℝ) + c := by
  constructor
  · intro hf
    rcases admissible_increment_classification hf with hzero | ⟨c, hc, hconst⟩
    · refine ⟨0, le_rfl, ?_⟩
      intro x
      have hx := hzero x
      dsimp [increment] at hx
      linarith
    · refine ⟨c, le_of_lt hc, ?_⟩
      intro x
      have hx := hconst x
      dsimp [increment] at hx
      linarith
  · rintro ⟨c, hc, hfc⟩
    intro x y
    change Real.sqrt (((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2) ≥
        ((f x : ℝ) + (y : ℝ)) / 2 ∧
      ((f x : ℝ) + (y : ℝ)) / 2 ≥
        Real.sqrt ((x : ℝ) * (f y : ℝ))
    rw [hfc x, hfc y]
    constructor
    · have hyc : 0 ≤ (y : ℝ) + c := add_nonneg (le_of_lt y.property) hc
      have h := arithmetic_mean_le_rms (x : ℝ) ((y : ℝ) + c)
        (le_of_lt x.property) hyc
      simpa [add_assoc, add_left_comm, add_comm] using h
    · have hyc : 0 ≤ (y : ℝ) + c := add_nonneg (le_of_lt y.property) hc
      have h := geometric_mean_le_arithmetic_mean (x : ℝ) ((y : ℝ) + c)
        (le_of_lt x.property) hyc
      simpa [add_assoc, add_left_comm, add_comm] using h
