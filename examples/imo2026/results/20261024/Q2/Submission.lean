import Mathlib
set_option backward.isDefEq.respectTransparency false

open EuclideanGeometry

-- We work in the Euclidean plane `ℝ²` with the standard `L²` (Euclidean) norm.
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A point `P` lies in the open interior of the triangle `X Y Z`: it is a
strictly convex combination `P = α • X + β • Y + γ • Z` with `α, β, γ > 0` and
`α + β + γ = 1`. -/
def InsideTriangle (X Y Z P : Plane) : Prop :=
  ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧
    P = α • X + β • Y + γ • Z

/-- A point `P` lies inside the (proper) angle at vertex `Y` spanned by the rays
`Y X` and `Y Z`: writing `P - Y = s • (X - Y) + t • (Z - Y)`, one has `s > 0`
and `t > 0`. -/
def InsideAngle (X Y Z P : Plane) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ P - Y = s • (X - Y) + t • (Z - Y)

/-- `O` is the circumcentre of triangle `A K L`: it is equidistant from the three
vertices. (For a nondegenerate triangle such a point exists and is unique.) -/
def IsCircumcentre (A K L O : Plane) : Prop :=
  dist O A = dist O K ∧ dist O A = dist O L

theorem signed_det_inner_eq_of_angle_eq
    (p q r s : Plane)
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0)
    (hang : InnerProductGeometry.angle p q = InnerProductGeometry.angle r s)
    (hdet : 0 < (p 0 * q 1 - p 1 * q 0) * (r 0 * s 1 - r 1 * s 0)) :
    (p 0 * q 1 - p 1 * q 0) * inner ℝ r s =
      (r 0 * s 1 - r 1 * s 0) * inner ℝ p q := by
  let dp : ℝ := p 0 * q 1 - p 1 * q 0
  let dr : ℝ := r 0 * s 1 - r 1 * s 0
  have hpgram :
      inner ℝ p p * inner ℝ q q - inner ℝ p q * inner ℝ p q = dp * dp := by
    dsimp [dp]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      dotProduct, Fin.sum_univ_two]
    ring
  have hrgram :
      inner ℝ r r * inner ℝ s s - inner ℝ r s * inner ℝ r s = dr * dr := by
    dsimp [dr]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      dotProduct, Fin.sum_univ_two]
    ring
  have hsinp := InnerProductGeometry.sin_angle_mul_norm_mul_norm p q
  have hsinr := InnerProductGeometry.sin_angle_mul_norm_mul_norm r s
  have hcosp := InnerProductGeometry.cos_angle_mul_norm_mul_norm p q
  have hcosr := InnerProductGeometry.cos_angle_mul_norm_mul_norm r s
  rw [hpgram, Real.sqrt_mul_self_eq_abs] at hsinp
  rw [hrgram, Real.sqrt_mul_self_eq_abs] at hsinr
  rw [hang] at hsinp hcosp
  have habs : |dp| * inner ℝ r s = |dr| * inner ℝ p q := by
    rw [← hcosr, ← hcosp, ← hsinp, ← hsinr]
    ring
  have hdet' : 0 < dp * dr := by simpa [dp, dr] using hdet
  rcases (mul_pos_iff.mp hdet') with hpos | hneg
  · simpa [abs_of_pos hpos.1, abs_of_pos hpos.2] using habs
  · have h := habs
    rw [abs_of_neg hneg.1, abs_of_neg hneg.2] at h
    dsimp [dp, dr] at h ⊢
    linarith
theorem det2_ne_zero_of_not_collinear (A B C : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    (B - A) 0 * (C - A) 1 - (B - A) 1 * (C - A) 0 ≠ 0 := by
  have hAB : A ≠ B := ne₁₂_of_not_collinear hABC
  have hb : B - A ≠ 0 := sub_ne_zero.mpr hAB.symm
  intro hdet
  apply hABC
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨A, B - A, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · by_cases hb0 : (B - A) 0 = 0
    · have hb1 : (B - A) 1 ≠ 0 := by
        intro hb1
        apply hb
        ext i
        fin_cases i <;> simp_all
      change B 0 - A 0 = 0 at hb0
      change B 1 - A 1 ≠ 0 at hb1
      change (B 0 - A 0) * (p 1 - A 1) -
        (B 1 - A 1) * (p 0 - A 0) = 0 at hdet
      refine ⟨(p - A) 1 / (B - A) 1, ?_⟩
      ext i
      fin_cases i
      · have hp0 : (p - A) 0 = 0 := by
          have hz : (B 1 - A 1) * (p 0 - A 0) = 0 := by
            simpa only [hb0, zero_mul, zero_sub, neg_eq_zero] using hdet
          exact (mul_eq_zero.mp hz).resolve_left hb1
        change p 0 = ((p 1 - A 1) / (B 1 - A 1)) * (B 0 - A 0) + A 0
        rw [hb0, mul_zero, zero_add]
        change p 0 - A 0 = 0 at hp0
        linarith
      · change p 1 = ((p 1 - A 1) / (B 1 - A 1)) * (B 1 - A 1) + A 1
        field_simp [hb1]
        ring
    · refine ⟨(p - A) 0 / (B - A) 0, ?_⟩
      change B 0 - A 0 ≠ 0 at hb0
      change (B 0 - A 0) * (p 1 - A 1) -
        (B 1 - A 1) * (p 0 - A 0) = 0 at hdet
      ext i
      fin_cases i
      · change p 0 = ((p 0 - A 0) / (B 0 - A 0)) * (B 0 - A 0) + A 0
        field_simp [hb0]
        ring
      · change p 1 = ((p 0 - A 0) / (B 0 - A 0)) * (B 1 - A 1) + A 1
        field_simp [hb0]
        nlinarith
theorem smul_add_smul_coeff_eq
    (b c : Plane) (D x y u v : ℝ)
    (hD : D = b 0 * c 1 - b 1 * c 0) (hDn : D ≠ 0)
    (h : x • b + y • c = u • b + v • c) : x = u ∧ y = v := by
  have h0 := congrArg (fun z : Plane => z 0) h
  have h1 := congrArg (fun z : Plane => z 1) h
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h0 h1
  have hxD : (x - u) * D = 0 := by
    rw [hD]
    linear_combination c 1 * h0 - c 0 * h1
  have hyD : (y - v) * D = 0 := by
    rw [hD]
    linear_combination b 0 * h1 - b 1 * h0
  constructor
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hxD).resolve_right hDn)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hyD).resolve_right hDn)
theorem proper_angle_factors_pos
    (A B C K L : Plane) (x y u v s t p q D : ℝ)
    (hD : D = (B - A) 0 * (C - A) 1 - (B - A) 1 * (C - A) 0)
    (hDn : D ≠ 0)
    (hK : K - A = x • (B - A) + y • (C - A))
    (hL : L - A = u • (B - A) + v • (C - A))
    (ht : 0 < t) (hp : 0 < p) (hx : 0 < x) (hv : 0 < v)
    (hKangle : K - B = s • (L - B) + t • (A - B))
    (hLangle : L - C = p • (A - C) + q • (K - C)) :
    0 < v * (1 - x) - y * (1 - u) ∧
      0 < x * (1 - v) - u * (1 - y) := by
  have hvec1 :
      (x - 1) • (B - A) + y • (C - A) =
        (s * (u - 1) - t) • (B - A) + (s * v) • (C - A) := by
    calc
      (x - 1) • (B - A) + y • (C - A) =
          (K - A) - (B - A) := by rw [hK]; module
      _ = K - B := by module
      _ = s • (L - B) + t • (A - B) := hKangle
      _ = s • ((L - A) - (B - A)) + t • (-(B - A)) := by module
      _ = (s * (u - 1) - t) • (B - A) +
          (s * v) • (C - A) := by rw [hL]; module
  have hc1 := smul_add_smul_coeff_eq (B - A) (C - A) D
    (x - 1) y (s * (u - 1) - t) (s * v) hD hDn hvec1
  have hvec2 :
      u • (B - A) + (v - 1) • (C - A) =
        (q * x) • (B - A) + (q * (y - 1) - p) • (C - A) := by
    calc
      u • (B - A) + (v - 1) • (C - A) =
          (L - A) - (C - A) := by rw [hL]; module
      _ = L - C := by module
      _ = p • (A - C) + q • (K - C) := hLangle
      _ = p • (-(C - A)) + q • ((K - A) - (C - A)) := by module
      _ = (q * x) • (B - A) +
          (q * (y - 1) - p) • (C - A) := by rw [hK]; module
  have hc2 := smul_add_smul_coeff_eq (B - A) (C - A) D
    u (v - 1) (q * x) (q * (y - 1) - p) hD hDn hvec2
  rcases hc1 with ⟨hc1x, hc1y⟩
  rcases hc2 with ⟨hc2u, hc2v⟩
  constructor
  · have hd : v * (1 - x) - y * (1 - u) = v * t := by
      rw [hc1y]
      linear_combination -v * hc1x
    rw [hd]
    exact mul_pos hv ht
  · have he : x * (1 - v) - u * (1 - y) = x * p := by
      rw [hc2u]
      linear_combination -x * hc2v
    rw [he]
    exact mul_pos hx hp
theorem coordinate_det_pos
    (x y u v : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hu : 0 < u) (hv : 0 < v)
    (hxy : x + y < 1) (hv1 : v < 1)
    (hd : 0 < v * (1 - x) - y * (1 - u))
    (he : 0 < x * (1 - v) - u * (1 - y)) :
    0 < x * v - y * u := by
  by_contra hΔpos
  have hΔ : x * v - y * u ≤ 0 := le_of_not_gt hΔpos
  have hxu : x < u := by
    by_contra hxu'
    have hux : u ≤ x := le_of_not_gt hxu'
    have hvy : v ≤ y := by
      have hp : 0 ≤ (x - u) * y :=
        mul_nonneg (sub_nonneg.mpr hux) (le_of_lt hy)
      nlinarith
    have hx1 : x < 1 := by nlinarith
    have hp : 0 ≤ (y - v) * (1 - x) :=
      mul_nonneg (sub_nonneg.mpr hvy) (by nlinarith)
    have hq : 0 ≤ y * (x - u) :=
      mul_nonneg (le_of_lt hy) (sub_nonneg.mpr hux)
    nlinarith
  have hvy : v < y := by
    by_contra hvy'
    have hyv : y ≤ v := le_of_not_gt hvy'
    have hxu' : x ≤ u := by
      have hp : 0 ≤ (v - y) * u :=
        mul_nonneg (sub_nonneg.mpr hyv) (le_of_lt hu)
      nlinarith
    have hp : 0 ≤ (u - x) * (1 - v) :=
      mul_nonneg (sub_nonneg.mpr hxu') (by nlinarith)
    have hq : 0 ≤ u * (v - y) :=
      mul_nonneg (le_of_lt hu) (sub_nonneg.mpr hyv)
    nlinarith
  have hx1 : x < 1 := by nlinarith
  have hy1 : y < 1 := by nlinarith
  have ha : 0 < u - x := sub_pos.mpr hxu
  have hz : 0 < y - v := sub_pos.mpr hvy
  have hA : (1 - x) * (y - v) < y * (u - x) := by nlinarith
  have hB : (1 - y) * (u - x) < x * (y - v) := by nlinarith
  have hA' := mul_lt_mul_of_pos_right hA (mul_pos (sub_pos.mpr hy1) ha)
  have hB' := mul_lt_mul_of_pos_left hB (mul_pos hy ha)
  have hmul :
      (1 - x) * (1 - y) * ((u - x) * (y - v))
        < x * y * ((u - x) * (y - v)) := by
    calc
      (1-x)*(1-y)*((u-x)*(y-v))
          = ((1-x)*(y-v))*((1-y)*(u-x)) := by ring
      _ < (y*(u-x))*((1-y)*(u-x)) := hA'
      _ < (y*(u-x))*(x*(y-v)) := hB'
      _ = x*y*((u-x)*(y-v)) := by ring
  have haz : 0 < (u - x) * (y - v) := mul_pos ha hz
  nlinarith
theorem coordinate_scalar_elimination
    (x y u v P Q R : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hy : 0 < y)
    (hx1 : x < 1) (hv1 : v < 1) (hP : 0 < P)
    (h1 : P * u * x - P * u - Q * v * y + Q * y = 0)
    (h2 :
      -(2 * P * u^2 * x - 2 * P * u^2 - 2 * P * u * x + 2 * P * u
        + Q * u * y + 2 * Q * v^2 * x - 2 * Q * v^2 - Q * v * x
        + 2 * Q * v * y + Q * v - Q * y + 4 * R * u * v * x
        - 4 * R * u * v) / 2 = 0)
    (h3 :
      -(2 * P * u * x + P * u * y - P * u + 2 * P * v * x^2
        - P * v * x - 2 * P * x^2 + P * x + 2 * Q * v * y^2
        - 2 * Q * v * y - 2 * Q * y^2 + 2 * Q * y
        + 4 * R * v * x * y - 4 * R * x * y) / 2 = 0) :
    2 * ((u + v) * (P * x^2 + 2 * R * x * y + Q * y^2)
      - (x + y) * (P * u^2 + 2 * R * u * v + Q * v^2))
      - (x * v - y * u) * (P - Q) = 0 := by
  let F := u*v*y - u*v - u*x*y - v^2*x + v*x^2 + x*y
  have hdet : (P * u * y * (v - 1) * (x - 1)) * F = 0 := by
    dsimp [F]
    linear_combination
      (y * (v - 1) *
        (-2*u*v*x*y + 2*u*v*x + 2*u*v*y - 2*u*v + u*x*y
          + 2*v^2*x^2 - 2*v^2*x - v*x^2 + 2*v*x*y + v*x - x*y)) * h1
      + (-2*x*y^2*(v-1)^2) * h2
      + (2*u*v*y*(v-1)*(x-1)) * h3
  have hcoeff : P * u * y * (v - 1) * (x - 1) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · exact mul_ne_zero (ne_of_gt hP) (ne_of_gt hu)
        · exact ne_of_gt hy
      · nlinarith
    · nlinarith
  have hF : F = 0 := (mul_eq_zero.mp hdet).resolve_left hcoeff
  let T :=
    2 * ((u + v) * (P * x^2 + 2 * R * x * y + Q * y^2)
      - (x + y) * (P * u^2 + 2 * R * u * v + Q * v^2))
      - (x * v - y * u) * (P - Q)
  let S := -u*v*x - u*v*y + u*x*y + v*x*y
  let W :=
    2*u^2*x*y - 2*u*v*x^2 + 2*u*v*x*y + 2*u*v*x + u*v*y
      - 2*u*x*y - 2*v^2*x^2 + v^2*x - 2*v*x*y
  have hcombo :
      u*v*(1-x)*T = W *
          (P * u * x - P * u - Q * v * y + Q * y)
        + 2*S *
          (-(2 * P * u^2 * x - 2 * P * u^2 - 2 * P * u * x + 2 * P * u
            + Q * u * y + 2 * Q * v^2 * x - 2 * Q * v^2 - Q * v * x
            + 2 * Q * v * y + Q * v - Q * y + 4 * R * u * v * x
            - 4 * R * u * v) / 2)
        + Q*y*(u+v)*F := by
    dsimp [T, W, S, F]
    ring
  have hzero : u*v*(1-x)*T = 0 := by rw [hcombo, h1, h2, hF]; ring
  have huvx : u*v*(1-x) ≠ 0 := by positivity
  have : T = 0 := (mul_eq_zero.mp hzero).resolve_left huvx
  exact this
def gramDot (P Q R a b c d : ℝ) : ℝ :=
  P * a * c + R * (a * d + b * c) + Q * b * d
theorem angle_bridge_outputs_normalize
    (x y u v P Q R : ℝ)
    (h1raw :
      y * gramDot P Q R 0 (-1) u (v - 1) =
        u * gramDot P Q R (x - 1) y (-1) 0)
    (h2raw :
      (v * (1 - x) - y * (1 - u)) *
          gramDot P Q R u (v - 1 / 2) 0 (1 / 2) =
        (u / 2) * gramDot P Q R (u - 1) v (x - 1) y)
    (h3raw :
      (x * (1 - v) - u * (1 - y)) *
          gramDot P Q R (1 / 2) 0 (x - 1 / 2) y =
        (y / 2) * gramDot P Q R u (v - 1) x (y - 1)) :
    (P * u * x - P * u - Q * v * y + Q * y = 0) ∧
    (-(2 * P * u^2 * x - 2 * P * u^2 - 2 * P * u * x + 2 * P * u
        + Q * u * y + 2 * Q * v^2 * x - 2 * Q * v^2 - Q * v * x
        + 2 * Q * v * y + Q * v - Q * y + 4 * R * u * v * x
        - 4 * R * u * v) / 2 = 0) ∧
    (-(2 * P * u * x + P * u * y - P * u + 2 * P * v * x^2
        - P * v * x - 2 * P * x^2 + P * x + 2 * Q * v * y^2
        - 2 * Q * v * y - 2 * Q * y^2 + 2 * Q * y
        + 4 * R * v * x * y - 4 * R * x * y) / 2 = 0) := by
  constructor
  · dsimp [gramDot] at h1raw
    nlinarith [h1raw]
  constructor
  · dsimp [gramDot] at h2raw
    nlinarith [h2raw]
  · dsimp [gramDot] at h3raw
    nlinarith [h3raw]
theorem det2_smul_add_smul
    (b c : Plane) (a d e f : ℝ) :
    (a • b + d • c) 0 * (e • b + f • c) 1 -
        (a • b + d • c) 1 * (e • b + f • c) 0 =
      (a * f - d * e) * (b 0 * c 1 - b 1 * c 0) := by
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring
theorem inner_smul_add_smul_eq_gramDot
    (b c : Plane) (a d e f : ℝ) :
    inner ℝ (a • b + d • c) (e • b + f • c) =
      gramDot (inner ℝ b b) (inner ℝ c c) (inner ℝ b c) a d e f := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm c b]
  dsimp [gramDot]
  ring
theorem signed_coeff_inner_eq_of_angle_eq
    (b c : Plane) (D a d e f g h i j : ℝ)
    (hD : D = b 0 * c 1 - b 1 * c 0) (hDn : D ≠ 0)
    (hang :
      InnerProductGeometry.angle (a • b + d • c) (e • b + f • c) =
        InnerProductGeometry.angle (g • b + h • c) (i • b + j • c))
    (hpos : 0 < (a * f - d * e) * (g * j - h * i)) :
    (a * f - d * e) *
        gramDot (inner ℝ b b) (inner ℝ c c) (inner ℝ b c) g h i j =
      (g * j - h * i) *
        gramDot (inner ℝ b b) (inner ℝ c c) (inner ℝ b c) a d e f := by
  let w₁ : Plane := a • b + d • c
  let w₂ : Plane := e • b + f • c
  let w₃ : Plane := g • b + h • c
  let w₄ : Plane := i • b + j • c
  have hdet₁ : w₁ 0 * w₂ 1 - w₁ 1 * w₂ 0 = (a * f - d * e) * D := by
    dsimp [w₁, w₂]
    rw [hD]
    exact det2_smul_add_smul b c a d e f
  have hdet₂ : w₃ 0 * w₄ 1 - w₃ 1 * w₄ 0 = (g * j - h * i) * D := by
    dsimp [w₃, w₄]
    rw [hD]
    exact det2_smul_add_smul b c g h i j
  have hc : (a * f - d * e) ≠ 0 ∧ (g * j - h * i) ≠ 0 :=
    mul_ne_zero_iff.mp (ne_of_gt hpos)
  have hdet₁n : w₁ 0 * w₂ 1 - w₁ 1 * w₂ 0 ≠ 0 := by
    rw [hdet₁]
    exact mul_ne_zero hc.1 hDn
  have hdet₂n : w₃ 0 * w₄ 1 - w₃ 1 * w₄ 0 ≠ 0 := by
    rw [hdet₂]
    exact mul_ne_zero hc.2 hDn
  have hw₁ : w₁ ≠ 0 := by
    intro hw
    apply hdet₁n
    rw [hw]
    simp
  have hw₂ : w₂ ≠ 0 := by
    intro hw
    apply hdet₁n
    rw [hw]
    simp
  have hw₃ : w₃ ≠ 0 := by
    intro hw
    apply hdet₂n
    rw [hw]
    simp
  have hw₄ : w₄ ≠ 0 := by
    intro hw
    apply hdet₂n
    rw [hw]
    simp
  have hDsq : 0 < D * D := mul_self_pos.mpr hDn
  have hdetpos :
      0 < (w₁ 0 * w₂ 1 - w₁ 1 * w₂ 0) *
        (w₃ 0 * w₄ 1 - w₃ 1 * w₄ 0) := by
    rw [hdet₁, hdet₂]
    calc
      0 < ((a * f - d * e) * (g * j - h * i)) * (D * D) :=
        mul_pos hpos hDsq
      _ = ((a * f - d * e) * D) * ((g * j - h * i) * D) := by ring
  change InnerProductGeometry.angle w₁ w₂ =
    InnerProductGeometry.angle w₃ w₄ at hang
  have hraw := signed_det_inner_eq_of_angle_eq w₁ w₂ w₃ w₄
    hw₁ hw₂ hw₃ hw₄ hang hdetpos
  have hi₁ : inner ℝ w₁ w₂ =
      gramDot (inner ℝ b b) (inner ℝ c c) (inner ℝ b c) a d e f := by
    exact inner_smul_add_smul_eq_gramDot b c a d e f
  have hi₂ : inner ℝ w₃ w₄ =
      gramDot (inner ℝ b b) (inner ℝ c c) (inner ℝ b c) g h i j := by
    exact inner_smul_add_smul_eq_gramDot b c g h i j
  rw [hdet₁, hdet₂, hi₁, hi₂] at hraw
  have hzero : D *
      ((a * f - d * e) *
          gramDot (inner ℝ b b) (inner ℝ c c) (inner ℝ b c) g h i j -
        (g * j - h * i) *
          gramDot (inner ℝ b b) (inner ℝ c c) (inner ℝ b c) a d e f) = 0 := by
    nlinarith [hraw]
  have := (mul_eq_zero.mp hzero).resolve_left hDn
  nlinarith
theorem coordinate_metric_of_angles
    (b c : Plane) (D x y u v : ℝ)
    (hD : D = b 0 * c 1 - b 1 * c 0) (hDn : D ≠ 0)
    (hy : 0 < y) (hu : 0 < u) (hv : 0 < v)
    (hx1 : x < 1) (hv1 : v < 1)
    (hd : 0 < v * (1 - x) - y * (1 - u))
    (he : 0 < x * (1 - v) - u * (1 - y))
    (hang1 :
      InnerProductGeometry.angle ((x - 1) • b + y • c)
          ((-1 : ℝ) • b + (0 : ℝ) • c) =
        InnerProductGeometry.angle ((0 : ℝ) • b + (-1 : ℝ) • c)
          (u • b + (v - 1) • c))
    (hang2 :
      InnerProductGeometry.angle ((u - 1) • b + v • c)
          ((x - 1) • b + y • c) =
        InnerProductGeometry.angle (u • b + (v - 1 / 2) • c)
          ((0 : ℝ) • b + (1 / 2 : ℝ) • c))
    (hang3 :
      InnerProductGeometry.angle (u • b + (v - 1) • c)
          (x • b + (y - 1) • c) =
        InnerProductGeometry.angle ((1 / 2 : ℝ) • b + (0 : ℝ) • c)
          ((x - 1 / 2) • b + y • c)) :
    2 * ((u + v) *
          (inner ℝ b b * x^2 + 2 * inner ℝ b c * x * y + inner ℝ c c * y^2) -
        (x + y) *
          (inner ℝ b b * u^2 + 2 * inner ℝ b c * u * v + inner ℝ c c * v^2)) =
      (x * v - y * u) * (inner ℝ b b - inner ℝ c c) := by
  have hpos1 :
      0 < (((x - 1) * 0 - y * (-1)) *
        (0 * (v - 1) - (-1) * u)) := by
    simpa using mul_pos hy hu
  have hraw1 :
      ((x - 1) * 0 - y * (-1)) *
          gramDot (inner ℝ b b) (inner ℝ c c) (inner ℝ b c)
            0 (-1) u (v - 1) =
        (0 * (v - 1) - (-1) * u) *
          gramDot (inner ℝ b b) (inner ℝ c c) (inner ℝ b c)
            (x - 1) y (-1) 0 := by
    apply signed_coeff_inner_eq_of_angle_eq
        (b := b) (c := c) (D := D) (a := x - 1) (d := y)
        (e := -1) (f := 0) (g := 0) (h := -1) (i := u) (j := v - 1)
    · exact hD
    · exact hDn
    · exact hang1
    · exact hpos1
  have hraw1' :
      y * gramDot (inner ℝ b b) (inner ℝ c c) (inner ℝ b c)
          0 (-1) u (v - 1) =
        u * gramDot (inner ℝ b b) (inner ℝ c c) (inner ℝ b c)
          (x - 1) y (-1) 0 := by
    simpa using hraw1
  have hpos2 :
      0 < (((u - 1) * y - v * (x - 1)) *
        (u * (1 / 2) - (v - 1 / 2) * 0)) := by
    have hu2 : 0 < u / 2 := by positivity
    have hdcoeff : (u - 1) * y - v * (x - 1) =
        v * (1 - x) - y * (1 - u) := by ring
    have hucoeff : u * (1 / 2) - (v - 1 / 2) * 0 = u / 2 := by ring
    rw [hdcoeff, hucoeff]
    exact mul_pos hd hu2
  have hraw2 := signed_coeff_inner_eq_of_angle_eq
    (b := b) (c := c) (D := D) (a := u - 1) (d := v) (e := x - 1) (f := y)
    (g := u) (h := v - 1 / 2) (i := 0) (j := 1 / 2)
    (hD := hD) (hDn := hDn) (hang := hang2) (hpos := hpos2)
  have hraw2' :
      (v * (1 - x) - y * (1 - u)) *
          gramDot (inner ℝ b b) (inner ℝ c c) (inner ℝ b c)
            u (v - 1 / 2) 0 (1 / 2) =
        (u / 2) *
          gramDot (inner ℝ b b) (inner ℝ c c) (inner ℝ b c)
            (u - 1) v (x - 1) y := by
    have hdcoeff : (u - 1) * y - v * (x - 1) =
        v * (1 - x) - y * (1 - u) := by ring
    have hucoeff : u * (1 / 2) - (v - 1 / 2) * 0 = u / 2 := by ring
    rw [hdcoeff, hucoeff] at hraw2
    exact hraw2
  have hpos3 :
      0 < ((u * (y - 1) - (v - 1) * x) *
        ((1 / 2) * y - 0 * (x - 1 / 2))) := by
    have hy2 : 0 < y / 2 := by positivity
    have hecoeff : u * (y - 1) - (v - 1) * x =
        x * (1 - v) - u * (1 - y) := by ring
    have hycoeff : (1 / 2) * y - 0 * (x - 1 / 2) = y / 2 := by ring
    rw [hecoeff, hycoeff]
    exact mul_pos he hy2
  have hraw3 := signed_coeff_inner_eq_of_angle_eq
    (b := b) (c := c) (D := D) (a := u) (d := v - 1) (e := x) (f := y - 1)
    (g := 1 / 2) (h := 0) (i := x - 1 / 2) (j := y)
    (hD := hD) (hDn := hDn) (hang := hang3) (hpos := hpos3)
  have hraw3' :
      (x * (1 - v) - u * (1 - y)) *
          gramDot (inner ℝ b b) (inner ℝ c c) (inner ℝ b c)
            (1 / 2) 0 (x - 1 / 2) y =
        (y / 2) *
          gramDot (inner ℝ b b) (inner ℝ c c) (inner ℝ b c)
            u (v - 1) x (y - 1) := by
    have hecoeff : u * (y - 1) - (v - 1) * x =
        x * (1 - v) - u * (1 - y) := by ring
    have hycoeff : (1 / 2) * y - 0 * (x - 1 / 2) = y / 2 := by ring
    rw [hecoeff, hycoeff] at hraw3
    exact hraw3
  let P : ℝ := inner ℝ b b
  let Q : ℝ := inner ℝ c c
  let R : ℝ := inner ℝ b c
  have hb0 : b ≠ 0 := by
    intro hb
    apply hDn
    rw [hD]
    rw [hb]
    simp
  have hP : 0 < P := by
    dsimp [P]
    exact real_inner_self_pos.mpr hb0
  have hnorm := angle_bridge_outputs_normalize x y u v P Q R
    (by simpa [P, Q, R] using hraw1')
    (by simpa [P, Q, R] using hraw2')
    (by simpa [P, Q, R] using hraw3')
  have hmetric0 := coordinate_scalar_elimination x y u v P Q R
    hu hv hy hx1 hv1 hP hnorm.1 hnorm.2.1 hnorm.2.2
  dsimp [P, Q, R] at hmetric0 ⊢
  linarith
theorem coordinate_circumcenter_finish
    (b c k l o : Plane) (x y u v : ℝ)
    (hDelta : 0 < x * v - y * u)
    (hk : k = x • b + y • c) (hl : l = u • b + v • c)
    (hOk : ‖o‖ = ‖o - k‖) (hOl : ‖o‖ = ‖o - l‖)
    (hmetric :
      2 * ((u + v) *
          (inner ℝ b b * x^2 + 2 * inner ℝ b c * x * y + inner ℝ c c * y^2) -
        (x + y) *
          (inner ℝ b b * u^2 + 2 * inner ℝ b c * u * v + inner ℝ c c * v^2)) =
        (x * v - y * u) * (inner ℝ b b - inner ℝ c c)) :
    ‖o - (1 / 2 : ℝ) • b‖ = ‖o - (1 / 2 : ℝ) • c‖ := by
  have hkk : inner ℝ k k =
      inner ℝ b b * x^2 + 2 * inner ℝ b c * x * y + inner ℝ c c * y^2 := by
    rw [hk]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [real_inner_comm c b]
    ring
  have hll : inner ℝ l l =
      inner ℝ b b * u^2 + 2 * inner ℝ b c * u * v + inner ℝ c c * v^2 := by
    rw [hl]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [real_inner_comm c b]
    ring
  have hOk' : 2 * inner ℝ o k = inner ℝ k k := by
    have hs := congrArg (fun z : ℝ => z ^ 2) hOk
    rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq k] at hs
    nlinarith
  have hOl' : 2 * inner ℝ o l = inner ℝ l l := by
    have hs := congrArg (fun z : ℝ => z ^ 2) hOl
    rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq l] at hs
    nlinarith
  have hweighted :
      4 * ((u + v) * inner ℝ o k - (x + y) * inner ℝ o l) =
        (x * v - y * u) * (inner ℝ b b - inner ℝ c c) := by
    calc
      _ = 2 * ((u + v) * inner ℝ k k - (x + y) * inner ℝ l l) := by
        rw [← hOk', ← hOl']
        ring
      _ = _ := by rw [hkk, hll]; exact hmetric
  have hlin :
      (x * v - y * u) • (b - c) =
        (u + v) • k - (x + y) • l := by
    rw [hk, hl]
    module
  have hlininner := congrArg (fun z : Plane => inner ℝ o z) hlin
  simp only [inner_sub_right, real_inner_smul_right] at hlininner
  have hcancel :
      (x * v - y * u) *
        (4 * inner ℝ o (b - c) - (inner ℝ b b - inner ℝ c c)) = 0 := by
    rw [inner_sub_right]
    nlinarith [hweighted, hlininner]
  have hdelta0 : x * v - y * u ≠ 0 := ne_of_gt hDelta
  have hbase :
      4 * inner ℝ o (b - c) = inner ℝ b b - inner ℝ c c := by
    have := (mul_eq_zero.mp hcancel).resolve_left hdelta0
    linarith
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sub_sq_real, norm_sub_sq_real]
  simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs]
  norm_num [abs_of_nonneg] at ⊢
  have hbNorm : (1 / 2 * ‖b‖) ^ 2 = (1 / 4) * inner ℝ b b := by
    rw [real_inner_self_eq_norm_sq]
    ring
  have hcNorm : (1 / 2 * ‖c‖) ^ 2 = (1 / 4) * inner ℝ c c := by
    rw [real_inner_self_eq_norm_sq]
    ring
  rw [hbNorm, hcNorm]
  rw [inner_sub_right] at hbase
  linarith
/-- With the configuration described above, the circumcentre
`O` of triangle `AKL` satisfies `OM = ON`, where `M`, `N` are the midpoints of
`AB`, `AC`. -/
theorem main_theorem
    (A B C K L O : Plane)
    -- `ABC` is a nondegenerate triangle.
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    -- `M`, `N` are the midpoints of `AB`, `AC`.
    (M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    -- `K` is inside triangle `BMC`; `L` is inside triangle `BNC`.
    (hK : InsideTriangle B M C K)
    (hL : InsideTriangle B N C L)
    -- `K` inside angle `∠ L B A`; `L` inside angle `∠ A C K`.
    (hKangle : InsideAngle L B A K)
    (hLangle : InsideAngle A C K L)
    -- The three angle equalities.
    (h1 : ∠ K B A = ∠ A C L)
    (h2 : ∠ L B K = ∠ L N C)
    (h3 : ∠ L C K = ∠ B M K)
    -- `O` is the circumcentre of triangle `AKL`.
    (hO : IsCircumcentre A K L O) :
    dist O M = dist O N := by
  rcases hK with ⟨ak, bk, ck, hak, hbk, hck, hsumK, hK⟩
  rcases hL with ⟨al, bl, cl, hal, hbl, hcl, hsumL, hL⟩
  rcases hKangle with ⟨s, t, hs, ht, hKangle⟩
  rcases hLangle with ⟨p, q, hp, hq, hLangle⟩
  let b : Plane := B - A
  let c : Plane := C - A
  let x : ℝ := ak + bk / 2
  let y : ℝ := ck
  let u : ℝ := al
  let v : ℝ := bl / 2 + cl
  let D : ℝ := b 0 * c 1 - b 1 * c 0
  have hDn : D ≠ 0 := by
    dsimp [D, b, c]
    exact det2_ne_zero_of_not_collinear A B C hABC
  have hMA : M - A = (1 / 2 : ℝ) • b := by
    rw [hM, midpoint_sub_left]
    norm_num [b, invOf_eq_inv]
  have hNA : N - A = (1 / 2 : ℝ) • c := by
    rw [hN, midpoint_sub_left]
    norm_num [c, invOf_eq_inv]
  have hKtranslate :
      K - A = ak • (B - A) + bk • (M - A) + ck • (C - A) := by
    rw [hK, show ck = 1 - ak - bk by linarith [hsumK]]
    module
  have hLtranslate :
      L - A = al • (B - A) + bl • (N - A) + cl • (C - A) := by
    rw [hL, show cl = 1 - al - bl by linarith [hsumL]]
    module
  have hKA : K - A = x • b + y • c := by
    rw [hKtranslate, hMA]
    dsimp [x, y, b, c]
    module
  have hLA : L - A = u • b + v • c := by
    rw [hLtranslate, hNA]
    dsimp [u, v, b, c]
    module
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < y := by exact hck
  have hu : 0 < u := by exact hal
  have hv : 0 < v := by dsimp [v]; positivity
  have hxy : x + y < 1 := by
    dsimp [x, y]
    nlinarith
  have huv : u + v < 1 := by
    dsimp [u, v]
    nlinarith
  have hKB : K - B = (x - 1) • b + y • c := by
    calc
      K - B = (K - A) - (B - A) := by module
      _ = (x • b + y • c) - b := by rw [hKA]
      _ = (x - 1) • b + y • c := by module
  have hLB : L - B = (u - 1) • b + v • c := by
    calc
      L - B = (L - A) - (B - A) := by module
      _ = (u • b + v • c) - b := by rw [hLA]
      _ = (u - 1) • b + v • c := by module
  have hLC : L - C = u • b + (v - 1) • c := by
    calc
      L - C = (L - A) - (C - A) := by module
      _ = (u • b + v • c) - c := by rw [hLA]
      _ = u • b + (v - 1) • c := by module
  have hKC : K - C = x • b + (y - 1) • c := by
    calc
      K - C = (K - A) - (C - A) := by module
      _ = (x • b + y • c) - c := by rw [hKA]
      _ = x • b + (y - 1) • c := by module
  have hfactors := proper_angle_factors_pos A B C K L x y u v s t p q D
    rfl hDn (by simpa [b, c] using hKA) (by simpa [b, c] using hLA)
    ht hp hx hv hKangle hLangle
  have hd : 0 < v * (1 - x) - y * (1 - u) := hfactors.1
  have he : 0 < x * (1 - v) - u * (1 - y) := hfactors.2
  have hv1 : v < 1 := by nlinarith [huv, hu]
  have hDelta : 0 < x * v - y * u :=
    coordinate_det_pos x y u v hx hy hu hv hxy hv1 hd he
  have hAB : A - B = (-1 : ℝ) • b + (0 : ℝ) • c := by
    dsimp [b]
    module
  have hAC : A - C = (0 : ℝ) • b + (-1 : ℝ) • c := by
    dsimp [c]
    module
  have hLN : L - N = u • b + (v - 1 / 2) • c := by
    calc
      L - N = (L - A) - (N - A) := by module
      _ = (u • b + v • c) - (1 / 2 : ℝ) • c := by rw [hLA, hNA]
      _ = u • b + (v - 1 / 2) • c := by module
  have hCN : C - N = (0 : ℝ) • b + (1 / 2 : ℝ) • c := by
    calc
      C - N = (C - A) - (N - A) := by module
      _ = c - (1 / 2 : ℝ) • c := by rw [hNA]
      _ = (0 : ℝ) • b + (1 / 2 : ℝ) • c := by module
  have hBM : B - M = (1 / 2 : ℝ) • b + (0 : ℝ) • c := by
    calc
      B - M = (B - A) - (M - A) := by module
      _ = b - (1 / 2 : ℝ) • b := by rw [hMA]
      _ = (1 / 2 : ℝ) • b + (0 : ℝ) • c := by module
  have hKM : K - M = (x - 1 / 2) • b + y • c := by
    calc
      K - M = (K - A) - (M - A) := by module
      _ = (x • b + y • c) - (1 / 2 : ℝ) • b := by rw [hKA, hMA]
      _ = (x - 1 / 2) • b + y • c := by module
  have hang1 :
      InnerProductGeometry.angle ((x - 1) • b + y • c)
          ((-1 : ℝ) • b + (0 : ℝ) • c) =
        InnerProductGeometry.angle ((0 : ℝ) • b + (-1 : ℝ) • c)
          (u • b + (v - 1) • c) := by
    change InnerProductGeometry.angle (K - B) (A - B) =
      InnerProductGeometry.angle (A - C) (L - C) at h1
    rw [hKB, hAB, hAC, hLC] at h1
    exact h1
  have hang2 :
      InnerProductGeometry.angle ((u - 1) • b + v • c)
          ((x - 1) • b + y • c) =
        InnerProductGeometry.angle (u • b + (v - 1 / 2) • c)
          ((0 : ℝ) • b + (1 / 2 : ℝ) • c) := by
    change InnerProductGeometry.angle (L - B) (K - B) =
      InnerProductGeometry.angle (L - N) (C - N) at h2
    rw [hLB, hKB, hLN, hCN] at h2
    exact h2
  have hang3 :
      InnerProductGeometry.angle (u • b + (v - 1) • c)
          (x • b + (y - 1) • c) =
        InnerProductGeometry.angle ((1 / 2 : ℝ) • b + (0 : ℝ) • c)
          ((x - 1 / 2) • b + y • c) := by
    change InnerProductGeometry.angle (L - C) (K - C) =
      InnerProductGeometry.angle (B - M) (K - M) at h3
    rw [hLC, hKC, hBM, hKM] at h3
    exact h3
  have hx1 : x < 1 := by linarith [hxy, hy]
  have hmetric :
      2 * ((u + v) *
          (inner ℝ b b * x^2 + 2 * inner ℝ b c * x * y + inner ℝ c c * y^2) -
        (x + y) *
          (inner ℝ b b * u^2 + 2 * inner ℝ b c * u * v + inner ℝ c c * v^2)) =
        (x * v - y * u) * (inner ℝ b b - inner ℝ c c) :=
    coordinate_metric_of_angles b c D x y u v rfl hDn hy hu hv hx1 hv1 hd he
      hang1 hang2 hang3
  rcases hO with ⟨hOK, hOL⟩
  have hOkNorm : ‖O - A‖ = ‖(O - A) - (K - A)‖ := by
    rw [show (O - A) - (K - A) = O - K by module]
    simpa only [dist_eq_norm] using hOK
  have hOlNorm : ‖O - A‖ = ‖(O - A) - (L - A)‖ := by
    rw [show (O - A) - (L - A) = O - L by module]
    simpa only [dist_eq_norm] using hOL
  have hfinish := coordinate_circumcenter_finish b c (K - A) (L - A) (O - A)
    x y u v hDelta hKA hLA hOkNorm hOlNorm hmetric
  have hOM : O - M = (O - A) - (1 / 2 : ℝ) • b := by
    rw [← hMA]
    module
  have hON : O - N = (O - A) - (1 / 2 : ℝ) • c := by
    rw [← hNA]
    module
  simpa only [dist_eq_norm, hOM, hON] using hfinish
