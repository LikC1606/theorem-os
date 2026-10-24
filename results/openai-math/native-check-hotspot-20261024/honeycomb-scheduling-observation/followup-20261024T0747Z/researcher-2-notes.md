# RESEARCH.md — HoneycombBridgeFiniteness

Assignment `initial_research_2` (researcher-2), task digest
`d3ee9175353ff80857b85331ad4cbd5f804574c36eba9e4564ee849696aac5e4`.
Consumer of the reporting chain below: task `initial_goal_1`, digest
`ab8c91c92c1d5d985ed03edfaee27bbef6df38455b84a82711d07d8d13e77890`, whose theorem is
`OAI.PolynomialVacuumBridge.Corridor.finite_bridge_sums`.
(The earlier deliveries in the log used the stale digest `34273f03...` / `342803c1...`; the
digest above is the one displayed in the current in-flight task table.)

## Status

**Conclusion of this investigation: inconclusive.** The original theorem is *not* proved here.
The checked reduction and structural work from checkpoint 3 is unchanged (full source in the
fence at the bottom; no `sorry`/`admit`/`native_decide`/`axiom`/`unsafe`):

1. The width `h = 1` case of the missing estimate is **proved unconditionally**, therefore
   `finite_bridge_sums_at_one` (all six `FiniteBridgeSums` conjuncts at `h = 1`) is proved.
2. The consumer reduction is **strengthened**: `FiniteBridgeSums` follows from the strip
   estimate restricted to widths `h ≥ 2` (`finite_bridge_sums_of_stripGrowth_ge_two`).
3. The frozen combinatorial object is identified structurally as a **brick-wall (honeycomb)
   strip** (checked lemmas `hexX`, `eq_of_hexX_layer`, `hexX_step`, `step_dichotomy`,
   `int_walk_monotone`, `chain_hexX_walk`).
4. **Width monotonicity is corrected**: the old claim that the *same vertex list* embeds
   `BridgePath h` into `BridgePath (h+1)` is **false** (the terminal layer changes with `h`).
   The replacement is checked: `bridgePathSucc` is an injection from length-`n` width-`h` paths
   into length-`(n+2)` width-`(h+1)` paths (`card_le_card_width_succ`).
5. Two elementary relaxations are shown (one in Lean, one by proof + numerics) to be unable to
   yield the needed strict inequality; this is recorded so that no further work is wasted on
   them (`## Why crude relaxations cannot work`).

**New in checkpoint 4 (advisory enumeration only, not Lean-checked).** Exact DFS counts of the
frozen `BridgePath h` objects were extended; see `## Library and environment facts` for the
data. Two consequences sharpen the route analysis:

6. The `h = 2` even-length counts satisfy, on all 29 computed terms `n = 4,6,…,60`, the exact
   order-`7` linear recurrence
   `a_k = 2 a_{k-1} + a_{k-2} - 3 a_{k-3} + a_{k-4} - a_{k-6} + a_{k-7}`
   (where `a_k = N_2(2k+4)`). Its characteristic polynomial factors as
   `(x^2 - 1)^2 (x^3 - 2x^2 + x - 1)`; the dominant root is
   `1.7548776662466927600…`, giving per-vertex base `1.3247179572447460259…`, far below
   `2cos(π/8) = 1.8477590650…`. This is a concrete transfer-matrix target for one width,
   **not a proof** and not a reduction of the `∀ h ≥ 2` obligation.
7. The observed width-`h` bases for small `h` remain strictly below `2cos(π/8)`:
   approximately `1.000, 1.324718, 1.488678, 1.58538, 1.64799, 1.67876, …`. They increase with
   `h`, so no uniform `β` exists and the frozen per-`h` quantifier is necessary.

`generated/problem/Submission.lean` is **untouched** by this task and is byte-identical to
`generated/problem/Challenge.lean` and to the seed:
sha256 `6acaeab1940555d1df29856e504deae4f9edf7777231969b9b7d13515731d830`, i.e. the original
`sorry` at line 60 is still there. Peer deliveries claiming the reduction is *integrated* into
`Submission.lean` are not confirmed by this worktree; consistent with host feedback
`math_task_existing_declaration_changed` on `finite_bridge_sums` for task `sums_reduction`.

The Lean development in the fence was re-extracted from this file and recompiled with the
pinned toolchain in this checkpoint (see `## Verification performed`). `.scratch/` is removed
by the host before checking ownership; **the fence below is the durable copy.**

## Corrections relative to earlier RESEARCH checkpoints

| earlier claim | status |
|---|---|
| "`BridgePath h ↪ BridgePath (h+1)` because the same list of vertices is still in the strip" | **FALSE / retracted.** `terminal` requires the last layer to be `h-1`; raising `h` breaks it. Replaced by the checked `+2` extension `bridgePathSucc` and `card_le_card_width_succ`. |
| "the `h = 1` instance is not yet proved in Lean" | **superseded**: `bridge1_card_le_two`, `stripGrowthAtOne`, `finite_bridge_sums_at_one` are proved. |
| "the reduction is integrated into `Submission.lean`" (peer claim) | not true in this worktree; the file is the pristine seed. |
| unweighted "column projection" counting as an upper bound | **unsound** (each horizontal step has two realizations). See `## Why crude relaxations cannot work`. |
| earlier `h ≥ 8` growth bases quoted from a single length | withdrawn (a single length cannot determine a growth base). |

## What is discharged (checked)

With `alpha = criticalActivity = (2 cos (π/8))⁻¹` (`0 < alpha < 1`,
`alpha * (2 cos (π/8)) = 1`, `alpha^2 = (2+√2)⁻¹`):

1. `weight p ≤ firstLengthWeight p`, both nonnegative
   (`weight_nonneg`, `weight_le_firstLengthWeight`), hence
   `summable_weight_of_summable_firstLengthWeight`.
2. **Counting → summability** (`summable_firstLengthWeight_of_profile`,
   `summable_firstLengthWeight_of_count_bound`): if for a fixed `h` every finite set `s` of
   length-`n` bridge paths satisfies `(s.card : ℝ) ≤ C * β^n`, with `0 ≤ C`, `0 ≤ β`,
   `β * alpha < 1`, then `Summable (firstLengthWeight (h := h))`. Proof: group any finite set by
   `vertices.length` (`Finset.sum_fiberwise_of_maps_to`), all weights in a fibre equal
   `alpha^n`, bound by `sum n * C * (β*alpha)^n` via
   `summable_pow_mul_geometric_of_norm_lt_one`, get a bound uniform in the finite set, and
   apply `summable_of_sum_le`.
3. **All six conjuncts** from first-length summability
   (`finite_bridge_sums_of_firstLengthWeight`): the two normalised clauses are
   `Summable.div_const`, the two confined clauses are `Summable.subtype` restricted to
   `InLogCorridor`. `InLogCorridor` is *never* analysed — the subtype restriction is free, so
   no geometry of `position` is required anywhere in the reduction.
4. `StripCountBound` (the `alpha`-normalised form), `stripCountBound_of_stripGrowthBelowMu`,
   and the consumer
   `finite_bridge_sums_of_stripGrowthBelowMu : StripGrowthBelowMu → FiniteBridgeSums`.
5. **Strengthened consumer** `finite_bridge_sums_of_stripGrowth_ge_two`: `FiniteBridgeSums`
   follows from the same estimate quantified only over `h ≥ 2`
   (`stripGrowthBelowMu_of_ge_two`, using the proved `h = 1` instance).

## Width one is fully discharged

`h = 1` forces every vertex onto layer `0` (`layer_eq_zero_of_bridge1`), so every step is
horizontal and the checked coordinate `hexX` (`up i j ↦ 2i+j`, `down i j ↦ 2i+j+1`) moves by
exactly `±1` (`hexX_step`) and separates vertices together with the layer
(`eq_of_hexX_layer`). A finite injective `±1` walk on `ℤ` never reverses
(`int_walk_monotone`), hence a width-1 bridge path is a monotone run starting at
`hexX (.up 0 0) = 0`. The terminal condition is `down i 0`, i.e. `hexX = 2i+1`, so the length is
even; a monotone run is determined by its direction, giving:

* `bridge1CoordFun`, `bridge1_start`, `bridge1_hexX`, `bridge1_length_ge_two`,
  `bridge1_second`, `bridge1_det` — two paths with the same length are equal;
* `bridge1_card_le_two : ∀ (n) (s : Finset (BridgePath 1)), (∀ p ∈ s, p.vertices.length = n) →
  s.card ≤ 2` (via `Finset.card_le_card_of_injOn` into `{-1, 1} : Finset ℤ`);
* `stripGrowthAtOne : ∃ C β, 0 ≤ C ∧ 0 ≤ β ∧ β < 2 cos(π/8) ∧ …` with `C = 2`, `β = 1`
  (needs `1 < 2 cos(π/8)`, obtained from `Real.cos_pi_div_eight` and `√2 < 2`);
* `finite_bridge_sums_at_one` — all six conjuncts of `FiniteBridgeSums` at `h = 1`,
  unconditionally.

## The exact remaining obligation

Verbatim from the checked file:

```lean
def StripGrowthBelowMu : Prop :=
  ∀ h : ℕ, 1 ≤ h → ∃ C β : ℝ, 0 ≤ C ∧ 0 ≤ β ∧
    β < 2 * Real.cos (Real.pi / 8) ∧
    ∀ (n : ℕ) (s : Finset (BridgePath h)),
      (∀ p ∈ s, p.vertices.length = n) → (s.card : ℝ) ≤ C * β ^ n
```

After `h = 1`, the residual obligation is exactly:

```lean
∀ h : ℕ, 2 ≤ h → ∃ C β : ℝ, 0 ≤ C ∧ 0 ≤ β ∧
  β < 2 * Real.cos (Real.pi / 8) ∧
  ∀ (n : ℕ) (s : Finset (BridgePath h)),
    (∀ p ∈ s, p.vertices.length = n) → (s.card : ℝ) ≤ C * β ^ n
```

and the checked theorem `finite_bridge_sums_of_stripGrowth_ge_two` turns it into
`FiniteBridgeSums`. Equivalently: `BridgePath h` of length `n` is at most `C_h β_h^n` with
`β_h < 2cos(π/8)`; i.e. the width-`h` strip growth rate `μ_h` satisfies `μ_h < 2cos(π/8)`.

This is a genuine research-level input, not algebra:

* `BridgePath h` has unbounded length: `examplePath2 : BridgePath 2` is checked, and an
  explicit `4K+2`-vertex `BridgePath 2` family was verified for `K = 1..12` against the frozen
  predicate by an advisory enumerator (not Lean-checked). So an exponential bound is genuinely
  necessary — no finite-support trick applies.
* `μ_h` increases with `h` (see width monotonicity below for the checked `+2` version, and the
  last section of this paragraph) and converges up to the bulk honeycomb value
  `2 cos(π/8) = √(2+√2) = 1.8477590650…`. Consequently **no uniform `β` works**: any proof must
  produce a *strict* per-`h` gap, and the available margin shrinks as `h` grows. It cannot be a
  quantitative bound uniform in `h`.
* The frozen threshold is exactly the (known, deep) connective constant of the *infinite*
  hexagonal lattice; so the obligation is a finite-width subcriticality statement for
  hexagonal self-avoiding bridges.

## Width monotonicity (corrected and checked)

The naive same-list embedding is false. The checked replacement appends the two vertices
`up i h`, `down i h` above the terminal vertex `down i (h-1)` of a width-`h` path:

* `adjacent_down_up_climb`, `adjacent_up_down_same` — the two new adjacencies;
* `exists_path_succ_with` / `bridgePathSucc` — the extension is a genuine `BridgePath (h+1)`
  (all six structure fields re-verified, `Nodup` uses the strict layer increase);
* `bridgePathSucc_vertices`, `bridgePathSucc_length` (`length + 2`);
* `bridgePathSucc_injective` (`List.take_append_of_le_length` + `List.take_length`);
* `card_le_card_width_succ :` length-`n` width-`h` paths inject into length-`(n+2)` width-`(h+1)`
  paths. Needs `bridgePathDecidableEq` (defined locally from vertex-list equality, since
  `BridgePath` has no derived `DecidableEq`; use `Finset.map` with the embedding).

Consequence: `N_h(n) ≤ N_{h+1}(n+2)`, i.e. `μ_h ≤ μ_{h+1}`, which is the checked part of
"the growth constants increase". It also explains why `stripGrowthBelowMu_of_ge_two` cannot be
improved to an induction on `h`: monotonicity goes the wrong way for transferring an upper
bound downward.

## Why crude relaxations cannot work

Let `c_t = hexX v_t` be the column coordinate along a bridge path. Checked facts give:

* `step_dichotomy`: every edge is either **horizontal** (`layer` unchanged, `c` moves by `±1`)
  or **vertical** (`layer` moves by `±1`); in the vertical case the column is unchanged.
* `eq_of_hexX_layer`: `(hexX, layer)` is injective, so a simple path has at most `h` vertices
  in any fixed column (`h` layers). Likewise a simple path crosses any *cut* between columns
  `c` and `c+1` at most `h` times (the cut has `h` horizontal edges).

Both natural relaxations of these facts are useless:

1. **Column projection.** The projection `(c_t)` is a walk on `ℤ` with steps `{-1,0,+1}` in
   which each value is used at most `h` times. But this projection is **not** injective: every
   horizontal step has **two** realizations (`up i j → down i j` or `down (i-1) j`, and dually),
   so an upper bound needs the weight `2^{#horizontal steps}`. The weighted count is already
   `≥ 2^n` (take the all-right walk: weight `2^n`, each column used once), and `2 > 2cos(π/8)`.
   Hence a projection bound with `β < 2cos(π/8)` is impossible. *Warning*: counting the
   unweighted projection is unsound; for the record, that unweighted count (computed this turn,
   advisory) has growth `≈ 1.7549` at `h = 2` and `≈ 2.1669` at `h = 3`.
2. **Cut-crossing relaxation.** Encoding a path by the sequence of cut edges it uses gives
   `h` symbols per cut; the resulting relaxation (advisory numerics) has growth `≈ 1.8552` at
   `h = 2`, already **above** `2cos(π/8) ≈ 1.84776`, while the true `h = 2` value is `≈ 1.3248`.
   So the relaxation error exceeds the whole available gap.

Moral: a proof must keep the genuine two-dimensional self-avoidance constraint (a transfer
matrix over column states, or an equivalent injection). No relaxation that forgets which
vertices of a column are used can produce the strict inequality.

## Library and environment facts

* Pinned toolchain, `import Mathlib` only. `Real.cos_pi_div_eight : cos (π/8) = √(2+√2)/2` is
  available via `Mathlib` (`Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`).
* Lemmas used by the checked development and confirmed by `#check`: `Finset.card_le_card_of_injOn`,
  `Finset.card_le_two`, `Finset.sum_fiberwise_of_maps_to`, `Summable.of_nonneg_of_le`,
  `Summable.subtype`, `Summable.div_const`, `summable_pow_mul_geometric_of_norm_lt_one`,
  `Real.cos_pos_of_mem_Ioo`, `Real.sq_sqrt`, `List.isChain_iff_getElem`, `List.IsChain.getElem`,
  `List.IsChain.append`, `List.Nodup.getElem_inj`, `List.getLast?_append_of_ne_nil`,
  `List.take_append_of_le_length`, `List.take_of_length_le`, `List.take_length`.
  `List.nodup_iff_getElem_injective` is **absent**.
* `search-lean` queries that return nothing usable: `honeycomb`, `hexagonal`,
  `self avoiding walk`, `connective constant`, `transfer matrix`, `Perron Frobenius`, `lattice
  animal`, `spectralRadius` (only Banach/C*-algebra results), `Matrix.IsPrimitive` (only
  `isIrreducible`, no Perron-root bound). **There is no finite-width SAW subcriticality,
  transfer-matrix or Perron-root theorem in the local corpus.** This is the stable local
  obstruction for the residual obligation.
* Numerics (advisory, **not** proof and not Lean-checked). Two independent DFS enumerators were
  cross-validated against the frozen predicate. **These counts are now superseded by the longer
  exact runs in the next bullet** (the earlier `h = 2`, `h = 3` prefixes agree term by term).
  `h = 1`: `N(2k) = 2`, `N(odd) = 0`. **No counterexample was found at any width.**
* Extended exact even-length counts of the frozen objects (C++ DFS; validated against the
  frozen `adjacent`/`layer`/`source`/`terminal`/`inStrip` predicate; advisory only):
  * `h = 2`, `n = 4,6,…,60` (29 terms):
    `4, 8, 12, 24, 44, 82, 144, 258, 454, 804, 1412, 2486, 4364, 7668, 13458, 23628, 41466,
    72780, 127722, 224150, 393358, 690310, 1211412, 2125896, 3730690, 6546922, 11489050,
    20161896, 35381664`.
  * `h = 3`, `n = 6,8,…,44` (20 terms):
    `8, 24, 48, 112, 248, 568, 1296, 2972, 6692, 15054, 33650, 75072, 167080, 371552, 825168,
    1831488, 4062526, 9007894, 19966884, 44249850`.
  * `h = 4`, `n = 8,…,36`:
    `16, 64, 160, 416, 1040, 2616, 6592, 16728, 42472, 108188, 274728, 695992, 1757578,
    4427426, 11128064`.
  * `h = 5`, `n = 10,…,32`:
    `32, 160, 480, 1376, 3776, 10208, 27488, 74064, 199728, 540376, 1464848, 3978356`.
  * `h = 6`, `n = 12,…,30`:
    `64, 384, 1344, 4224, 12544, 36128, 102720, 290240, 817824, 2304816`.
  * `h = 7`, `n = 14,…,28`: `128, 896, 3584, 12288, 39168, 119552, 356864, 1051584`.
  * `h = 8`, `n = 16,…,28`: `256, 2048, 9216, 34304, 116736, 376192, 1175040`.
  * `h = 9`, `n = 18,…,28`: `512, 4608, 23040, 92672, 335360, 1137664`.
  * `h = 10`, `n = 20,…,26`: `1024, 10240, 56320, 243712`.
  **Caveat:** for `h ≥ 8` the available lengths are too short to estimate a growth base; only
  the small-width bases below should be used.
* Observed per-vertex bases for the small widths are
  `h = 1,2,3,4,5,6 ≈ 1.000000, 1.324718, 1.488678, 1.58538, 1.64799, 1.67876`, all strictly
  below `2cos(π/8) = 1.8477590650…` and increasing in `h`.
* **Exact `h = 2` recurrence (empirical, unproved).** With `a_k = N_2(2k+4)` (`k ≥ 0`),
  Berlekamp–Massey over `ℚ` on the 29 terms above returns
  `a_k = 2 a_{k-1} + a_{k-2} - 3 a_{k-3} + a_{k-4} - a_{k-6} + a_{k-7}`,
  verified on **all** 22 steps where it is defined. Characteristic polynomial
  `x^7 - 2x^6 - x^5 + 3x^4 - x^3 + x - 1 = (x^2 - 1)^2 (x^3 - 2x^2 + x - 1)`. Dominant root
  `1.7548776662466927600…`, per-vertex base `1.3247179572447460259…`. This is a *candidate*
  transfer-matrix denominator and is **not** proved; the older denominator
  `(1-y)^2(1-2y^2-y^3-y^4-y^5)` recorded in checkpoint 3 is **withdrawn** as inconsistent with
  the longer data.
* `h ≥ 3` Berlekamp–Massey fits are short-data overfits and must **not** be treated as
  recurrences.

## Planning: smallest complete task graph

The smallest valid graph that can close the frozen target is:

```
strip_growth_below_mu   -- prove  ∀ h ≥ 2, ∃ C_h β_h < 2cos(π/8), card ≤ C_h β_h^n
        ↓
initial_goal_1          -- apply the checked glue to the pristine Submission.lean
                           (finite_bridge_sums : FiniteBridgeSums, unconditional)
```

Notes for the lead:

* `sums_reduction` is *mathematically* discharged by the fence below
  (`finite_bridge_sums_of_stripGrowthBelowMu`, plus the strengthened
  `finite_bridge_sums_of_stripGrowth_ge_two`), but *file-level* integration is still missing
  because `Submission.lean` is the pristine seed and the host rejected a previous attempt with
  `math_task_existing_declaration_changed`. Integrating it is short glue (helper lemmas with new
  `bridge_`-prefixed names plus the body of `finite_bridge_sums` applied to the strip estimate),
  and must be re-done on the pristine declaration. Do **not** rename or re-parameterise
  `finite_bridge_sums`.
* Splitting `strip_growth_below_mu` by width does not close the goal: the statement is `∀ h ≥ 2`
  and the growth constants increase towards the threshold, so a per-width computation with an
  explicit transfer matrix must be accompanied by a real argument that produces, for *every* `h`,
  some `β_h < 2cos(π/8)`. A single width (even `h = 2`) is an independent sub-case, not a
  reduction of the goal. It would only be worth assigning as a methodology pilot.
* Two candidate routes, both research-level:
  (a) a *uniform-in-`h`* argument, e.g. a strip transfer matrix whose Perron root is bounded by
      an explicit `h`-dependent `β_h` with a proof that `β_h < 2cos(π/8)` for all `h`
      (needs a positivity/eigenvalue certificate such as `T^k w ≤ c • w` with `c^{1/k} < 2cos(π/8)`,
      plus an encoding theorem from `BridgePath h` into the matrix model);
  (b) import/formalise the exact honeycomb connective constant (`2cos(π/8)`, Duminil-Copin–Smirnov)
      **plus** a strictness argument for finite width. Neither component is in the local corpus.
* If the lead's budget is limited, the honest assessment is that the frozen target is not
  closable by glue: the one missing estimate *is* the mathematical content of the problem.

## Verification performed

Repeated check in this checkpoint, starting from **this file** (not from `.scratch/`, which the
host partially removes between turns):

1. extract the last ```` ```lean ```` block of `RESEARCH.md` to a temp file →
   **854 lines**, sha256
   `14d52c1af8fa50f49ff7a8a6acd15a6acfecd3f88df7b0cd375fdc486a0449f2`
   (same digest as the previously verified `.scratch/tmp/FENCE.lean`);
2. `cd generated/problem && timeout 1800 lake env lean "$TMPDIR/research_extract.lean"`
   → **EXIT=0**, no warnings;
3. textual audit of the extracted block: no `sorry`, `admit`, `native_decide`, `axiom`,
   `unsafe` (`grep` exit 1 for all patterns);
4. `#print axioms` on `finite_bridge_sums_of_stripGrowth_ge_two`,
   `finite_bridge_sums_at_one`, `bridge1_card_le_two`, `card_le_card_width_succ` →
   `[propext, Classical.choice, Quot.sound]` only (checked this checkpoint by appending the
   `#print axioms` commands to a copy of the fence);
5. `head -57` of the fence is **byte-identical** to `head -57` of
   `generated/problem/Submission.lean` (verified by `diff`), so the fence reproduces the frozen
   context verbatim before adding helpers;
6. `sha256sum generated/problem/Submission.lean generated/problem/Challenge.lean` agree
   (`6acaeab1…`), i.e. the owned file was not modified.

## Reusable Lean source (854 lines, compiled standalone)

Self-contained: it reproduces the frozen declarations verbatim in
`namespace OAI.PolynomialVacuumBridge.Corridor`, then adds the checked helpers. To reuse, either
append the helper part after the frozen definitions in `Submission.lean`, or compile the whole
block as a standalone file (as done here).

```lean
import Mathlib

namespace OAI

namespace PolynomialVacuumBridge.Corridor

inductive Vertex where
  | up (i j : ℤ)
  | down (i j : ℤ)
  deriving DecidableEq

noncomputable def position : Vertex → ℝ × ℝ
  | .up i j => ((i : ℝ) + (j : ℝ) / 2,
      ((j : ℝ) + 1 / 3) * (Real.sqrt 3 / 2))
  | .down i j => ((i : ℝ) + (j : ℝ) / 2 + 1 / 2,
      ((j : ℝ) + 2 / 3) * (Real.sqrt 3 / 2))

def adjacent : Vertex → Vertex → Prop
  | .up i j, .down k l =>
      (k = i ∧ l = j - 1) ∨ (k = i ∧ l = j) ∨ (k = i - 1 ∧ l = j)
  | .down k l, .up i j =>
      (k = i ∧ l = j - 1) ∨ (k = i ∧ l = j) ∨ (k = i - 1 ∧ l = j)
  | _, _ => False

noncomputable def criticalActivity : ℝ := (2 * Real.cos (Real.pi / 8))⁻¹
noncomputable def layer (vertex : Vertex) : ℤ :=
  Vertex.rec (fun _ vertical => vertical) (fun _ vertical => vertical) vertex

structure BridgePath (h : ℕ) where
  vertices : List Vertex
  distinct : vertices.Nodup
  connected : vertices.IsChain adjacent
  source : vertices.head? = some (.up 0 0)
  terminal : ∃ i : ℤ, vertices.getLast? = some (.down i ((h : ℤ) - 1))
  inStrip : ∀ v ∈ vertices, 0 ≤ layer v ∧ layer v < (h : ℤ)

noncomputable def weight {h : ℕ} (p : BridgePath h) : ℝ :=
  criticalActivity ^ p.vertices.length

noncomputable def firstLengthWeight {h : ℕ} (p : BridgePath h) : ℝ :=
  (p.vertices.length : ℝ) * weight p

noncomputable def bridgeMass (h : ℕ) : ℝ := ∑' p : BridgePath h, weight p
noncomputable def InLogCorridor {h : ℕ} (p : BridgePath h) : Prop :=
  ∀ v ∈ p.vertices, |(position v).1| ≤ (h : ℝ) * (Real.log (h : ℝ)) ^ 2

def ConfinedBridgePath (h : ℕ) := {p : BridgePath h // InLogCorridor p}

noncomputable def confinedMass (h : ℕ) : ℝ :=
  ∑' p : ConfinedBridgePath h, weight p.val
def FiniteBridgeSums : Prop :=
  ∀ h : ℕ, 1 ≤ h →
    Summable (weight (h := h)) ∧ Summable (firstLengthWeight (h := h)) ∧
    Summable (fun p : BridgePath h => firstLengthWeight p / bridgeMass h) ∧
    Summable (fun p : ConfinedBridgePath h => weight p.val) ∧
    Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val) ∧
    Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val / confinedMass h)

open scoped BigOperators

lemma criticalActivity_pos : 0 < criticalActivity := by
  have hmem : Real.pi / 8 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have hc : 0 < Real.cos (Real.pi / 8) := Real.cos_pos_of_mem_Ioo hmem
  unfold criticalActivity
  positivity

lemma criticalActivity_lt_one : criticalActivity < 1 := by
  have h2 : Real.sqrt 2 < 2 := by
    calc Real.sqrt 2 < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 2 := by norm_num
  have h5 : 2 + Real.sqrt 2 < 4 := by linarith
  have h3 : Real.sqrt (2 + Real.sqrt 2) < 2 := by
    calc Real.sqrt (2 + Real.sqrt 2) < Real.sqrt 4 := Real.sqrt_lt_sqrt (by positivity) h5
      _ = 2 := by norm_num
  have h4 : (1 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
    have h6 : (1 : ℝ) < 2 + Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt (2 + Real.sqrt 2) := Real.sqrt_lt_sqrt (by norm_num) h6
  have hcos : Real.cos (Real.pi / 8) = Real.sqrt (2 + Real.sqrt 2) / 2 := Real.cos_pi_div_eight
  have hgt : 1 < 2 * Real.cos (Real.pi / 8) := by rw [hcos]; linarith
  unfold criticalActivity
  exact inv_lt_one_of_one_lt₀ hgt

lemma head?_ne_nil {l : List Vertex} {v : Vertex} (h : l.head? = some v) : l ≠ [] := by
  intro hnil; rw [hnil] at h; simp at h

lemma one_le_length {h : ℕ} (p : BridgePath h) : 1 ≤ p.vertices.length := by
  have hne : p.vertices ≠ [] := head?_ne_nil p.source
  have := List.length_pos_iff.mpr hne
  omega

lemma weight_nonneg {h : ℕ} (p : BridgePath h) : 0 ≤ weight p :=
  pow_nonneg (le_of_lt criticalActivity_pos) _

lemma weight_le_firstLengthWeight {h : ℕ} (p : BridgePath h) :
    weight p ≤ firstLengthWeight p := by
  have hn : (1 : ℝ) ≤ (p.vertices.length : ℝ) := by exact_mod_cast one_le_length p
  have hw : 0 ≤ weight p := weight_nonneg p
  unfold firstLengthWeight
  nlinarith

lemma summable_weight_of_summable_firstLengthWeight {h : ℕ}
    (hL : Summable (firstLengthWeight (h := h))) : Summable (weight (h := h)) :=
  Summable.of_nonneg_of_le (fun p => weight_nonneg p)
    (fun p => weight_le_firstLengthWeight p) hL

/-- The single remaining mathematical input, for each `h`: a per-length upper bound
`u n` on the number of bridge paths of length `n`, with `∑ n * u n * α ^ n` convergent.
`α = criticalActivity` is the common ratio, hence the `n * α ^ n` factor is what must be
beaten by the (super)exponential growth of `u`. -/
lemma summable_firstLengthWeight_of_profile {h : ℕ} {u : ℕ → ℝ}
    (hu : ∀ n, 0 ≤ u n)
    (hsum : Summable (fun n : ℕ => (n : ℝ) * u n * criticalActivity ^ n))
    (hcount : ∀ (n : ℕ) (s : Finset (BridgePath h)),
      (∀ p ∈ s, p.vertices.length = n) → (s.card : ℝ) ≤ u n) :
    Summable (firstLengthWeight (h := h)) := by
  have hα : 0 ≤ criticalActivity := le_of_lt criticalActivity_pos
  refine summable_of_sum_le (c := ∑' n : ℕ, (n : ℝ) * u n * criticalActivity ^ n)
    (fun p => ?_) (fun s => ?_)
  · unfold firstLengthWeight weight
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hα _)
  · set L : ℕ → ℝ := fun n => (n : ℝ) * u n * criticalActivity ^ n with hL
    have hmap : ∀ p ∈ s, p.vertices.length ∈ s.image (fun p => p.vertices.length) :=
      fun p hp => Finset.mem_image_of_mem _ hp
    rw [← Finset.sum_fiberwise_of_maps_to hmap (fun p => firstLengthWeight p)]
    have hstep : ∀ n ∈ s.image (fun p => p.vertices.length),
        ∑ p ∈ s with p.vertices.length = n, firstLengthWeight p ≤ L n := by
      intro n _
      have hcongr : ∑ p ∈ s with p.vertices.length = n, firstLengthWeight p
          = ((s.filter (fun p => p.vertices.length = n)).card : ℝ) *
              ((n : ℝ) * criticalActivity ^ n) := by
        rw [Finset.sum_congr rfl (fun p hp => ?_), Finset.sum_const, nsmul_eq_mul]
        have hpn : p.vertices.length = n := (Finset.mem_filter.mp hp).2
        simp only [firstLengthWeight, weight, hpn]
      have hfib : ∀ p ∈ s.filter (fun p => p.vertices.length = n), p.vertices.length = n :=
        fun p hp => (Finset.mem_filter.mp hp).2
      have hcard : ((s.filter (fun p => p.vertices.length = n)).card : ℝ) ≤ u n :=
        hcount n _ hfib
      have hfac : (0 : ℝ) ≤ (n : ℝ) * criticalActivity ^ n :=
        mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hα n)
      rw [hcongr]
      calc ((s.filter (fun p => p.vertices.length = n)).card : ℝ) *
              ((n : ℝ) * criticalActivity ^ n)
          ≤ u n * ((n : ℝ) * criticalActivity ^ n) := mul_le_mul_of_nonneg_right hcard hfac
        _ = L n := by simp only [hL]; ring
    refine le_trans (Finset.sum_le_sum hstep) ?_
    exact Summable.sum_le_tsum _ (fun n _ => by
      simp only [hL]
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hu n)) (pow_nonneg hα n)) hsum

lemma summable_firstLengthWeight_of_count_bound {h : ℕ} {C β : ℝ} (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hlt : β * criticalActivity < 1)
    (hcount : ∀ (n : ℕ) (s : Finset (BridgePath h)),
      (∀ p ∈ s, p.vertices.length = n) → (s.card : ℝ) ≤ C * β ^ n) :
    Summable (firstLengthWeight (h := h)) := by
  have hb : ‖β * criticalActivity‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hβ (le_of_lt criticalActivity_pos))]
    exact hlt
  have hgeom : Summable (fun n : ℕ => (n : ℝ) * (C * β ^ n) * criticalActivity ^ n) := by
    have h1 : Summable (fun n : ℕ => C * ((n : ℝ) ^ 1 * (β * criticalActivity) ^ n)) :=
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hb).mul_left C
    refine h1.congr fun n => ?_
    rw [pow_one, mul_pow]; ring
  exact summable_firstLengthWeight_of_profile (fun n => mul_nonneg hC (pow_nonneg hβ n)) hgeom hcount

lemma finite_bridge_sums_of_firstLengthWeight
    (hL : ∀ h : ℕ, 1 ≤ h → Summable (firstLengthWeight (h := h))) : FiniteBridgeSums := by
  intro h hh
  have hw : Summable (weight (h := h)) := summable_weight_of_summable_firstLengthWeight (hL h hh)
  have hc : Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val) :=
    (hL h hh).subtype (fun p : BridgePath h => InLogCorridor p)
  exact ⟨hw, hL h hh, (hL h hh).div_const (bridgeMass h),
    hw.subtype (fun p : BridgePath h => InLogCorridor p), hc, hc.div_const (confinedMass h)⟩

/-- Frozen sub-contract for the hard part: for every `h ≥ 1`, the number of length-`n`
bridge paths grows geometrically with a base strictly below `1 / criticalActivity`.
Note `β` may depend on `h`; no uniform `β` can work (see RESEARCH.md). -/
def StripCountBound : Prop :=
  ∀ h : ℕ, 1 ≤ h → ∃ C β : ℝ, 0 ≤ C ∧ 0 ≤ β ∧ β * criticalActivity < 1 ∧
    ∀ (n : ℕ) (s : Finset (BridgePath h)),
      (∀ p ∈ s, p.vertices.length = n) → (s.card : ℝ) ≤ (C : ℝ) * β ^ n

lemma finite_bridge_sums_of_stripCountBound (H : StripCountBound) : FiniteBridgeSums := by
  refine finite_bridge_sums_of_firstLengthWeight fun h hh => ?_
  obtain ⟨C, β, hC, hβ, hlt, hcount⟩ := H h hh
  exact summable_firstLengthWeight_of_count_bound hC hβ hlt hcount

def examplePath2 : BridgePath 2 where
  vertices := [.up 0 0, .down 0 0, .up 0 1, .down 0 1]
  distinct := by decide
  connected := by
    refine List.IsChain.cons_cons ?_ (List.IsChain.cons_cons ?_ (List.IsChain.cons_cons ?_ (List.IsChain.singleton _)))
    · simp [adjacent]
    · simp [adjacent]
    · simp [adjacent]
  source := rfl
  terminal := ⟨0, rfl⟩
  inStrip := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> decide

lemma cos_pi_div_eight_pos : 0 < Real.cos (Real.pi / 8) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [Real.pi_pos]

lemma criticalActivity_mul_mu : criticalActivity * (2 * Real.cos (Real.pi / 8)) = 1 := by
  have hc := cos_pi_div_eight_pos
  have hne : Real.cos (Real.pi / 8) ≠ 0 := ne_of_gt hc
  unfold criticalActivity
  field_simp

lemma inv_mul_cancel' : criticalActivity = (2 * Real.cos (Real.pi / 8))⁻¹ := rfl

lemma two_mul_criticalActivity_gt_one : 1 < 2 * criticalActivity := by
  have hc := cos_pi_div_eight_pos
  have hm := criticalActivity_mul_mu
  have hmu : 0 < 2 * Real.cos (Real.pi / 8) := by linarith
  rw [inv_mul_cancel'] at hm
  -- criticalActivity = 1/(2c); 2 * criticalActivity = 2/(2c) = 1/c > 1 since c < 1
  have hclt : Real.cos (Real.pi / 8) < 1 := by
    have h := Real.cos_pi_div_eight
    have hs : Real.sqrt (2 + Real.sqrt 2) < 2 := by
      have h2 : Real.sqrt 2 < 2 := by
        calc Real.sqrt 2 < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
          _ = 2 := by norm_num
      calc Real.sqrt (2 + Real.sqrt 2) < Real.sqrt 4 :=
            Real.sqrt_lt_sqrt (by positivity) (by linarith)
        _ = 2 := by norm_num
    rw [h]; linarith
  rw [inv_mul_cancel']
  have hne : Real.cos (Real.pi / 8) ≠ 0 := ne_of_gt hc
  have : (2 : ℝ) * (2 * Real.cos (Real.pi / 8))⁻¹ = (Real.cos (Real.pi / 8))⁻¹ := by
    field_simp
  rw [this]
  exact (one_lt_inv_iff₀).mpr ⟨hc, hclt⟩

lemma criticalActivity_sq : criticalActivity ^ 2 = (2 + Real.sqrt 2)⁻¹ := by
  have hcos : Real.cos (Real.pi / 8) = Real.sqrt (2 + Real.sqrt 2) / 2 := Real.cos_pi_div_eight
  have hpos : 0 < 2 + Real.sqrt 2 := by
    have := Real.sqrt_nonneg 2; linarith
  have hsq : Real.sqrt (2 + Real.sqrt 2) ^ 2 = 2 + Real.sqrt 2 := Real.sq_sqrt (le_of_lt hpos)
  unfold criticalActivity
  rw [hcos]
  have hsimp : 2 * (Real.sqrt (2 + Real.sqrt 2) / 2) = Real.sqrt (2 + Real.sqrt 2) := by ring
  rw [hsimp, inv_pow, hsq]


/-! ### Growth-rate form of the missing counting input and its conversion -/

/-- **Natural form of the missing combinatorial input.**  The number of length-`n` bridge
paths in the width-`h` strip grows geometrically with a base strictly below the honeycomb
connective constant `2 cos (π/8) = √(2+√2)`.  Both `C` and `β` may depend on `h`
(no uniform `β` can work, since the strip connective constants increase to `μ_hex`). -/
def StripGrowthBelowMu : Prop :=
  ∀ h : ℕ, 1 ≤ h → ∃ C β : ℝ, 0 ≤ C ∧ 0 ≤ β ∧
    β < 2 * Real.cos (Real.pi / 8) ∧
    ∀ (n : ℕ) (s : Finset (BridgePath h)),
      (∀ p ∈ s, p.vertices.length = n) → (s.card : ℝ) ≤ C * β ^ n

lemma stripCountBound_of_stripGrowthBelowMu (H : StripGrowthBelowMu) : StripCountBound := by
  intro h hh
  obtain ⟨C, β, hC, hβ, hlt, hcount⟩ := H h hh
  refine ⟨C, β, hC, hβ, ?_, hcount⟩
  calc β * criticalActivity
      < (2 * Real.cos (Real.pi / 8)) * criticalActivity :=
        mul_lt_mul_of_pos_right hlt criticalActivity_pos
    _ = 1 := by rw [mul_comm]; exact criticalActivity_mul_mu

theorem finite_bridge_sums_of_stripGrowthBelowMu (H : StripGrowthBelowMu) :
    FiniteBridgeSums :=
  finite_bridge_sums_of_stripCountBound (stripCountBound_of_stripGrowthBelowMu H)



/-! ### Direct-application corollaries -/

/-- If the width-`h` strip counting base is below `μ_hex = 2cos(π/8)` together with
`StripCountBound`'s shape, `firstLengthWeight` is summable. -/
lemma summable_firstLengthWeight_of_growth_below_mu {h : ℕ} {C β : ℝ}
    (hC : 0 ≤ C) (hβ : 0 ≤ β) (hlt : β < 2 * Real.cos (Real.pi / 8))
    (hcount : ∀ (n : ℕ) (s : Finset (BridgePath h)),
      (∀ p ∈ s, p.vertices.length = n) → (s.card : ℝ) ≤ C * β ^ n) :
    Summable (firstLengthWeight (h := h)) := by
  refine summable_firstLengthWeight_of_count_bound hC hβ ?_ hcount
  calc β * criticalActivity
      < (2 * Real.cos (Real.pi / 8)) * criticalActivity :=
        mul_lt_mul_of_pos_right hlt criticalActivity_pos
    _ = 1 := by rw [mul_comm]; exact criticalActivity_mul_mu


open scoped BigOperators

/-- Position of a vertex along the infinite direction of the strip.  In the brick-wall picture
the strip has one vertex per layer in each "column" `hexX = c`. -/
def hexX : Vertex → ℤ
  | .up i j => 2 * i + j
  | .down i j => 2 * i + j + 1

/-- `(hexX, layer)` is injective, so the frozen vertex type *is* the brick-wall strip. -/
lemma eq_of_hexX_layer {v w : Vertex} (hX : hexX v = hexX w) (hj : layer v = layer w) :
    v = w := by
  cases v with
  | up i j =>
    cases w with
    | up i' j' =>
      simp only [hexX, layer] at hX hj
      subst hj
      have : i = i' := by omega
      subst this; rfl
    | down i' j' =>
      simp only [hexX, layer] at hX hj
      omega
  | down i j =>
    cases w with
    | up i' j' =>
      simp only [hexX, layer] at hX hj
      omega
    | down i' j' =>
      simp only [hexX, layer] at hX hj
      subst hj
      have : i = i' := by omega
      subst this; rfl

/-- A step between two vertices of the *same* layer moves `hexX` by exactly `±1`. -/
lemma hexX_step {a b : Vertex} (hl : layer a = layer b) (hab : adjacent a b) :
    hexX b = hexX a + 1 ∨ hexX b = hexX a - 1 := by
  cases a with
  | up i j => cases b with
    | up _ _ => simp [adjacent] at hab
    | down k l =>
      simp only [adjacent] at hab
      have hl' : j = l := hl
      simp only [hexX]
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  | down k l => cases b with
    | down _ _ => simp [adjacent] at hab
    | up i j =>
      simp only [adjacent] at hab
      have hl' : l = j := hl
      simp only [hexX]
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

lemma hexX_up_zero : hexX (.up 0 0) = 0 := rfl

lemma head?_eq_getElem?_zero {α : Type*} (l : List α) : l.head? = l[0]? := by
  cases l <;> rfl

lemma ne_nil_of_vertices_nonempty {h : ℕ} (p : BridgePath h) : p.vertices ≠ [] := by
  intro hnil
  have hsrc := p.source
  rw [hnil] at hsrc
  simp at hsrc

open scoped BigOperators

/-- **The frozen adjacency is exactly the brick-wall (hexagonal) strip.**  In the coordinates
`(hexX, layer)` every edge is either *horizontal* (same layer, `hexX` moves by `±1`) or
*vertical* (same `hexX`, layer moves by `±1`). -/
lemma step_dichotomy {a b : Vertex} (hab : adjacent a b) :
    (layer a = layer b ∧ (hexX b = hexX a + 1 ∨ hexX b = hexX a - 1)) ∨
    (hexX a = hexX b ∧ (layer b = layer a + 1 ∨ layer b = layer a - 1)) := by
  cases a with
  | up i j =>
    cases b with
    | up _ _ => simp [adjacent] at hab
    | down k l =>
      simp only [adjacent] at hab
      rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right
        refine ⟨?_, ?_⟩
        · simp only [hexX]; omega
        · simp only [layer]; omega
      · left
        refine ⟨?_, ?_⟩
        · simp only [layer]; omega
        · simp only [hexX]; omega
      · left
        refine ⟨?_, ?_⟩
        · simp only [layer]; omega
        · simp only [hexX]; omega
  | down k l =>
    cases b with
    | down _ _ => simp [adjacent] at hab
    | up i j =>
      simp only [adjacent] at hab
      rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right
        refine ⟨?_, ?_⟩
        · simp only [hexX]; omega
        · simp only [layer]; omega
      · left
        refine ⟨?_, ?_⟩
        · simp only [layer]; omega
        · simp only [hexX]; omega
      · left
        refine ⟨?_, ?_⟩
        · simp only [layer]; omega
        · simp only [hexX]; omega


/-- **Integer walk core lemma.** A finite injective walk on `ℤ` with steps `±1` is monotone:
it goes straight in one direction. This is the combinatorial fact that makes the width-one
strip a single line. -/
lemma int_walk_monotone {n : ℕ} {f : ℕ → ℤ}
    (hinj : ∀ i j, i < n → j < n → f i = f j → i = j)
    (hstep : ∀ i, i + 1 < n → f (i + 1) = f i + 1 ∨ f (i + 1) = f i - 1) :
    (∀ i, i < n → f i = f 0 + (i : ℤ)) ∨ (∀ i, i < n → f i = f 0 - (i : ℤ)) := by
  have no_flip : ∀ k, k + 2 < n → ¬(f (k+1) = f k + 1 ∧ f (k+2) = f (k+1) - 1) ∧
      ¬(f (k+1) = f k - 1 ∧ f (k+2) = f (k+1) + 1) := by
    intro k hk
    constructor
    · rintro ⟨h1, h2⟩
      have hval : f (k+2) = f k := by rw [h2, h1]; ring
      exact absurd (hinj (k+2) k (by omega) (by omega) hval) (by omega)
    · rintro ⟨h1, h2⟩
      have hval : f (k+2) = f k := by rw [h2, h1]; ring
      exact absurd (hinj (k+2) k (by omega) (by omega) hval) (by omega)
  rcases Nat.lt_or_ge n 2 with hn | hn
  · left
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0; simp
  · rcases hstep 0 (by omega) with hplus | hminus
    · left
      have allplus : ∀ j, j + 1 < n → f (j+1) = f j + 1 := by
        intro j
        induction j with
        | zero => intro _; exact hplus
        | succ k ihk =>
          intro hjk
          have hprev : f (k+1) = f k + 1 := ihk (by omega)
          rcases hstep (k+1) hjk with h | h
          · exact h
          · exact absurd ⟨hprev, h⟩ (no_flip k (by omega)).1
      intro i
      induction i using Nat.strong_induction_on with
      | _ i ih =>
        intro hi
        match i with
        | 0 => simp
        | k + 1 =>
          have hk : f (k+1) = f k + 1 := allplus k (by omega)
          have hk' : f k = f 0 + (k : ℤ) := ih k (by omega) (by omega)
          rw [hk, hk']
          push_cast
          ring
    · right
      have allminus : ∀ j, j + 1 < n → f (j+1) = f j - 1 := by
        intro j
        induction j with
        | zero => intro _; exact hminus
        | succ k ihk =>
          intro hjk
          have hprev : f (k+1) = f k - 1 := ihk (by omega)
          rcases hstep (k+1) hjk with h | h
          · exact absurd ⟨hprev, h⟩ (no_flip k (by omega)).2
          · exact h
      intro i
      induction i using Nat.strong_induction_on with
      | _ i ih =>
        intro hi
        match i with
        | 0 => simp
        | k + 1 =>
          have hk : f (k+1) = f k - 1 := allminus k (by omega)
          have hk' : f k = f 0 - (k : ℤ) := ih k (by omega) (by omega)
          rw [hk, hk']
          push_cast
          ring

open scoped BigOperators

/-- For a chain of adjacent vertices all on layer `0`, the `hexX` coordinates form an
injective `±1` walk. -/
lemma chain_hexX_walk {l : List Vertex}
    (hchain : l.IsChain adjacent) (hnd : l.Nodup)
    (hlay : ∀ v ∈ l, layer v = 0) :
    (∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length),
        hexX (l[i]'hi) = hexX (l[j]'hj) → i = j) ∧
    (∀ (i : ℕ) (hi : i + 1 < l.length),
        hexX (l[i+1]'hi) = hexX (l[i]'(by omega)) + 1 ∨
        hexX (l[i+1]'hi) = hexX (l[i]'(by omega)) - 1) := by
  constructor
  · intro i j hi hj hX
    have hli : layer (l[i]'hi) = 0 := hlay _ (List.getElem_mem (l := l) hi)
    have hlj : layer (l[j]'hj) = 0 := hlay _ (List.getElem_mem (l := l) hj)
    have hveq : l[i]'hi = l[j]'hj := eq_of_hexX_layer hX (by rw [hli, hlj])
    by_contra hne
    exact absurd hveq (fun h => hne ((hnd.getElem_inj (hi := hi) (hj := hj)).mp h))
  · intro i hi
    have h1 : adjacent (l[i]'(by omega)) (l[i+1]'hi) := hchain.getElem i hi
    have hl1 : layer (l[i]'(by omega)) = 0 := hlay _ (List.getElem_mem (l := l) (by omega))
    have hl2 : layer (l[i+1]'hi) = 0 := hlay _ (List.getElem_mem (l := l) (by omega))
    exact hexX_step (by rw [hl1, hl2]) h1

open scoped BigOperators

lemma BridgePath.ext_vertices {h : ℕ} {p q : BridgePath h} (hv : p.vertices = q.vertices) :
    p = q := by
  cases p with
  | mk vp dp cp sp tp ip =>
    cases q with
    | mk vq dq cq sq tq iq =>
      simp only at hv
      subst hv
      congr 1

lemma layer_eq_zero_of_bridge1 {p : BridgePath 1} (v : Vertex) (hv : v ∈ p.vertices) :
    layer v = 0 := by
  have h := p.inStrip v hv
  have h1 : layer v < ((1 : ℕ) : ℤ) := h.2
  have h2 : 0 ≤ layer v := h.1
  omega

lemma length_pos_of_bridge {h : ℕ} (p : BridgePath h) : 0 < p.vertices.length :=
  List.length_pos_iff.mpr (ne_nil_of_vertices_nonempty p)

noncomputable def bridge1CoordFun (p : BridgePath 1) : ℕ → ℤ :=
  fun i => hexX (p.vertices.getD i (.up 0 0))

lemma bridge1CoordFun_eq (p : BridgePath 1) {i : ℕ} (hi : i < p.vertices.length) :
    bridge1CoordFun p i = hexX (p.vertices[i]'hi) := by
  unfold bridge1CoordFun
  rw [List.getD_eq_getElem]

lemma bridge1_start (p : BridgePath 1) {h : 0 < p.vertices.length} :
    hexX (p.vertices[0]'h) = 0 := by
  have hsrc : p.vertices[0]? = some (.up 0 0) := by
    rw [← head?_eq_getElem?_zero]; exact p.source
  have e1 : p.vertices[0]? = some (p.vertices[0]'h) := List.getElem?_eq_getElem h
  rw [e1] at hsrc
  have hv : p.vertices[0]'h = .up 0 0 := Option.some.inj hsrc
  rw [hv]; exact hexX_up_zero

/-- The `hexX` coordinate of a width-one bridge path is affine: `+i` or `-i`. -/
lemma bridge1_hexX (p : BridgePath 1) :
    (∀ (i : ℕ) (_hi : i < p.vertices.length), bridge1CoordFun p i = (i : ℤ)) ∨
    (∀ (i : ℕ) (_hi : i < p.vertices.length), bridge1CoordFun p i = -(i : ℤ)) := by
  have hlen : 0 < p.vertices.length := length_pos_of_bridge p
  obtain ⟨hinj, hstep⟩ :=
    chain_hexX_walk p.connected p.distinct (fun v hv => layer_eq_zero_of_bridge1 v hv)
  have hinj' : ∀ i j, i < p.vertices.length → j < p.vertices.length →
      bridge1CoordFun p i = bridge1CoordFun p j → i = j := by
    intro i j hi hj hf
    rw [bridge1CoordFun_eq p hi, bridge1CoordFun_eq p hj] at hf
    exact hinj i j hi hj hf
  have hstep' : ∀ i, i + 1 < p.vertices.length →
      bridge1CoordFun p (i+1) = bridge1CoordFun p i + 1 ∨
      bridge1CoordFun p (i+1) = bridge1CoordFun p i - 1 := by
    intro i hi
    rw [bridge1CoordFun_eq p hi, bridge1CoordFun_eq p (by omega)]
    exact hstep i hi
  have hc0 : bridge1CoordFun p 0 = 0 := by
    rw [bridge1CoordFun_eq p hlen]; exact bridge1_start p
  obtain hm | hm := int_walk_monotone (n := p.vertices.length) hinj' hstep'
  · left
    intro i hi
    have h := hm i hi
    rw [hc0] at h
    simpa using h
  · right
    intro i hi
    have h := hm i hi
    rw [hc0] at h
    simpa using h

/-- A width-one bridge path has at least two vertices (`up 0 0` is not `down i 0`). -/
lemma bridge1_length_ge_two (p : BridgePath 1) : 2 ≤ p.vertices.length := by
  have hpos := length_pos_of_bridge p
  obtain ⟨i, hi⟩ := p.terminal
  rcases Nat.lt_or_ge p.vertices.length 2 with h | h
  · have hlen1 : p.vertices.length = 1 := by omega
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen1
    have hhead : p.vertices.head? = some a := by rw [ha]; rfl
    rw [p.source] at hhead
    have hav : a = Vertex.up 0 0 := Option.some.inj hhead.symm
    have hlast : p.vertices.getLast? = some a := by rw [ha]; rfl
    rw [hi] at hlast
    have hcontra : Vertex.down i (((1 : ℕ) : ℤ) - 1) = Vertex.up 0 0 := by
      have hd : Vertex.down i (((1 : ℕ) : ℤ) - 1) = a := Option.some.inj hlast
      rw [hd, hav]
    exact absurd hcontra (by simp)
  · exact h

/-- The second `hexX` coordinate of a width-one bridge path is `±1`. -/
lemma bridge1_second (p : BridgePath 1) :
    bridge1CoordFun p 1 = 1 ∨ bridge1CoordFun p 1 = -1 := by
  have h2 := bridge1_length_ge_two p
  rcases bridge1_hexX p with hp | hp
  · left; have := hp 1 (by omega); simpa using this
  · right; have := hp 1 (by omega); simpa using this

/-- **Determination by length and second coordinate.** -/
lemma bridge1_det {p q : BridgePath 1}
    (hlen : p.vertices.length = q.vertices.length)
    (hsecond : bridge1CoordFun p 1 = bridge1CoordFun q 1) :
    p.vertices = q.vertices := by
  have h2q : 2 ≤ q.vertices.length := by have := bridge1_length_ge_two q; omega
  have hlen' : 2 ≤ p.vertices.length := bridge1_length_ge_two p
  have sign : ∀ i, i < p.vertices.length → bridge1CoordFun p i = bridge1CoordFun q i := by
    intro i hi
    rcases bridge1_hexX p with hp | hp <;> rcases bridge1_hexX q with hq | hq
    · rw [hp i hi, hq i (by omega)]
    · exfalso
      have h1 := hp 1 (by omega)
      have h2' := hq 1 (by omega)
      rw [h1, h2'] at hsecond
      omega
    · exfalso
      have h1 := hp 1 (by omega)
      have h2' := hq 1 (by omega)
      rw [h1, h2'] at hsecond
      omega
    · rw [hp i hi, hq i (by omega)]
  refine List.ext_getElem hlen ?_
  intro i hi hiq
  have hlp : layer (p.vertices[i]'hi) = 0 :=
    layer_eq_zero_of_bridge1 _ (List.getElem_mem (l := p.vertices) hi)
  have hlq : layer (q.vertices[i]'hiq) = 0 :=
    layer_eq_zero_of_bridge1 _ (List.getElem_mem (l := q.vertices) hiq)
  refine eq_of_hexX_layer ?_ (by rw [hlp, hlq])
  rw [← bridge1CoordFun_eq p hi, ← bridge1CoordFun_eq q hiq]
  exact sign i hi

/-- **Width-one counting bound**: at most two bridge paths of any prescribed length. -/
theorem bridge1_card_le_two (n : ℕ) (s : Finset (BridgePath 1))
    (hlen : ∀ p ∈ s, p.vertices.length = n) : s.card ≤ 2 := by
  have hinj : Set.InjOn (fun p : BridgePath 1 => bridge1CoordFun p 1) (s : Set (BridgePath 1)) := by
    intro p hp q hq heq
    have hpn : p.vertices.length = n := hlen p hp
    have hqn : q.vertices.length = n := hlen q hq
    exact BridgePath.ext_vertices (bridge1_det (by omega) heq)
  have hmaps : Set.MapsTo (fun p : BridgePath 1 => bridge1CoordFun p 1) (s : Set (BridgePath 1))
      ({-1, 1} : Finset ℤ) := by
    intro p _
    rcases bridge1_second p with h | h <;> simp [h]
  calc s.card ≤ ({-1, 1} : Finset ℤ).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ 2 := Finset.card_le_two

/-- **Width-one instance of the missing strip-growth estimate.**  This is the `h = 1` case of
`StripGrowthBelowMu`, fully proved: `C = 2`, `β = 1`, and `1 < 2 cos (π/8)`. -/
theorem stripGrowthAtOne :
    ∃ C β : ℝ, 0 ≤ C ∧ 0 ≤ β ∧ β < 2 * Real.cos (Real.pi / 8) ∧
      ∀ (n : ℕ) (s : Finset (BridgePath 1)),
        (∀ p ∈ s, p.vertices.length = n) → (s.card : ℝ) ≤ C * β ^ n := by
  refine ⟨2, 1, by norm_num, by norm_num, ?_, ?_⟩
  · have hpos : 0 < Real.cos (Real.pi / 8) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [Real.pi_pos]
    have h2 : Real.sqrt 2 < 2 := by
      calc Real.sqrt 2 < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
        _ = 2 := by norm_num
    have hle : Real.sqrt (2 + Real.sqrt 2) < 2 := by
      calc Real.sqrt (2 + Real.sqrt 2) < Real.sqrt 4 :=
            Real.sqrt_lt_sqrt (by positivity) (by linarith)
        _ = 2 := by norm_num
    have hgt : 1 < Real.sqrt (2 + Real.sqrt 2) := by
      have h1 : (1 : ℝ) < 2 + Real.sqrt 2 := by
        have := Real.sqrt_nonneg 2; linarith
      calc (1 : ℝ) = Real.sqrt 1 := by simp
        _ < Real.sqrt (2 + Real.sqrt 2) := Real.sqrt_lt_sqrt (by norm_num) h1
    rw [Real.cos_pi_div_eight]
    linarith
  · intro n s hs
    have hcard : s.card ≤ 2 := bridge1_card_le_two n s hs
    have hcast : ((s.card : ℝ)) ≤ 2 := by exact_mod_cast hcard
    simpa using hcast



open scoped BigOperators

/-- **The `h = 1` case of the six `FiniteBridgeSums` conjuncts**, fully proved.
This is the part of the acceptance target that is discharged unconditionally. -/
theorem finite_bridge_sums_at_one :
    Summable (weight (h := 1)) ∧ Summable (firstLengthWeight (h := 1)) ∧
    Summable (fun p : BridgePath 1 => firstLengthWeight p / bridgeMass 1) ∧
    Summable (fun p : ConfinedBridgePath 1 => weight p.val) ∧
    Summable (fun p : ConfinedBridgePath 1 => firstLengthWeight p.val) ∧
    Summable (fun p : ConfinedBridgePath 1 => firstLengthWeight p.val / confinedMass 1) := by
  have hcount : ∀ (n : ℕ) (s : Finset (BridgePath 1)),
      (∀ p ∈ s, p.vertices.length = n) → (s.card : ℝ) ≤ (2 : ℝ) * (1 : ℝ) ^ n := by
    intro n s hs
    have h := bridge1_card_le_two n s hs
    have h2 : ((s.card : ℝ)) ≤ 2 := by exact_mod_cast h
    simpa using h2
  have hL : Summable (firstLengthWeight (h := 1)) :=
    summable_firstLengthWeight_of_count_bound (by norm_num) (by norm_num)
      (by simpa using criticalActivity_lt_one) hcount
  have hw : Summable (weight (h := 1)) := summable_weight_of_summable_firstLengthWeight hL
  have hc : Summable (fun p : ConfinedBridgePath 1 => firstLengthWeight p.val) :=
    hL.subtype (fun p : BridgePath 1 => InLogCorridor p)
  exact ⟨hw, hL, hL.div_const (bridgeMass 1), hw.subtype _,
    hc, hc.div_const (confinedMass 1)⟩



open scoped BigOperators

/-- `BridgePath` has decidable equality: two bridge paths are equal iff their vertex lists
are equal (all other fields are propositions). -/
instance bridgePathDecidableEq (h : ℕ) : DecidableEq (BridgePath h) :=
  fun p q => decidable_of_iff (p.vertices = q.vertices)
    ⟨fun hv => by cases p; cases q; simp_all,
     fun he => congrArg BridgePath.vertices he⟩

/-- The two upward steps used to extend a width-`h` bridge path to width `h+1`. -/
lemma adjacent_down_up_climb {h : ℕ} (i : ℤ) :
    adjacent (.down i ((h : ℤ) - 1)) (.up i (h : ℤ)) := by
  simp [adjacent]

lemma adjacent_up_down_same {h : ℕ} (i : ℤ) :
    adjacent (.up i (h : ℤ)) (.down i (h : ℤ)) := by
  simp [adjacent]

/-- Appending `up i h, down i h` above the terminal vertex of a width-`h` bridge path gives
a width-`(h+1)` bridge path. -/
lemma exists_path_succ_with {h : ℕ} (p : BridgePath h) (i : ℤ)
    (hi : p.vertices.getLast? = some (.down i ((h : ℤ) - 1))) :
    ∃ q : BridgePath (h + 1),
      q.vertices = p.vertices ++ [.up i (h : ℤ), .down i (h : ℤ)] := by
  have hpne : p.vertices ≠ [] := by
    intro hnil
    have := p.source
    rw [hnil] at this
    exact absurd this (by simp)
  refine ⟨{
    vertices := p.vertices ++ [.up i (h : ℤ), .down i (h : ℤ)]
    distinct := ?_
    connected := ?_
    source := ?_
    terminal := ?_
    inStrip := ?_ }, rfl⟩
  · rw [List.nodup_append]
    refine ⟨p.distinct, by simp, ?_⟩
    intro a ha b hb hab
    have hla := (p.inStrip a ha).2
    have hlb : layer b = (h : ℤ) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> simp [layer]
    have : layer a = layer b := by rw [hab]
    omega
  · refine List.IsChain.append p.connected ?_ ?_
    · refine List.IsChain.cons_cons (adjacent_up_down_same (h := h) i) ?_
      exact List.IsChain.singleton _
    · intro x hx y hy
      rw [hi] at hx
      simp only [Option.mem_some_iff] at hx
      subst hx
      simp only [List.head?_cons, Option.mem_some_iff] at hy
      subst hy
      exact adjacent_down_up_climb (h := h) i
  · simp only [List.head?_append]
    rw [p.source]
    simp
  · refine ⟨i, ?_⟩
    rw [List.getLast?_append_of_ne_nil _ (by simp : ([Vertex.up i (h : ℤ), Vertex.down i (h : ℤ)] : List Vertex) ≠ [])]
    simp
  · intro v hv
    rw [List.mem_append] at hv
    rcases hv with hv | hv
    · have := p.inStrip v hv
      refine ⟨this.1, ?_⟩
      push_cast
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl <;>
        (simp only [layer]; constructor <;> omega)

/-- The canonical width-`(h+1)` extension of a width-`h` bridge path. -/
noncomputable def bridgePathSucc {h : ℕ} (p : BridgePath h) : BridgePath (h + 1) :=
  Classical.choose (exists_path_succ_with p (Classical.choose p.terminal)
    (Classical.choose_spec p.terminal))

lemma bridgePathSucc_vertices {h : ℕ} (p : BridgePath h) :
    (bridgePathSucc p).vertices =
      p.vertices ++ [.up (Classical.choose p.terminal) (h : ℤ),
        .down (Classical.choose p.terminal) (h : ℤ)] :=
  Classical.choose_spec (exists_path_succ_with p (Classical.choose p.terminal)
    (Classical.choose_spec p.terminal))

lemma bridgePathSucc_length {h : ℕ} (p : BridgePath h) :
    (bridgePathSucc p).vertices.length = p.vertices.length + 2 := by
  rw [bridgePathSucc_vertices]
  simp

lemma bridgePathSucc_injective {h : ℕ} : Function.Injective (@bridgePathSucc h) := by
  intro p q heq
  have hv : (bridgePathSucc p).vertices = (bridgePathSucc q).vertices :=
    congrArg (fun r : BridgePath (h + 1) => r.vertices) heq
  rw [bridgePathSucc_vertices, bridgePathSucc_vertices] at hv
  have hlen : p.vertices.length = q.vertices.length := by
    have := congrArg List.length hv
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    omega
  have htake := congrArg (List.take p.vertices.length) hv
  rw [List.take_append_of_le_length (le_refl p.vertices.length),
      List.take_append_of_le_length (by omega)] at htake
  have htake2 : List.take p.vertices.length q.vertices = q.vertices :=
    List.take_of_length_le (by omega)
  rw [List.take_length, htake2] at htake
  exact BridgePath.ext_vertices htake

/-- **Width monotonicity for fixed lengths.**  Length-`n` bridge paths of width `h` inject
into length-`(n+2)` bridge paths of width `h+1`, so the width-`h` counting sequence dominates
the width-`(h-1)` one at shifted lengths.  (The naive inclusion `BridgePath h ⊆ BridgePath
(h+1)` is *false*: the terminal layer changes with `h`.) -/
theorem card_le_card_width_succ {h n : ℕ} (s : Finset (BridgePath h))
    (hs : ∀ p ∈ s, p.vertices.length = n) :
    ∃ t : Finset (BridgePath (h + 1)),
      (∀ q ∈ t, q.vertices.length = n + 2) ∧ s.card = t.card := by
  set emb : BridgePath h ↪ BridgePath (h + 1) :=
    ⟨@bridgePathSucc h, bridgePathSucc_injective⟩ with hemb
  refine ⟨s.map emb, ?_, (Finset.card_map emb).symm⟩
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hq
  exact (bridgePathSucc_length p).trans (by rw [hs p hp])



open scoped BigOperators

/-- **The missing estimate is only needed for widths `h ≥ 2`.**  Width `1` is fully proved
(`stripGrowthAtOne`), so the hypothesis of the reduction can be weakened by one case. -/
theorem stripGrowthBelowMu_of_ge_two
    (H : ∀ h : ℕ, 2 ≤ h → ∃ C β : ℝ, 0 ≤ C ∧ 0 ≤ β ∧
      β < 2 * Real.cos (Real.pi / 8) ∧
      ∀ (n : ℕ) (s : Finset (BridgePath h)),
        (∀ p ∈ s, p.vertices.length = n) → (s.card : ℝ) ≤ C * β ^ n) :
    StripGrowthBelowMu := by
  intro h hh
  rcases Nat.lt_or_ge h 2 with hlt | hge
  · have h1 : h = 1 := by omega
    subst h1
    exact stripGrowthAtOne
  · exact H h hge

/-- **Strengthened consumer reduction.**  `FiniteBridgeSums` follows from the strip growth
estimate only for `h ≥ 2`; the `h = 1` case is discharged unconditionally. -/
theorem finite_bridge_sums_of_stripGrowth_ge_two
    (H : ∀ h : ℕ, 2 ≤ h → ∃ C β : ℝ, 0 ≤ C ∧ 0 ≤ β ∧
      β < 2 * Real.cos (Real.pi / 8) ∧
      ∀ (n : ℕ) (s : Finset (BridgePath h)),
        (∀ p ∈ s, p.vertices.length = n) → (s.card : ℝ) ≤ C * β ^ n) :
    FiniteBridgeSums :=
  finite_bridge_sums_of_stripGrowthBelowMu (stripGrowthBelowMu_of_ge_two H)


end PolynomialVacuumBridge.Corridor

end OAI
```
