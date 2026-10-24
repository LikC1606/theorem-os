# RESEARCH.md — HoneycombBridgeFiniteness (worktree-3)

## Current status

- Assigned task: `sums_reduction` (digest `9dc59a25560dac27093dfb2f02a3aeb453e87ebd4a7945f3082d23436f3a5872`).
- Assigned declaration `OAI.PolynomialVacuumBridge.Corridor.finite_bridge_sums_of_stripGrowthBelowMu`
  is **proved and saved** with exactly the requested conditional type. This is the
  algebra/Finset-grouping glue; it is **not** a proof of the original unconditional target.
- Original target `OAI.PolynomialVacuumBridge.Corridor.finite_bridge_sums : FiniteBridgeSums`
  remains unproved in `generated/problem/Submission.lean` (the seed `sorry` is preserved at line 195).
- Conclusion for the original target: **inconclusive / blocked on the unconditional strip
  growth estimate**. The conditional reduction alone cannot close it.

Consumer for the remaining gap: task `initial_goal_1`, digest
`ab8c91c92c1d5d985ed03edfaee27bbef6df38455b84a82711d07d8d13e77890`.

Saved Lean file: `generated/problem/Submission.lean`
- 199 lines, 8813 bytes, sha256 `6f81ffc481e22c8a189ced1d0de1d154c39e0edc57f17e9c1f492a271139f6e2`.
- The original header/declarations before `FiniteBridgeSums` are byte-identical to the seed;
  only new `bridge…`-prefixed helpers were inserted before the original theorem position.
- No `sorry`, `admit`, `native_decide`, `unsafe` or new `axiom` occurs in the added proof text;
  the only `sorry` is the untouched original `finite_bridge_sums` body.

## Exact argument now checked in Lean

With `α = criticalActivity = (2 cos (π/8))⁻¹`, `μ = 2 cos (π/8)`:

1. `bridgeCriticalActivity_pos : 0 < α` and
   `bridgeCriticalActivity_mul_mu : α * μ = 1`.
2. Every bridge path has positive length (`bridgeOne_le_length`), so
   `0 ≤ weight p ≤ firstLengthWeight p`
   (`bridgeWeight_nonneg`, `bridgeWeight_le_firstLengthWeight`), hence
   `bridgeSummable_weight_of_summable_firstLengthWeight`.
3. `bridgeSummable_firstLengthWeight_of_profile`: for any per-length bound
   `u : ℕ → ℝ`, if every finite set of length-`n` paths has cardinality at most `u n`,
   then `∑ p, firstLengthWeight p` is bounded by the profile series
   `∑ n, n * u n * α^n`. The proof groups a finite set by `vertices.length`
   (`Finset.sum_fiberwise_of_maps_to`), bounds each fibre using the constant weight `α^n`,
   and applies `summable_of_sum_le`.
4. `bridgeSummable_firstLengthWeight_of_mu_bound`: if
   `0 ≤ C`, `0 ≤ β`, `β < μ`, and `card(s) ≤ C β^n` for all length-`n` fibres, then
   `β * α < μ * α = 1`; `summable_pow_mul_geometric_of_norm_lt_one` gives summability of
   `n * (C β^n) * α^n`, and step 3 gives `Summable (firstLengthWeight (h := h))`.
5. `bridgeFiniteBridgeSums_of_firstLengthWeight` derives all six clauses of
   `FiniteBridgeSums` from first-length summability:
   the two normalised clauses by `Summable.div_const`; the two confined clauses by
   `Summable.subtype`; the unconfined `weight` clause by step 2. No geometry of
   `InLogCorridor` is needed for this conditional reduction.
6. `finite_bridge_sums_of_stripGrowthBelowMu` composes 4 and 5, with exactly the
   task-declared hypothesis
   `∀ h ≥ 1, ∃ C β, 0 ≤ C ∧ 0 ≤ β ∧ β < 2 cos(π/8) ∧ ∀ n s, (∀ p∈s, len=n) → card s ≤ C β^n`.

## Verification performed (fresh, this checkpoint)

1. Standalone extraction of the previously retained reduction fence from `RESEARCH.md` at
   commit `91e0fb7f…`: 854 lines; `lake env lean` exit 0.
2. The final saved `Submission.lean`: `lake env lean Submission.lean` exit 0, with only
   `warning(hasSorry)` on the original `finite_bridge_sums`.
3. Prescribed host diagnostic:
   `check-lean --workspace generated/problem --file Submission.lean --timeout-seconds 0`
   exited 0. `sourceDigest = 19ecdec2c0649b8d02a43f1b915737426fa3aa6ba04d9370622a8afc6e47624d`,
   `environmentDigest = 709c0e42f20836fdb664e11102621217447bb4ac772b6cb6794a0ee5b2e1f1da`,
   sole message is the original sorry (line 195 in the final file). `captureComplete` was true.
4. Type preflight of the assigned declaration:
   `check-lean --type '(∀ h : ℕ, 1 ≤ h → ∃ C β : ℝ, 0 ≤ C ∧ 0 ≤ β ∧ β < 2 * Real.cos (Real.pi / 8) ∧ ∀ (n : ℕ) (s : Finset (BridgePath h)), (∀ p ∈ s, p.vertices.length = n) → (s.card : ℝ) ≤ C * β ^ n) → FiniteBridgeSums'`
   with `--context OAI.PolynomialVacuumBridge.Corridor.finite_bridge_sums_of_stripGrowthBelowMu`
   returned `status: elaborated`, exit 0.
5. `#print axioms` on `finite_bridge_sums_of_stripGrowthBelowMu` and
   `bridgeSummable_firstLengthWeight_of_mu_bound`:
   `[propext, Classical.choice, Quot.sound]` only.

Tooling note: the host’s `math_original_context_changed` check treats top-level `open scoped`
and doc-comment text outside original declarations as frozen context. The first integration
failed for that reason. Removing the added top-level `open scoped BigOperators` and added
module/doc comments made the file pass; no math changed.

## What was attempted / negative scope

- The earlier retained route `FiniteBridgeSums ← per-width strict sub-μ geometric count bound`
  was recompiled and then integrated here. This is complete and kernel-checked.
- The unconditional input `StripGrowthBelowMu` was **not** proved. Previous checkpoints
  inspected the local Mathlib corpus for honeycomb/hexagonal SAWs, connective constants,
  transfer-matrix spectral radius, Perron–Frobenius and finite-width subcriticality; no
  applicable theorem was found. The searches are recorded in the prior research checkpoint
  (seed research history / earlier commits) and are not repeated unchanged here.
- Advisory enumeration (not proof) from earlier checkpoints shows small-width growth bases
  increasing toward `μ = 2cos(π/8)`; no counterexample to strict finiteness was found. These
  counts are advisory only and are not used in the Lean proof.

## Precise unresolved inference

For every fixed width `h ≥ 1` (it suffices to handle `h ≥ 2`), prove the unconditional
statement

```lean
∃ C β : ℝ, 0 ≤ C ∧ 0 ≤ β ∧ β < 2 * Real.cos (Real.pi / 8) ∧
  ∀ (n : ℕ) (s : Finset (BridgePath h)),
    (∀ p ∈ s, p.vertices.length = n) → (s.card : ℝ) ≤ C * β ^ n
```

Equivalently (and sufficient for the frozen target), prove for every such `h`
`Summable (weight (h := h))` and `Summable (firstLengthWeight (h := h))`. Constants may
depend on `h`; no uniform `β` is possible; the strict inequality is essential. This is the
unconditional finite-width strict subcriticality/growth estimate for simple paths in the
hexagonal strip, i.e. the free input `StripGrowthBelowMu`.

Independently checkable smaller obligations:
- **width one**: at most two width-1 bridge paths of each length (fits in a closed `Fin`
  cardinality bound and is unconditional);
- **fixed width `h`**: the displayed `C`, `β` count bound for that single `h`, with explicit
  constants and strict `β < μ` (a strictly smaller per-width target, not a rename of the
  uniform theorem);
- **finite confined clause**: `Finite (ConfinedBridgePath h)` or the three confined
  summabilities; these are independent of the unconfined growth estimate but do not by
  themselves imply `FiniteBridgeSums`.

## Reopen triggers

- A checked finite-width transfer-matrix / cut-state certificate giving a strict sub-μ
  Perron root for every width.
- A local library theorem supplying the strict per-width count estimate or summability.
- A frozen-contract or environment change.
