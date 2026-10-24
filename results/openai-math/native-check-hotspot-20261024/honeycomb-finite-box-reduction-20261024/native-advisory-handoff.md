This is a shared advisory reference for the ongoing engineer and researcher-2 work. It supplies only checked auxiliary lemmas for the already proposed finite-box route. It does not replace the existing research assignment, assert the finite-box bound, or prove the original goal. Preserve all existing objectives and frozen original declarations. Attribution: independently developed Codex helper proofs; no publisher solution or hidden reasoning was read.

A finite family of finite vertex lists lies in one common column box. Consequently, for a fixed h, a bound K uniform over every radius R and every finite BridgePath h family in that box implies Summable (weight (h := h)) and bridgeMass h <= K. The input is exactly:

    forall (R : Nat) (s : Finset (BridgePath h)),
      (forall p in s, bridgeInColumnBox R p) -> sum p in s, weight p <= K

There is no extra h >= 1 premise in this logical reduction. No finite K, parafermionic cancellation, exact transfer encoding, first length moment, strict growth estimate, or original-goal solution is supplied. Do not claim those missing results or infer firstLengthWeight summability from this zeroth-mass reduction alone.

Checked source base: canonical commit 96e89fbc7f26408eaaab99235481d1dd64ffcc1c. Full reference source: 12310 bytes, SHA256 1fbba78bad15173b4be8b033009ab80e7d892347cc4324b0baf608f07d44dca4. The full reference deliberately preserves the original finite_bridge_sums sorry; use only the increment below, never overwrite your current Submission.lean from that reference snapshot.

Real local kernel result: actual exit code 0, 2026-10-24T09:05:08.037505+00:00, elapsed 13.472379584098235 seconds, Lean 4.34.1, Mathlib pin d13f23b723b8a846827a245b89c10fc7d3f11612, original read-only sealed-package identity 2d808da67c8ab8ad74458d8a53ecc2ee8da9c63a825e0429439ebf56a9a78c87. Invocation: lean --threads=1 --memory=32768 -DautoImplicit=false -DmaxHeartbeats=0 -DmaxRecDepth=1000 Submission.lean. There was no wall timeout, CPU time budget or invocation cap. Address-space limit remained 32 GiB, CPU affinity one core. Each of the four new declarations has exactly the printed axioms propext, Classical.choice, Quot.sound, with no sorryAx. The sole sorry warning belongs to the unchanged original target. Evidence file on the host: validation/native-check-hotspot-20261024/honeycomb-finite-box-reduction-20261024/validation-no-budget-result.json.

This is local kernel evidence, not native host TaskProof acceptance. Keep this as advisory progress and reuse the increment when useful. The engineer may adapt/merge the increment against current sources in its own normal worktree while preserving ongoing changes. Researcher-2 may cite these exact checked interfaces instead of reproving this already solved logical step; keep working on the remaining mathematical inputs. Any later formal integration or proof acceptance must use the ordinary host workflow. Do not launch redundant standalone Lean/Lake loops merely to recheck this reference. Host absolute paths are evidence indices only; the full increment is inline so no external path access is required.

Insert the following increment inside namespace OAI.PolynomialVacuumBridge.Corridor, after the existing bridgeWeight_nonneg helper and before the original target. Check for name collisions and adapt the small addition, preserving all existing source work.

Increment SHA256: 5c24df9ec75f6ec7aa9c1a65a67ea54bec70dea7542a3759c677fdd6615ac542

```lean
open scoped BigOperators

/-- Integer column coordinate of the frozen honeycomb vertices. -/
def bridgeBoxColumn : Vertex → ℤ
  | .up i j => 2 * i + j
  | .down i j => 2 * i + j + 1

/-- A path lies in the two-column-slab box indexed by `-R, ..., R`. -/
def bridgeInColumnBox {h : ℕ} (R : ℕ) (p : BridgePath h) : Prop :=
  ∀ v ∈ p.vertices,
    -(2 * (R : ℤ)) ≤ bridgeBoxColumn v ∧
      bridgeBoxColumn v ≤ 2 * (R : ℤ) + 1

/-- Every finite family of finite bridge paths lies in one common column box. -/
theorem bridgeFiniteSet_commonColumnBox {h : ℕ} (s : Finset (BridgePath h)) :
    ∃ R : ℕ, ∀ p ∈ s, bridgeInColumnBox R p := by
  classical
  let radius : BridgePath h → ℕ := fun p =>
    p.vertices.toFinset.sup (fun v => (bridgeBoxColumn v).natAbs)
  let R : ℕ := s.sup radius
  refine ⟨R, ?_⟩
  intro p hp v hv
  have hpR : radius p ≤ R := Finset.le_sup hp
  have hvR : (bridgeBoxColumn v).natAbs ≤ radius p :=
    Finset.le_sup (f := fun v : Vertex => (bridgeBoxColumn v).natAbs)
      (List.mem_toFinset.mpr hv)
  have hnat : (bridgeBoxColumn v).natAbs ≤ R := hvR.trans hpR
  have hcast : ((bridgeBoxColumn v).natAbs : ℤ) ≤ (R : ℤ) := by
    exact_mod_cast hnat
  have habs : |bridgeBoxColumn v| ≤ (R : ℤ) := by
    simpa only [Int.natCast_natAbs] using hcast
  obtain ⟨hlo, hhi⟩ := abs_le.mp habs
  constructor <;> omega

/-- A bound uniform in the box radius bounds every finite bridge-family sum. -/
theorem bridgeFiniteSum_weight_le_of_uniformColumnBoxBound {h : ℕ} {K : ℝ}
    (H : ∀ (R : ℕ) (s : Finset (BridgePath h)),
      (∀ p ∈ s, bridgeInColumnBox R p) → ∑ p ∈ s, weight p ≤ K) :
    ∀ s : Finset (BridgePath h), ∑ p ∈ s, weight p ≤ K := by
  intro s
  obtain ⟨R, hR⟩ := bridgeFiniteSet_commonColumnBox s
  exact H R s hR

/-- Conditional zeroth-mass reduction. The uniform finite-box bound is an input;
this theorem does not establish that bound or any first length moment. -/
theorem bridgeSummable_weight_of_uniformColumnBoxBound {h : ℕ} {K : ℝ}
    (H : ∀ (R : ℕ) (s : Finset (BridgePath h)),
      (∀ p ∈ s, bridgeInColumnBox R p) → ∑ p ∈ s, weight p ≤ K) :
    Summable (weight (h := h)) := by
  exact summable_of_sum_le (fun p => bridgeWeight_nonneg p)
    (bridgeFiniteSum_weight_le_of_uniformColumnBoxBound H)

/-- The same still-unproved finite-box input also bounds the full bridge mass. -/
theorem bridgeMass_le_of_uniformColumnBoxBound {h : ℕ} {K : ℝ}
    (H : ∀ (R : ℕ) (s : Finset (BridgePath h)),
      (∀ p ∈ s, bridgeInColumnBox R p) → ∑ p ∈ s, weight p ≤ K) :
    bridgeMass h ≤ K := by
  exact (bridgeSummable_weight_of_uniformColumnBoxBound H).tsum_le_of_sum_le
    (bridgeFiniteSum_weight_le_of_uniformColumnBoxBound H)
```
