# Honeycomb 已验分层接口增量：任意 profile → firstLengthWeight → 原六项

本消息是可供现有共享 objective 采用的本地形式化建议及代码增量。未改活动源码/队列，也未请求重新运行原题。原题 `OAI.PolynomialVacuumBridge.Corridor.finite_bridge_sums` 仍未由本包证明。

规范基底 commit 96e89fbc7f26408eaaab99235481d1dd64ffcc1c，canonical SHA256 1274ab0b8f9c01548559d48d055fc92a20ebf2433f643bd8ad90a313b304b674。主8接口真实 Lean exit0，3.372312 秒；occupied-slab 组合 exit0，3.993500 秒。9条公理逐项仅标准三项。证据：/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/honeycomb-length-profile-followup-20261024/validation-02-result.json、/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/honeycomb-length-profile-followup-20261024/validation-03-occupied-result.json、/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/honeycomb-length-profile-followup-20261024/axioms-audit.json。精确声明头、SHA256 和剩余义务见 /home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/honeycomb-length-profile-followup-20261024/delivery-contract.json。

主接口使用任意 `profile : BridgePath h → ℕ`。`bridgeProfileMass profile n` 是精确 profile 层的权重 tsum；Bridge 入口从 `hw : Summable weight` 自动取得每层 HasSum，通用入口则显式要求每层 HasSum。不要仅凭可能发散的 tsum 相等推断分层正确。`C≥0` 和 `length≤C*(profile+1)` 处理平移/零层，不把矩阵幂指标强行当成路径顶点数。

依赖：已递送的 TheoremOS.FiniteMatrixFirstMoment 两条定理和 matrixMass；canonical 定义、bridgeWeight_nonneg、bridgeFiniteBridgeSums_of_firstLengthWeight。旧矩阵增量 SHA256 fa18397788fad96d9c54a45b51dc9f8aa338da30c5bd5108a0445c5437fd3fb6，本包逐字复用，下面不重复它。

第一段完整主增量自带 namespace；加到顶层，已有 namespace 若打开须先正确闭合，不嵌套成重复的 OAI。

```lean
namespace TheoremOS.ProfileSummability

open scoped BigOperators

/-- The real mass of an exact profile fiber. Its use as a coefficient requires
fiber convergence; the theorems below derive it from whole-family summability
or request `HasSum`, rather than relying on a possibly divergent `tsum`. -/
noncomputable def fiberMass {α : Type*} (w : α → ℝ) (profile : α → ℕ) (n : ℕ) : ℝ :=
  ∑' a : {a : α // profile a = n}, w a.val

theorem summable_fiberMass_of_summable
    {α : Type*} {w : α → ℝ} (profile : α → ℕ) (hw : Summable w) :
    Summable (fiberMass w profile) := by
  exact (hw.hasSum.tsum_fiberwise profile).summable


/-- Exact convergent fiber sums may be lifted through any nonnegative profile
multiplier. Fibers may be infinite; each is required to have the stated sum. -/
theorem summable_profileScale_of_hasSum
    {α : Type*} {w : α → ℝ} {profile : α → ℕ} {c scale : ℕ → ℝ}
    (hw : ∀ a, 0 ≤ w a) (hscale : ∀ n, 0 ≤ scale n)
    (hfiber : ∀ n, HasSum (fun a : {a : α // profile a = n} => w a.val) (c n))
    (hc : Summable (fun n => scale n * c n)) :
    Summable (fun a => scale (profile a) * w a) := by
  let f : (Σ n : ℕ, {a : α // profile a = n}) → ℝ :=
    fun p => scale p.1 * w p.2.val
  have hscaled (n : ℕ) :
      HasSum (fun a : {a : α // profile a = n} => scale n * w a.val)
        (scale n * c n) := (hfiber n).mul_left (scale n)
  have hsigma : Summable f :=
    (summable_sigma_of_nonneg (f := f)
      (fun p => mul_nonneg (hscale p.1) (hw p.2.val))).2
      ⟨fun n => (hscaled n).summable,
        hc.congr (fun n => (hscaled n).tsum_eq.symm)⟩
  have hreindex : Summable
      (fun p : Σ n : ℕ, {a : α // profile a = n} =>
        scale (profile p.2.val) * w p.2.val) := by
    refine hsigma.congr fun p => ?_
    change scale p.1 * w p.2.val = scale (profile p.2.val) * w p.2.val
    rw [p.2.property]
  exact (Equiv.sigmaFiberEquiv profile).summable_iff.mp hreindex


/-- A first moment in an arbitrary natural profile dominates a size moment
whenever `size <= C * (profile+1)`. The shift handles zero/offset profiles. -/
theorem summable_sizeWeight_of_hasSum
    {α : Type*} {w : α → ℝ} {size profile : α → ℕ} {c : ℕ → ℝ} {C : ℝ}
    (hw : ∀ a, 0 ≤ w a) (hC : 0 ≤ C)
    (hsize : ∀ a, (size a : ℝ) ≤ C * ((profile a : ℝ) + 1))
    (hfiber : ∀ n, HasSum (fun a : {a : α // profile a = n} => w a.val) (c n))
    (hc : Summable c) (hmoment : Summable (fun n : ℕ => (n : ℝ) * c n)) :
    Summable (fun a => (size a : ℝ) * w a) := by
  have hshift : Summable (fun n : ℕ => C * ((n : ℝ) + 1) * c n) := by
    refine ((hmoment.add hc).mul_left C).congr fun n => ?_
    ring
  have hscale : ∀ n : ℕ, 0 ≤ C * ((n : ℝ) + 1) :=
    fun n => mul_nonneg hC (add_nonneg (Nat.cast_nonneg n) zero_le_one)
  have hdom : Summable (fun a => C * ((profile a : ℝ) + 1) * w a) :=
    summable_profileScale_of_hasSum (w := w) (profile := profile) (c := c)
      (scale := fun n => C * ((n : ℝ) + 1)) hw hscale hfiber hshift
  exact Summable.of_nonneg_of_le
    (fun a => mul_nonneg (Nat.cast_nonneg _) (hw a))
    (fun a => mul_le_mul_of_nonneg_right (hsize a) (hw a)) hdom


end TheoremOS.ProfileSummability

namespace OAI.PolynomialVacuumBridge.Corridor

open scoped BigOperators Matrix

/-- Exact bridge mass in a caller-chosen profile fiber; the transfer exponent
may be occupied slab span, rather than the path's vertex length. -/
noncomputable def bridgeProfileMass {h : ℕ}
    (profile : BridgePath h → ℕ) (n : ℕ) : ℝ :=
  TheoremOS.ProfileSummability.fiberMass (weight (h := h)) profile n

theorem bridgeSummable_firstLengthWeight_of_profileFirstMoment
    {h : ℕ} (profile : BridgePath h → ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hsize : ∀ p : BridgePath h,
      (p.vertices.length : ℝ) ≤ C * ((profile p : ℝ) + 1))
    (hw : Summable (weight (h := h)))
    (hmoment : Summable (fun n : ℕ => (n : ℝ) * bridgeProfileMass profile n)) :
    Summable (firstLengthWeight (h := h)) := by
  change Summable (fun p : BridgePath h => (p.vertices.length : ℝ) * weight p)
  refine TheoremOS.ProfileSummability.summable_sizeWeight_of_hasSum
    (w := weight (h := h)) (size := fun p => p.vertices.length)
    (profile := profile) (c := bridgeProfileMass profile)
    bridgeWeight_nonneg hC hsize ?_
    (TheoremOS.ProfileSummability.summable_fiberMass_of_summable profile hw) hmoment
  intro n
  exact (hw.subtype (fun p : BridgePath h => profile p = n)).hasSum


theorem bridgeSummable_firstLengthWeight_of_profileFactorization
    {h : ℕ} {ι : Type*} [Fintype ι]
    (profile : BridgePath h → ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hsize : ∀ p : BridgePath h,
      (p.vertices.length : ℝ) ≤ C * ((profile p : ℝ) + 1))
    (hw : Summable (weight (h := h))) (L R : ℕ → ι → ℝ)
    (hL : ∀ n i, 0 ≤ L n i) (hR : ∀ n i, 0 ≤ R n i)
    (hfactor : ∀ a b, bridgeProfileMass profile (a + b) = ∑ i, L a i * R b i) :
    Summable (firstLengthWeight (h := h)) := by
  apply bridgeSummable_firstLengthWeight_of_profileFirstMoment profile hC hsize hw
  exact TheoremOS.FiniteMatrixFirstMoment.summable_firstMoment_of_finite_nonneg_factorization
    (c := bridgeProfileMass profile) (L := L) (R := R) hL hR hfactor
    (TheoremOS.ProfileSummability.summable_fiberMass_of_summable profile hw)

theorem bridgeSummable_firstLengthWeight_of_matrixProfile
    {h : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (profile : BridgePath h → ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hsize : ∀ p : BridgePath h,
      (p.vertices.length : ℝ) ≤ C * ((profile p : ℝ) + 1))
    (hw : Summable (weight (h := h)))
    (A : Matrix ι ι ℝ) (u v : ι → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hidentity : ∀ n, bridgeProfileMass profile n =
      TheoremOS.FiniteMatrixFirstMoment.matrixMass A u v n) :
    Summable (firstLengthWeight (h := h)) := by
  have hc : Summable (TheoremOS.FiniteMatrixFirstMoment.matrixMass A u v) :=
    (TheoremOS.ProfileSummability.summable_fiberMass_of_summable profile hw).congr hidentity
  have hm := TheoremOS.FiniteMatrixFirstMoment.summable_matrix_firstMoment A u v hA hu hv hc
  apply bridgeSummable_firstLengthWeight_of_profileFirstMoment profile hC hsize hw
  refine hm.congr fun n => ?_
  rw [hidentity n]


/-- A special case only: this does not claim that a honeycomb transfer matrix
is naturally indexed by vertex length. -/
theorem bridgeSummable_firstLengthWeight_of_lengthProfileFactorization
    {h : ℕ} {ι : Type*} [Fintype ι]
    (hw : Summable (weight (h := h))) (L R : ℕ → ι → ℝ)
    (hL : ∀ n i, 0 ≤ L n i) (hR : ∀ n i, 0 ≤ R n i)
    (hfactor : ∀ a b,
      bridgeProfileMass (fun p : BridgePath h => p.vertices.length) (a + b) =
        ∑ i, L a i * R b i) : Summable (firstLengthWeight (h := h)) := by
  apply bridgeSummable_firstLengthWeight_of_profileFactorization
    (fun p : BridgePath h => p.vertices.length) (C := 1) zero_le_one ?_ hw L R hL hR hfactor
  intro p
  simp only [one_mul]
  linarith

/-- Composition with the accepted canonical six-clause reduction. Each width
may use its own finite state type, profile and comparison constant. -/
theorem bridgeFiniteBridgeSums_of_matrixProfiles
    (ι : ℕ → Type*) [∀ h, Fintype (ι h)] [∀ h, DecidableEq (ι h)]
    (profile : ∀ h, BridgePath h → ℕ) (C : ℕ → ℝ)
    (A : ∀ h, Matrix (ι h) (ι h) ℝ) (u v : ∀ h, ι h → ℝ)
    (hw : ∀ h, 1 ≤ h → Summable (weight (h := h)))
    (hC : ∀ h, 1 ≤ h → 0 ≤ C h)
    (hsize : ∀ h, 1 ≤ h → ∀ p : BridgePath h,
      (p.vertices.length : ℝ) ≤ C h * (((profile h) p : ℝ) + 1))
    (hA : ∀ h, 1 ≤ h → ∀ i j, 0 ≤ A h i j)
    (hu : ∀ h, 1 ≤ h → ∀ i, 0 ≤ u h i)
    (hv : ∀ h, 1 ≤ h → ∀ i, 0 ≤ v h i)
    (hidentity : ∀ h, 1 ≤ h → ∀ n, bridgeProfileMass (profile h) n =
      TheoremOS.FiniteMatrixFirstMoment.matrixMass (A h) (u h) (v h) n) :
    FiniteBridgeSums := by
  apply bridgeFiniteBridgeSums_of_firstLengthWeight
  intro h hh
  exact bridgeSummable_firstLengthWeight_of_matrixProfile (profile h)
    (hC h hh) (hsize h hh) (hw h hh) (A h) (u h) (v h)
    (hA h hh) (hu h hh) (hv h hh) (hidentity h hh)


end OAI.PolynomialVacuumBridge.Corridor
```

第二段是直接接已验几何的额外推论。它依赖已验 `bridgeLength_le_occupiedSlabs`、`bridgeOccupiedSlabs`；几何增量 SHA256 c67b5cf4dabbaf84a7b3158406e055fc63442a404c6b9c16657a063e2cf2987f，本包集成 harness 逐字复用。把下面这段加在 OAI.PolynomialVacuumBridge.Corridor namespace 内，位于几何和第一段之后。它将 profile 设为实际 occupied-slab 数、C 设为 2*h，已经通过 exact_mod_cast 与非负比较。

```lean
/-- The checked occupied-slab length estimate discharges every geometric
comparison premise. Only mass summability and the exact transfer encoding remain. -/
theorem bridgeFiniteBridgeSums_of_occupiedSlabMatrices
    (ι : ℕ → Type*) [∀ h, Fintype (ι h)] [∀ h, DecidableEq (ι h)]
    (A : ∀ h, Matrix (ι h) (ι h) ℝ) (u v : ∀ h, ι h → ℝ)
    (hw : ∀ h, 1 ≤ h → Summable (weight (h := h)))
    (hA : ∀ h, 1 ≤ h → ∀ i j, 0 ≤ A h i j)
    (hu : ∀ h, 1 ≤ h → ∀ i, 0 ≤ u h i)
    (hv : ∀ h, 1 ≤ h → ∀ i, 0 ≤ v h i)
    (hidentity : ∀ h, 1 ≤ h → ∀ n,
      bridgeProfileMass (fun p : BridgePath h => (bridgeOccupiedSlabs p).card) n =
        TheoremOS.FiniteMatrixFirstMoment.matrixMass (A h) (u h) (v h) n) :
    FiniteBridgeSums := by
  refine bridgeFiniteBridgeSums_of_matrixProfiles ι
    (fun h p => (bridgeOccupiedSlabs p).card) (fun h => 2 * (h : ℝ))
    A u v hw ?_ ?_ hA hu hv hidentity
  · intro h _hh
    positivity
  · intro h _hh p
    have hlength : (p.vertices.length : ℝ) ≤
        2 * (h : ℝ) * ((bridgeOccupiedSlabs p).card : ℝ) := by
      exact_mod_cast bridgeLength_le_occupiedSlabs p
    exact hlength.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right zero_le_one)
      (mul_nonneg zero_le_two (Nat.cast_nonneg h)))
```

剩余数学输入仍为：(1) 每 h≥1 的真实桥质量可和性，可由 uniform finite-box 总质量界加此前归约取得；(2) 有限非负 transfer/因子分解的精确 profile 系数恒等式，包括端点、n=0 和指标平移。对于 occupied-slab 实例，长度比较已由几何包及第二段消去；对其它 profile，使用第一段传入真实比较界。

这是辅助定理及条件归约的内核通过，不是原题整体成功。固定 Lean/Mathlib/封存环境，32 GiB、单核 -j1、maxHeartbeats=0，无 wall/CPU/调用次数 cap。首次宽导入辅助准备被诊断性 SIGTERM（exit=-15，非timeout）中断，后精简依赖context exit0；首候选多余dsimp导致exit1的证据也保留。本次没有改原题活动进程、runtime、state 或队列。主代理可按正常流程串行递送本条具体增量。
