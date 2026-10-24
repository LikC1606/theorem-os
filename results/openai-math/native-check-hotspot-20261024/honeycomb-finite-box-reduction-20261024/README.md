# Honeycomb 有限列盒到零阶可求和性的条件归约

已得到并用固定 Lean 4.34.1、原运行的只读 sealed Mathlib 缓存真实验证了四个新声明。最新无预算检查实际退出码为 **0**，耗时 13.47 秒，没有 wall/CPU 时间、调用次数或 Lean heartbeat 预算；`maxHeartbeats=0`，`-j1`、32 GiB 地址空间上限保持不变，峰值 RSS 6,886,212 KiB。四个新声明的 `#print axioms` 均只有 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx`。这是独立工作区的内核检查，正常队列递送仅为 advisory，尚未由活动任务宿主发布原生 TaskProof。

可递送的完整文件是 [Submission.lean](Submission.lean)，12,310 字节，SHA256：

```text
1fbba78bad15173b4be8b033009ab80e7d892347cc4324b0baf608f07d44dca4
```

增量源码为 [FiniteBoxLemmas.lean.inc](FiniteBoxLemmas.lean.inc)。它应置于已有 namespace `OAI.PolynomialVacuumBridge.Corridor` 内、原目标之前。完整文件以 canonical commit `96e89fbc7f26408eaaab99235481d1dd64ffcc1c` 的 8,797 字节源码为基底，原有声明逐字保留，仅插入增量和检查命令；数学工作没有改活动源码、runtime 或共享依赖。随后仅通过宿主正常 `queueRunEdit` 通道递送了下述共享参考任务。基底副本与身份见 [canonical-Submission.lean](canonical-Submission.lean) 和 [provenance.json](provenance.json)。

## 精确接口

坐标与盒定义为：

```lean
def bridgeBoxColumn : Vertex → ℤ
  | .up i j => 2 * i + j
  | .down i j => 2 * i + j + 1

def bridgeInColumnBox {h : ℕ} (R : ℕ) (p : BridgePath h) : Prop :=
  ∀ v ∈ p.vertices,
    -(2 * (R : ℤ)) ≤ bridgeBoxColumn v ∧
      bridgeBoxColumn v ≤ 2 * (R : ℤ) + 1
```

共同列盒引理无需任何质量上界：

```lean
theorem bridgeFiniteSet_commonColumnBox {h : ℕ}
    (s : Finset (BridgePath h)) :
    ∃ R : ℕ, ∀ p ∈ s, bridgeInColumnBox R p
```

构造 `R` 为所有路径、所有顶点的整数列坐标绝对值的有限上确界。每条路径是有限列表，因此任意有限桥族共处该列盒；该步骤不需要先证明固定盒内路径族有限。

主条件归约的精确声明是：

```lean
theorem bridgeSummable_weight_of_uniformColumnBoxBound {h : ℕ} {K : ℝ}
    (H : ∀ (R : ℕ) (s : Finset (BridgePath h)),
      (∀ p ∈ s, bridgeInColumnBox R p) → ∑ p ∈ s, weight p ≤ K) :
    Summable (weight (h := h))
```

证明先用共同列盒将 `H` 应用于任意有限桥族，再用已集成的 `bridgeWeight_nonneg` 与 Mathlib `summable_of_sum_le`。`h ≥ 1` 不需要成为该逻辑归约的附加前提。`K` 对当前固定 h 的所有 R 和有限桥族统一；没有假设不同 h 共用 K，也没有将 K 设成 1。对空族应用 H 已蕴含 K 非负，因此声明不再另外要求该符号条件。

同一源码还给出：

```lean
bridgeFiniteSum_weight_le_of_uniformColumnBoxBound :
  (∀ R s, (∀ p ∈ s, bridgeInColumnBox R p) →
    ∑ p ∈ s, weight p ≤ K) →
  ∀ s : Finset (BridgePath h), ∑ p ∈ s, weight p ≤ K

bridgeMass_le_of_uniformColumnBoxBound :
  (∀ R s, (∀ p ∈ s, bridgeInColumnBox R p) →
    ∑ p ∈ s, weight p ≤ K) → bridgeMass h ≤ K
```

上述四个名称全部位于 `OAI.PolynomialVacuumBridge.Corridor` namespace。可供正常 typed delivery 采用的完整目标与精确类型见 [delivery-contract.json](delivery-contract.json)。

## 已检查的边界与剩余数学

开始前已读新路线交接和当前可见 RESEARCH/辅助源码；原 854 行 fence SHA256 为 `14d52c1af8fa50f49ff7a8a6acd15a6acfecd3f88df7b0cd375fdc486a0449f2`，完整保存在 [prior-research-854-lines.lean](prior-research-854-lines.lean)。其中有计数到一阶矩的旧归约，没有本次的有限列盒共同容纳或有限盒总质量条件归约，因此本次补充未重复旧声明。未读取发布方答案或隐藏 reasoning。

本次没有证明统一有限盒上界 H、parafermionic 配对、精确有限状态编码、`vertices.length ≤ 2*h*occupiedSlabs`、矩阵 Green 质量到一阶矩的提升或严格指数增长界。它仅完成新路线中“有限盒上界 → 无限桥族零阶可求和性”的接口。活动原目标 `finite_bridge_sums` 在完整文件第 239 行仍有其原始 `sorry`；最终 stdout 中唯一的 sorry 警告属于该保留目标，不属于四个新声明。不能据此标记一阶矩、全部六项或原题完成。

## 真实验证记录

最新 [validation-no-budget-result.json](validation-no-budget-result.json)、[stdout](validation-no-budget.stdout.log)、[stderr](validation-no-budget.stderr.log) 保留实际命令、资源、退出码、声明类型和公理；[validation-no-budget-launch.json](validation-no-budget-launch.json) 绑定最终源码 SHA。[validate-no-budget.py](validate-no-budget.py) 不传进程等待超时，不设置 CPU 时间上限，没有 `invocationLimit`，并将 Lean `maxHeartbeats` 设为 0。保留的 `maxRecDepth=1000` 是语言递归深度选项。固定版本与封存缓存身份见 [environment-readability.json](environment-readability.json)。

先前 [validation-final-result.json](validation-final-result.json) 的 exit 0 记录有效，但当时入口仍设置 wall 180 秒、CPU 120/125 秒和 `maxHeartbeats=800000`，不能称为无预算验证。该记录及脚本原样保留；最新一次复验仅用于修正与授权无预算要求冲突的入口，源码、数学环境和四个声明均未改变。

首次入口在 6 GiB 地址空间限制下于 0.32 秒 import 阶段退出 1，尚未检查任何定理。报错指向的 `Injective.ir` 实际存在且可读，故没有把它记为已确认依赖缺失。调整为父任务授权的同版本、只读封存缓存、32 GiB/-j1 后，首次真实 elaboration 在 `Finset.le_sup` 的映射推断上失败；显式给出同一映射后，必要复验通过。失败源码与实际记录均保留在 [attempts](attempts/)；早期 runner 复用了 stdout 文件名，相关原记录与日志保存方式已在 [失败证据索引](failed-attempt-evidence-index.json) 明确说明。没有通过更换数学环境、下载依赖或改变活动现场来规避问题。

## 正常队列递送与回读

已通过 [queue-finite-box-reference.ts](queue-finite-box-reference.ts) 调用冻结 runtime 的正常 `queueRunEdit` 接口。先 dry-run，预测原有任务 `invalidated=[]`；随后排队 edit `honeycomb-finite-box-5e38146e7324`，宿主于 2026-10-24 09:09:16.506 UTC 标记 **applied**。最终计划版本为 `54e65a72a7df77c506a1f0425f35c71d388766da76e45a2c6cda55271fceca90`。

该 edit 仅在原六项后新增 `finite_box_zero_mass_reference`，`kind=research`、`ownerId=researcher-2`、`groupId=main`、`sharing=problem`，没有添加任何原任务依赖。原六个完整 task 对象、objective、revision、status、pendingValidation、完整 assignment、groups 与 proofRoutes 均经逐项回读保持一致。宿主 `affectedTasks` 恰为新增任务，`recheck.status=not-required`。新任务回读时为 pending；当前 engineer 仍在 `initial_goal_1`，r2 仍在 `initial_research_2`。

交接全文及增量源码内联在 [native-advisory-handoff.md](native-advisory-handoff.md)，没有要求覆盖活动 `Submission.lean`。宿主可见性规则使同一 main group 的 pending 任务也进入当前上下文；已实际读取 engineer 与 r2 的宿主生成 `COOPERATION.json`，确认两份均含新任务和逐字完整 objective。这证明参考已进入正常共享上下文，不声称模型已经阅读或采用。

准备、排队与实际应用证据分别为 [native-advisory-preparation.json](native-advisory-preparation.json)、[native-advisory-queue-receipt.json](native-advisory-queue-receipt.json)、[native-advisory-applied-readback.json](native-advisory-applied-readback.json)。最后一份保存原六项摘要与完整 assignment 比对、宿主 edit 回执、两份上下文 SHA 及可见性结果。此次交付是 **advisory 参考**，不是原生 proof 验收；四个新声明尚未由活动宿主集成或发布 TaskProof，原题仍未解决。没有直接写活动 state、delivery 文件、活动源码或冻结 runtime，也没有 git 提交。
