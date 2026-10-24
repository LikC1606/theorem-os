# 有限非负矩阵：Green 可和性推出一阶矩可和性

已证明两个可复用定理，最终用固定 Lean 4.34.1 与 Mathlib pin `d13f23b723b8a846827a245b89c10fc7d3f11612` 真实检查，**exit 0**，耗时 **4.673 秒**，峰值 RSS **2,290,528 KiB**。两条定理的 `#print axioms` 都恰为 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx`；最终 stdout 无错误或警告，stderr 为空。

本次完成有限非负矩阵的一阶矩分析步骤。没有证明 Honeycomb 的统一有限盒质量上界、精确 transfer 编码或路径长度与 span 的关系，原题仍未解决。结果仅为独立工作区的本地内核证据，尚无活动宿主的原生 TaskProof 验收。

## 已验证接口

完整源码：[FiniteMatrixFirstMoment.lean](FiniteMatrixFirstMoment.lean)，4,970 字节，SHA256：

```text
bae1606a1e3ad7675bdfa043f99d08d1e5a9fb7e822fb31612a19eec63eff33f
```

所有新声明在独立 namespace `TheoremOS.FiniteMatrixFirstMoment` 内。第一条是更一般的有限非负分解定理：

```lean
theorem summable_firstMoment_of_finite_nonneg_factorization
    {ι : Type*} [Fintype ι] {c : ℕ → ℝ} {L R : ℕ → ι → ℝ}
    (hL : ∀ n i, 0 ≤ L n i) (hR : ∀ n i, 0 ≤ R n i)
    (hfactor : ∀ a b, c (a + b) = ∑ i, L a i * R b i)
    (hc : Summable c) : Summable (fun n : ℕ => (n : ℝ) * c n)
```

对每个状态，一侧恒零则无贡献；否则另一侧的正见证和 `c` 的平移级数给出左右两侧可和。把有限个 Cauchy 乘积相加，恰得到 `(n+1)*c n` 的可和性，再减去 `c n`。无需先构造裁剪矩阵或收缩向量。

第二条实例化为有限矩阵，`matrixMass A u v n` 定义为 `u ⬝ᵥ ((A ^ n) *ᵥ v)`：

```lean
theorem summable_matrix_firstMoment
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (u v : ι → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hc : Summable (matrixMass A u v)) :
    Summable (fun n : ℕ => (n : ℝ) * matrixMass A u v n)
```

取 `L a = u ᵥ* A^a`、`R b = A^b *ᵥ v`，矩阵幂的乘法与点积结合律给出第一条所需的精确分解。空状态集和不可见状态已被该证明覆盖，不要求 irreducibility、完整矩阵 Green 可和性或 Perron 根定理。

## 与原题的精确连接及限制

已读取当前 canonical commit `96e89fbc7f26408eaaab99235481d1dd64ffcc1c` 的规范源码、公开 RESEARCH.md 和已递送路线，未读 ProducedSolution 或隐藏模型推理。规范副本及身份保存在 [canonical-Submission.lean](canonical-Submission.lean)、[provenance.json](provenance.json)。公开旧笔记含过期的 assignment/集成状态陈述，当前规范和宿主身份优先。

规范中的 `bridgeFiniteBridgeSums_of_firstLengthWeight` 已把全部六项原结论归约到 `firstLengthWeight` 可和性。若对每个固定 h 建立精确有限 transfer 模型，使 `matrixMass A u v k` 等于 span k 的原桥路径总权重，有限盒四引理提供的条件零阶可和性便给出 `Summable c`。本次矩阵定理随后给出 `Summable (k*c k)`。再用已验证的 `vertices.length ≤ 2*h*k` 和有限族分组上界，即可推出原桥路径的一阶长度矩可和。

该连接仍需真正证明：固定 h 的统一有限盒上界；保留 source/terminal 标记、cut connectivity、无闭环、无空 padding、精确多重性和 `alpha^vertices.length` 权重的 transfer 编码；该编码上的 span/长度界与分组估计。本次不建立这些几何或组合对象，也不证明 `strip_growth_below_mu`。更完整论证与证据边界见 [MATHEMATICAL-ROUTE.md](MATHEMATICAL-ROUTE.md) 和 [NEED-MAP.txt](NEED-MAP.txt)。

“单个端点 Green 级数可和，故未裁剪矩阵每一项 Green 级数都可和”的推论是假的：取 `A=diag(1/2,2)`、`u=v=(1,0)`，端点系数是 `(1/2)^n`，另一对角项却是 `2^n`。本次直接定理避开该推论；反例是明确的初等数学计算，未另外声称有反例 Lean 验核。

## 实际验核与故障记录

最终证据：[validation-04-final-result.json](validation-04-final-result.json)、[launch](validation-04-final-launch.json)、[stdout](validation-04-final.stdout.log)、[stderr](validation-04-final.stderr.log)。执行入口为 [validate.py](validate.py)，使用原运行只读封存包缓存 `/proc/1250131/fd/5`，环境身份 `2d808da67c8ab8ad74458d8a53ecc2ee8da9c63a825e0429439ebf56a9a78c87`。

实际命令带 `--threads=1 --memory=32768 -DautoImplicit=false -DmaxHeartbeats=0 -DmaxRecDepth=1000`；进程单核、32 GiB 地址空间，没有 wall/CPU 时间限制或调用次数上限。入口不传 `process.wait` timeout，不设置 `RLIMIT_CPU`。`maxRecDepth=1000` 是语言递归深度选项。没有新下载依赖或构建 Mathlib。

前三次过程完整保留，不把编译错误或诊断中断计作通过：

| 记录 | 实际结果 | 定位和后续修正 |
| --- | --- | --- |
| `validation-01-*` | 正常诊断 SIGINT，exit -2，453.90 秒 | 单 worker 持续计算且内存增长；imports 已映射、无输入 I/O，尚无具体战术定位。经父任务授权仅中断自己的辅助检查，未碰原题运行链。 |
| `validation-02-diagnostic-*` | 正常诊断 SIGINT，exit -2，53.72 秒 | 减少 import、关闭异步、实时 stderr 标记确认前置证明均完成，停在 Cauchy API 应用；随后显式给出其 `f/g`，不再依赖高阶函数推断。 |
| `validation-03-explicit-cauchy-*` | 自然 exit 1，4.89 秒 | 显式参数后全部声明快速 elaboration；唯一实质错误是 `Finset.card_antidiagonal` 名称，应为 `Finset.Nat.card_antidiagonal`。该失败输出的 `sorryAx` 来自错误占位，绝不是验核通过。 |
| `validation-04-final-*` | 自然 exit 0，4.67 秒 | 修正精确 namespace、移除诊断 IO，两个定理公理集合均符合要求。 |

每次 launch 绑定对应源码 SHA，`*-source.lean` 保存当次源码快照，stdout/stderr 分别独立保存。两次诊断中断另有 `*-interruption.json`，包括原因与实际进程证据。没有 wall 超时或求解预算失败，也没有同时运行重复候选。

## 递送材料

精确接口与验核索引：[delivery-contract.json](delivery-contract.json)。可插入增量：[FiniteMatrixFirstMoment.lean.inc](FiniteMatrixFirstMoment.lean.inc)，SHA256 `fa18397788fad96d9c54a45b51dc9f8aa338da30c5bd5108a0445c5437fd3fb6`。增量保留独立 namespace，当前原题 `import Mathlib` 已覆盖其 API；可放在 imports 后、`namespace OAI` 前，或 `end OAI` 后，无需覆盖已有源码。

完整内联 advisory：[native-advisory-handoff.md](native-advisory-handoff.md)，8,638 字节，SHA256 `e56599f0c36605c4ca7db106ce8b449cf912c9269f4f353fdb8df4ae247bc969`。它明确只关闭矩阵分析步骤、保留未解几何输入及本地验核/原生验收边界。

父任务已用 fresh planVersion 经正常队列串行递送：edit `honeycomb-finite-matrix-e56599f0c366` 于 2026-10-24 09:55:44.980 UTC **applied**，计划版本 `d487ab1d2595773b2deec8556dcce11d881cd34c274c79110c7f3480f9664c3b`。仅追加现有 pending 共享参考任务 `finite_box_zero_mass_reference` 的 objective，`affectedTasks` 仅此一项；reference 仍 pending/unassigned。全部已有 assignment、其他 task 定义、groups 与 proofRoutes 经实际回读保持一致。

solver、researcher-1、researcher-2、engineer 的四份宿主 `COOPERATION.json` 均已实际回读到完整 helper，含最终源码 SHA。该证据证明正常上下文可见，尚未证明模型已阅读或在数学上采用，更不构成 native TaskProof 或原题验收。

队列材料由父任务维护：[queue-matrix-reference.ts](queue-matrix-reference.ts)、[native-advisory-preparation.json](native-advisory-preparation.json)、[native-advisory-queue-receipt.json](native-advisory-queue-receipt.json)、[native-advisory-applied-readback.json](native-advisory-applied-readback.json)。完整文件与 SHA 清单见 [artifact-index.json](artifact-index.json)，包括上述四项及所有诊断/最终验核记录。

数学辅助文件均在本隔离目录。未改活动源码或 runtime，未直接写活动 state 或 worker delivery，未覆盖在途任务 objective/assignment/group/proofRoutes，未提交 git。队列状态变化由宿主正常应用。唯一仓库读取是 `git --no-optional-locks show` 保存已知 canonical 规范源码。
