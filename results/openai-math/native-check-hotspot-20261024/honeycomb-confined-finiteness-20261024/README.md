# Honeycomb logarithmic-corridor finiteness

已在固定官方定义下，无条件证明每个 `h : ℕ` 的 `ConfinedBridgePath h` 为有限类型，并证明原六项结论中的后三个 confined 可求和子句。完整原题仍未解决：一般高度的前三个完整 `BridgePath` 可求和子句未由本包证明。

[精确递送合同](delivery-contract.json) 给出可直接设置为 typed lemma 的合取：

```lean
∀ h : ℕ,
  Summable (fun p : ConfinedBridgePath h => weight p.val) ∧
  Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val) ∧
  Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val / confinedMass h)
```

已检验的汇总定理为 `OAI.PolynomialVacuumBridge.Corridor.bridgeConfined_sums`，其显式参数为 `(h : ℕ)`；直接证明项为 `fun h => OAI.PolynomialVacuumBridge.Corridor.bridgeConfined_sums h`。无 `1 ≤ h`、质量为正或全条带增长假设。空 confined 族和零质量均由有限支持求和与实数的原生除法处理。

证明先把真实横坐标界转为整数 column 界，再与有限 layer 区间组合成有限顶点类型。无重复的 confined 路径注入该有限类型上的 Nodup 列表；因此任何实值函数均有限支持。这使用官方 `inStrip`、`distinct` 和 `InLogCorridor`，不使用连接性或终点条件，也不使用任何未证的全条带计数或增长估计。

[完整验证源](ConfinedFiniteness.lean) 的 SHA256 是 `9dd59d27aa8ab3bec43bd0bd475153e2b52efa2f83a9b391f082a3c7f426d694`。[唯一原始运行回执](validation-01-result.json) 记录 Lean 4.34.1、固定 Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`、真实退出码 0、18.681 秒。11 个新定理的 [原始公理输出](validation-01.stdout.log) 均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。stderr 为空；stdout 保留不影响通过的 unused simp、letI 风格和 deprecated alias 提示。没有 sorry、admit 或新公理。

检查使用单 CPU、单线程与 32 GiB 内存，`maxHeartbeats=0`，无 wall/CPU/调用次数预算上限。本次归档没有重跑不变的 Lean 源；[完整性核对](integrity-check.json) 逐字比较验证快照，并核对 launch、result、来源片段与全部公理输出。

递送用 [HANDOFF.txt](HANDOFF.txt) 已内联完整的 `ExistingColumnCode.lean.inc` 与 `ConfinedFiniteness.lean.inc`。只需官方定义及 Mathlib；前者的 column 定义和 injectivity 已在旧包独立检验，按顺序附加两段即可。如果当前源码已存在同名且相同的 column 前提定义，应复用并跳过重复声明。宿主仍需独立验证 typed task 与正式集成。

[CanonicalDefinitions.lean.inc](CanonicalDefinitions.lean.inc) 是从自身固定规范源码逐字摘录的官方定义，不包含原题证明。既有辅助代码来源见 [provenance.json](provenance.json)；实际字节比对见完整性报告。没有读取发布方 ProducedSolution 或隐藏推理。

本包仅写入独立验证目录；未修改活动 runtime、源码、state、队列、manifest、缓存或全局配置，未 commit/push，也不代表 OpenAI 托管认证或本地原题最终验收。可交付文件由 [delivery-files.json](delivery-files.json) 和 [SHA256SUMS](SHA256SUMS) 完整列出。
