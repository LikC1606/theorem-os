# Honeycomb 相邻列唯一性与列 word 单射

本轮两个 bounded 几何任务已完成：给定当前顶点，邻接后继由其列号唯一确定；固定规范起点后，完整列号序列对 `BridgePath h` 是单射。四个声明真实 Lean 内核检查 exit=0，耗时 2.657527851872146 秒，结束时间 2026-10-24T12:53:53.187541+00:00，stderr 为空、stdout 无警告，公理均精确为 propext、Quot.sound，无 sorryAx。本包冻结于 2026-10-24T12:55:41.881353+00:00。

可递送的共享 objective delta 见 [HANDOFF.txt](/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/honeycomb-column-word-followup-20261024/HANDOFF.txt)，新增源码见 [ColumnWordInjection.lean.inc](/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/honeycomb-column-word-followup-20261024/ColumnWordInjection.lean.inc)，独立验证 harness 见 [ColumnWordInjection.lean](/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/honeycomb-column-word-followup-20261024/ColumnWordInjection.lean)。这里只给局部内核证据，尚非 TaskProof 或原题正式验收。没有向队列写入，递送由主代理串行处理。

| 定理 | 接口 |
|---|---|
| `bridgeAdjacent_unique_of_column` | `adjacent u v → adjacent u w → bridgeBoxColumn v = bridgeBoxColumn w → v = w` |
| `bridgeChain_tail_eq_of_columnWord` | `(root :: vs).IsChain adjacent → (root :: ws).IsChain adjacent → vs.map bridgeBoxColumn = ws.map bridgeBoxColumn → vs = ws` |
| `bridgeVertices_eq_of_columnWord` | `bridgeColumnWord p = bridgeColumnWord q → p.vertices = q.vertices` |
| `bridgeColumnWord_injective` | `Function.Injective (bridgeColumnWord (h := h))` |

唯一新增定义为 `bridgeColumnWord p := p.vertices.map bridgeBoxColumn`。从规范 adjacency 的每个分支可知当前点的三个邻点列号不同；然后用 IsChain 对列表归纳重建全部顶点。BridgePath 的其它字段是证明，列表相等即可推出对象相等。这个单射不需要 Nodup、inStrip 或任何增长/质量假设。

边界：编码必须给出完整整数列 word，或另证其能确定该 word，才能使用本单射。不能由此直接认定有限 cut-state 编码、transfer 接受语言或 count/weight 恒等式已成立。uniform finite-box 总质量界与严格 sub-μ 增长仍未提供；此前矩阵与列基数辅助包保留原样，无重复证明。

工具链 Lean 4.34.1，Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`，只读 sealed environment `2d808da67c8ab8ad74458d8a53ecc2ee8da9c63a825e0429439ebf56a9a78c87`。真实命令 `lean --threads=1 --memory=32768 -DautoImplicit=false -DmaxHeartbeats=0 -DmaxRecDepth=1000 ColumnWordInjection.lean`，固定单核；32 GiB、单线程（-j1）、maxHB=0，无 wall/CPU/invocation cap。来源为既有冻结规范片段；未读 ProducedSolution/隐藏推理，未改活动代码、state、缓存或 runtime，未使用 Git 或队列。

完整 source SHA256 `bcb5c4ca45ff3d4298f3ff8a0f0325856334ab167dcd33279877a3de0138c04b`（4970 bytes）；increment SHA256 `2b0c4f2a47ae6a95e6a229b57bfc6281282945ad123eb8ff39f8f542c431fb0e`（3315 bytes）；最终 validation-result SHA256 `6e7a0ddbd33dc082c76c0677922b630b8d5695c09ac090ad763b7775dfd4a2a3`。source 与保存的 final-source 快照和 launch/result SHA 已匹配，四项公理打印与定理名逐项匹配。第一次调用真实 exit=1，只因列表证明的 API 名称和冗余 rewrite；诊断全部保留，最终调用 exit=0。

交付索引 `delivery-files.json` 列出 payload 的完整绝对路径、字节数与 SHA256；`SHA256SUMS` 校验所有其它文件，包括索引自身。验证命令：

```sh
cd /home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/honeycomb-column-word-followup-20261024
sha256sum -c SHA256SUMS
```

完整文件清单：

- `CanonicalGeometry.lean.inc`
- `ColumnWordInjection.lean`
- `ColumnWordInjection.lean.inc`
- `HANDOFF.txt`
- `README.md`
- `SHA256SUMS`
- `assemble.py`
- `delivery-files.json`
- `lean-toolchain`
- `provenance.json`
- `result.json`
- `validate.py`
- `validation-01-launch.json`
- `validation-01-result.json`
- `validation-01-source.lean`
- `validation-01.stderr.log`
- `validation-01.stdout.log`
- `validation-02-final-launch.json`
- `validation-02-final-result.json`
- `validation-02-final-source.lean`
- `validation-02-final.stderr.log`
- `validation-02-final.stdout.log`
