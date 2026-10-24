# Honeycomb 列/slab 几何基数辅助定理

9 个独立辅助 theorem 已由真实 Lean 内核检查成功，actualExitCode=0，耗时 2.8644451410509646 秒，结束时间 2026-10-24T10:12:20.395376+00:00。它们是局部内核证据，尚非 native TaskProof 或原题正式验收。核心结论只用规范列表的 Nodup 和 inStrip：同一 layer 和 column 唯一确定顶点，所以长度不超过 `h × 占据列数`。每个 two-column slab 的列号为 `2k, 2k+1`，因此得到 transfer 所需的 `length ≤ 2*h*占据slab数`，并正确覆盖负整数列。

可直接加入现有共享 objective 的 delta 为 [HANDOFF.txt](/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/honeycomb-column-cardinality-followup-20261024/HANDOFF.txt)，含解释、缺口、证据与完整新增 Lean increment；不重复旧矩阵代码。合并增量见 [ColumnCardinality.lean.inc](/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/honeycomb-column-cardinality-followup-20261024/ColumnCardinality.lean.inc)，单独验证 harness 为 [ColumnCardinality.lean](/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/honeycomb-column-cardinality-followup-20261024/ColumnCardinality.lean)。只把 increment 加到正确 namespace 中，保留现有工作，不以 harness 覆盖 Submission.lean。

| 定理 | 接口/结论 |
|---|---|
| `bridgeLayerColumnCode_injective` | `Function.Injective bridgeLayerColumnCode` |
| `bridgeVertexList_length_le_columnSet` | `vs.Nodup → (∀ v ∈ vs, 0 ≤ layer v ∧ layer v < (h : ℤ)) → (∀ v ∈ vs, bridgeBoxColumn v ∈ columns) → vs.length ≤ h * columns.card` |
| `bridgeLength_le_columnSet` | `(∀ v ∈ p.vertices, bridgeBoxColumn v ∈ columns) → p.vertices.length ≤ h * columns.card` |
| `bridgeLength_le_columnInterval` | `(∀ v ∈ p.vertices, a ≤ bridgeBoxColumn v ∧ bridgeBoxColumn v ≤ b) → p.vertices.length ≤ h * (b + 1 - a).toNat` |
| `bridgeLength_le_columnBox` | `bridgeInColumnBox R p → p.vertices.length ≤ h * (4 * R + 2)` |
| `bridgeLength_le_slabSet` | `(∀ v ∈ p.vertices, bridgeBoxSlab v ∈ slabs) → p.vertices.length ≤ 2 * h * slabs.card` |
| `bridgeLength_le_occupiedSlabs` | `p.vertices.length ≤ 2 * h * (bridgeOccupiedSlabs p).card` |
| `bridgeColumn_natAbs_le_radius` | `v ∈ p.vertices → (bridgeBoxColumn v).natAbs ≤ bridgeColumnRadius p` |
| `bridgeLength_le_columnRadius` | `p.vertices.length ≤ h * (2 * bridgeColumnRadius p + 1)` |

`bridgeBoxSlab v := bridgeBoxColumn v / 2`，使用整数 floor division；`bridgeOccupiedSlabs p := p.vertices.toFinset.image bridgeBoxSlab`；`bridgeColumnRadius p` 为有限顶点列表 column.natAbs 的实际最大值。任意列区间结论比请求的 `2*h*宽度` 更强，不要求 `a ≤ b`，空区间由 `.toNat` 正确处理。

规范 Vertex、adjacent、layer、BridgePath 从冻结挑战逐字提取；已有 bridgeBoxColumn 和 bridgeInColumnBox 仅复制定义作为前提，未重做已通过的有限盒/矩阵定理。Harness 不含原题目标、sorry、admit 或新公理。所有 9 个打印结果只含 propext、Classical.choice、Quot.sound；注入定理仅含 propext、Quot.sound。最终 stdout 无 sorryAx，stderr 为空。

工具链固定 Lean 4.34.1，Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`，读取先前建立的只读 sealed packages，identity `2d808da67c8ab8ad74458d8a53ecc2ee8da9c63a825e0429439ebf56a9a78c87`。真实调用为 `lean --threads=1 --memory=32768 -DautoImplicit=false -DmaxHeartbeats=0 -DmaxRecDepth=1000 ColumnCardinality.lean`；`--threads=1` 对应单线程 `-j1`，并固定单核。地址空间 32 GiB，无 wall/CPU/invocation cap。未改活动 runtime/state/源码，未使用队列，未执行 Git、commit 或 push，未读 ProducedSolution、隐藏推理或凭据。

当前数学缺口仍为 uniform finite-box 总质量界或等价实质输入，以及精确 transfer 编码与 count/weight 恒等式。若 transfer 编码给出包含路径所有顶点的 k 个 slab，可用 `bridgeLength_le_slabSet`；若 k 等于实际占据 slab 数，可直接用 `bridgeLength_le_occupiedSlabs`。编码对应关系与质量可和性不由本包提供。

源码 SHA256：`4b28aaf9a6976f4985dee98f98da3fb58aa11d4b850268ac675761ffc8588fe2`（8085 bytes）；增量 SHA256：`c67b5cf4dabbaf84a7b3158406e055fc63442a404c6b9c16657a063e2cf2987f`（6180 bytes）；最终 Lean 结果 SHA256：`3e95a31d5b92302cbcfdfdef94e90adedfd833e9d7b227710d8e0e98af30aa5f`。最终 source、保存的 final-source 快照与 launch/result 的 sourceSHA256 已逐字核对，axioms 输出已与九个 theorem 名逐项匹配。第一次调用只有半径推论因精简导入中缺少 abs_le 接口失败，真实 exit=1；全部诊断保留，最终改为 Int.le_natAbs 后 exit=0。

包已冻结，主代理可串行递送 `HANDOFF.txt`。校验目录和命令：

```sh
cd /home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/honeycomb-column-cardinality-followup-20261024
sha256sum -c SHA256SUMS
```

若需在相同只读包仍可访问时重验，先执行 `/usr/bin/python3 assemble.py`，再以新的唯一 label 执行 `/usr/bin/python3 validate.py validation-newlabel`；实际 Lean 退出码记录在生成的 result JSON，不能将 Python wrapper 自身退出码当作数学验收。无重新运行要求。

完整文件清单如下；`delivery-files.json` 给出 payload 文件绝对路径、字节数与 SHA256，`SHA256SUMS` 检查所有其它文件，包括索引自身；两者不循环校验。

- `CanonicalGeometry.lean.inc`
- `ColumnCardinality.lean`
- `ColumnCardinality.lean.inc`
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
