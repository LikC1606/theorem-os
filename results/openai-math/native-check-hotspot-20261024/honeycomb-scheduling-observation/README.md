# Honeycomb 条件归约的提交与调度核查

`sums_reduction` 没有丢失已经验收的证明。此前 worker 提交了研究事件，真正的归约源码另存于 context checkpoint，尚未通过该任务的原生 typed proof 验收。本次已通过正常 human edit 队列把既有条件归约交给 engineer 正式提交；编辑已应用，数学验收仍待运行结果。

## 已核实的证据

- 原任务本身已是精确的 `H → FiniteBridgeSums`，其中 `H` 是按宽度的严格指数增长界。`kind=lemma`、`conditional=true`、`dependsOn=[]`，原 type preflight 为 `elaborated`。无需修改数学陈述。
- 原始 delivery 是 `kind=research`、`conclusion=inconclusive`，没有 `commit` 或 `sources`。它关于原目标尚未解决的陈述是合理的，但不能替代条件归约的 typed proof 提交。见 [原始事件](raw-research-delivery.jsonl)。
- 此研究事件固定到 `d854a7623b1ca7e601966efdf3bd847b7d0d1f8c`；其 `Submission.lean` 是 2,367 字节的 seed，SHA256 为 `6acaeab1940555d1df29856e504deae4f9edf7777231969b9b7d13515731d830`，没有归约 theorem。事件的 artifact 列表和 reported checks 都为空。
- 随后的 checkpoint `0e6ec0cfff4aceb912de8009331ed5ca3ea4d794` 保留了 8,813 字节的 [归约源码](retained-reduction.lean)，SHA256 为 `6f81ffc481e22c8a189ced1d0de1d154c39e0edc57f17e9c1f492a271139f6e2`。第 183 行 theorem 的文本接口匹配任务，原目标仍有唯一 `sorry`。
- [worker notes](retained-worker-notes.md) 报告了本地检查通过及标准公理审计。这些属于 worker 报告；本次没有将其当作原生 TaskProof 回执，也未重新启动 Lean。
- 观察前 state 中唯一通过的 TaskProof 是 `initial_goal_1` 的两输入条件装配，仍依赖 `strip_growth_below_mu` 和 `sums_reduction`，不能证明这两个输入已经完成。完整摘录见 [初始观察](observation.json)。
- 运行从第 44/45 轮继续到第 49 轮，`blockers=[]`，原生已请求 `advisory-no-durable-progress` 恢复。没有证据表明已验收 proof 被丢弃，也不能仅凭 pending 判定运行死锁。

## 正常队列推进

父代理明确授权将此缺口通过最小 human edit 交回正常运行流程。已先检查当前冻结构建的协议：`queueRunEdit` 把完整 plan 追加到 `edits.jsonl`，由 `edits.lock` 和 `baseVersion` 比较交换保护；它不是局部任务 merge。因此提交从当前图复制全部 6 个 task、原 groups 和 proof routes，只改以下字段：

- `sums_reduction.ownerId = engineer`。
- `sums_reduction.revision: 0 → 1`。
- 补充 objective：在新 assignment 中从上述固定 Git checkpoint 还原精确源码，确认 SHA 和字节数，然后通过普通 completed proof delivery 交原生 typed checker；此条件蕴涵的提交不再因其 antecedent 尚未无条件证明而报 inconclusive。

`kind`、`type`、`theoremName`、`proofPath`、`conditional`、`dependsOn` 和所有其他 task 对象均保持。loader 仅放入 objective，由正常 worker 在新 assignment 中执行；本次没有直接覆盖活动源码。Git 对象已确认在 engineer 的仓库可读，无需压缩 source payload。

准备和执行记录：

- [执行脚本](queue-conditional-reduction.ts)。
- [dry-run 与准备记录](human-edit-preparation.json)：验证通过，载荷 5,164 字节，真实 delivery reader 可读取；loader 在证据目录 fixture 中恢复了逐字节相同的源码。
- [完整 proposal](human-edit-proposal.json)。
- [正式队列回执](human-edit-queue-receipt.json)：`queued`，编辑 ID 为 `honeycomb-sums-typed-6f81ffc481e2-r1-664d9664`。
- [运行回读](post-queue-observation.json) 和 [应用后不变量检查](applied-invariants.json)：编辑为 `applied`，plan version 为 `77b7d42ad95450f1f0547b09e9f8d1e72caaf4e33e0ce14c53daf16cbc8246bc`；原题、冻结构建、全部 6 个 task 及其顺序、其他任务对象、groups/routes 均核实保留，队列中仅一条本编辑。

objective/revision 的变动按原生规则使归约及两个下游旧版本失效：`sums_reduction`、`initial_goal_1`、`frontier_input_a566b95879bcff8e245ce923826d7c6ed33fcb51`。原两输入条件装配的旧回执留作历史证据，新版本需要重检。这是正常版本传播，没有删除任务或回填完成状态。

2026-10-24 07:31:58 UTC 的回读为第 53 轮：归约 owner 为 engineer、revision 为 1，状态 pending，尚无新 assignment、TaskProof 或 integratedCheck；编辑 recheck 仍 pending。后续应观察正常 engineer dispatch、typed proof receipt 和 integration。`strip_growth_below_mu` 仍是原目标路线中未解决的数学输入；本次没有把条件归约当作原题无条件解。

除正式调用 `queueRunEdit` 追加正常编辑外，新文件均位于本证据目录。未直接写活动 state 或源码、未发进程信号、未启动额外 Lean 或模型、未读取发布方 ProducedSolution。
