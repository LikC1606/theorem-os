# Honeycomb exact typed task adapters

本包把已冻结验证的 column-word helper 包装为现有两个 typed task 的原始完整类型。`exact-type-check.json` 逐字核对任务快照、生成的 theorem header 和 type SHA256。

`ColumnTaskAdapters.lean.inc` 只包含两个包装。将它追加到同 namespace 中的已验证 helper 之后；不要用完整验证 harness 替换活动 `Submission.lean`。前置 helper 位于 `honeycomb-column-word-followup-20261024`；本包保存原始 harness 的只读副本 `ColumnWordInjection.base.lean`。

真实 Lean 4.34.1 检查第一次即通过，Mathlib pin 为 d13f23b723b8a846827a245b89c10fc7d3f11612。两条新 theorem 公理均仅 propext、Quot.sound，无 sorryAx。详细退出码、计时和资源限制见 `validation-01-result.json`，完整输出见两个 log 文件。

本包仅提供两个辅助任务的本地内核证据，尚未通过 native TaskProof 流程。Honeycomb 原题的 strict sub-mu growth、uniform finite-box mass 和 exact transfer identity 仍未证明。旧包、活动 state、源文件和队列均未改动；由父代理通过正常队列串行递送。
