# Honeycomb 宽度二的原生集成回执

`width_two_summability_diagnostic` 已通过原生 TaskProof 与 canonical 集成检查。定理 `OAI.PolynomialVacuumBridge.Corridor.width_two_summability_diagnostic` 无条件证明宽度 2 的完整 BridgePath 的 weight 与 firstLengthWeight 两项可求和。20 个新增声明还给出有限路径计数上界 `4 * (sqrt 3)^n`，并证明 `sqrt 3 < 2 * cos (pi / 8)`，供既有可求和约化使用。

原生证明回执为 `lean-30a9b8d0f88ea68d0cdfffd7`，耗时 23.908 秒；集成回执为 `lean-280acb880d3c011f61e534da`，耗时 24.130 秒。两项均 kernel_verified、exit 0、无 timeout/abort，目标的 sorry/admit/goals 全为 0，无 conditions，只依赖 propext、Classical.choice、Quot.sound。

proof commit 为 `a862efb5ee31eaf58ca174b79730f960a7b89302`，集成 commit 为 `0d4bd1c55e8dff31f375e1d5dbe243c799489133`。[proof 公开源码](proof-source/Submission.lean) 与 [集成公开源码](integrated-source/Submission.lean) 来自对应精确 commit 的只读 git show。20 个新增声明均存在，canonical 定义与前一冻结基准一致，新增声明没有调用未证原目标。

两份宿主回执均没有 references/declarationReferences，stdout 的 DS_DECL_REFERENCES 标记为 null。因此不能独立核对根 reference SHA，也不宣称公开整文件 SHA 等于宿主 proofHash。两种 SHA、sourceDigest、验证 sandbox targetCommit、statementHash 与 caller-bound-to-committed-declaration 绑定分别保存在 [verification-summary.json](verification-summary.json)。精确 integration commit 的 Lean 4.34.1 和 Mathlib revision 保存在 [toolchain-provenance.json](toolchain-provenance.json)。

任务依赖数组为空；其公开证明使用 canonical 中既有的两个可求和约化辅助定理。该结论只覆盖宽度 2 的两项可求和，尚未证明所有宽度的增长界或完整原题。`initial_goal_1` 仍 conditional/未解，归档的整文件中仍保留该原目标的 sorry；零 sorry 的说法仅针对本辅助任务的实际验证目标及依赖闭包。本结果不是 OpenAI 托管认证。

[task-record.json](task-record.json) 冻结对应任务记录；两份原始 verification JSON、公理输出、[安全原生日志](events-safe-raw.jsonl)、[事件索引](events-index.json) 与 [身份摘要](identity.json) 保留核查证据。本次未调用 Lean、修改活动 state/source/runtime/cache/队列/配置、旧包或结果库顶层 README/manifest，未 commit/push。[delivery-files.json](delivery-files.json) 与 [SHA256SUMS](SHA256SUMS) 提供精确交付清单。
