# Honeycomb 高度一的六项正式集成回执

`width_one_bridge_sums_b433299a` 已通过独立原生 TaskProof 检查与 canonical 集成检查。正式定理 `OAI.PolynomialVacuumBridge.Corridor.finite_bridge_sums_at_one` 在高度 1 证明完整 BridgePath 与 ConfinedBridgePath 的 weight、firstLengthWeight 和归一化 firstLengthWeight 六项可求和。

原生证明回执为 `lean-b1c75a2ef3a0363767a6edd9`，耗时 21.382 秒；集成回执为 `lean-909381d19f6680c1615fba09`，耗时 18.179 秒。两项均 kernel_verified、exit 0、无 timeout/abort，sorry/admit/goals 全为 0，无 conditions，仅依赖 propext、Classical.choice、Quot.sound。

proof commit 为 `3c08cbf9e691e7156540ed075ffc3de20edb6652`，集成 canonical commit 为 `78602bd19dc2708c16543e3fe55edfe8407a8824`。[proof 公开源码](proof-source/Submission.lean) 与 [集成公开源码](integrated-source/Submission.lean) 由对应精确 commit 的 git show 只读取出，22 个新增声明均存在，官方定义未改变。

本次两份宿主回执未提供 references/declarationReferences，stdout 的 DS_DECL_REFERENCES 标记为 null；因此不能像 prior confined 包一样核对根 reference SHA。两份源码 SHA、sourceDigest、proofHash 与验证 targetCommit 分别保存在 [verification-summary.json](verification-summary.json)，不混称它们相等。正式回执仍具有 caller-bound-to-committed-declaration 绑定、精确 statementHash 和原生内核通过状态。

[task-record.json](task-record.json) 冻结完整对应任务记录。两份原始 verification JSON、原生公理输出、[raw 安全宿主事件](events-safe-raw.jsonl)、[事件索引](events-index.json) 和 [身份摘要](identity.json) 提供可复查证据。该任务只依赖已集成的 sums_reduction，没有假设未证的全高度 strip_growth_below_mu，也未在新增声明中调用原目标。

本结果只证明高度 1 的六项结论。全高度 confined 三项已有集成状态仅记录于 [confined-status-only.json](confined-status-only.json)，完整证据保留于先前冻结包。完整原题 initial_goal_1 仍 conditional/未解，一般高度完整 BridgePath 的前三个子句缺口仍在；此结果不属于 OpenAI 托管认证。

本次只在这个新包冻结已有正式证据与公开 git 源码，没有重编 Lean、修改活动源码/runtime/state/队列/缓存/配置或旧包，没有编辑结果库顶层 README/manifest，也没有 commit/push。[delivery-files.json](delivery-files.json) 与 [SHA256SUMS](SHA256SUMS) 列出精确交付。
