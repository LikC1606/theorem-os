# Honeycomb 全高度 confined 三项正式集成回执

`confined_bridge_sums_all_heights_9dd59d27` 已通过独立原生 TaskProof 检查与 canonical 集成检查。正式定理 `OAI.PolynomialVacuumBridge.Corridor.bridgeConfined_sums` 对每个自然高度无条件证明 confined weight、firstLengthWeight、以及 firstLengthWeight/confinedMass 三项可求和。

原生证明回执为 `lean-14624c27faf85a6bc4e5a9f0`，耗时 20.285 秒；集成回执为 `lean-062ee507a3097c19b45fb262`，耗时 20.024 秒。两项均 kernel_verified、exit 0、无 timeout/abort，sorry/admit/goals 全为 0，无 conditions，仅依赖 propext、Classical.choice、Quot.sound。

proof commit 为 `5c383ba2ff4220cbb57aecb041127365d15ac35c`，集成 canonical commit 为 `fa3012608614475df88d051503ad0cdaaf8f4be6`。两份 [proof 公开源码](proof-source/Submission.lean) 与 [集成公开源码](integrated-source/Submission.lean) 均由精确 commit 的 git show 只读取出，SHA 与各自正式 references 根源文件摘要一致；官方定义未改变。[verification-summary.json](verification-summary.json) 区分 proof commit、沙箱验证 targetCommit、sourceDigest 与文件 SHA，避免混用身份。

[task-record.json](task-record.json) 冻结完整对应任务记录，含正式 proof、integratedCheck、全部来源与依赖。两份原始 verification JSON、原生公理输出、[raw 安全宿主事件](events-safe-raw.jsonl)、[事件索引](events-index.json) 和 [运行身份](identity.json) 可相互核对。原始任务记录包含较长 reference 列表，摘要没有据此扩大数学结论。

这只关闭全高度 confined 的后三个辅助子句。完整原题 initial_goal_1 仍 conditional/未解，一般高度完整 BridgePath 的前三个子句缺口仍在。width-one 在本包截点仍 running，状态仅记录于 [width-one-status-only.json](width-one-status-only.json)，没有额外宣称其通过。此结果不属于 OpenAI 托管认证。

本次仅冻结既有正式证据和公开 git 源码，没有重跑 Lean、改活动源码/runtime/state/队列/缓存、修改旧 health 包或 commit/push。[delivery-files.json](delivery-files.json) 与 [SHA256SUMS](SHA256SUMS) 列出精确交付。
