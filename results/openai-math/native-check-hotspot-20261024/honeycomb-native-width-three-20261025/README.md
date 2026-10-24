# Honeycomb 宽度 3 原生集成回执

`width_three_summability_e0dd3d96` 已通过原生 TaskProof 和 canonical 集成检查，无条件证明宽度 3 的完整 BridgePath weight 与 firstLengthWeight 两项可求和。

证明回执 `lean-4bae72d27c6d83d9d29474cd` 耗时 25.788 秒，集成回执 `lean-57bf5d70cc019e03fa3fba3d` 耗时 27.590 秒。两项均 kernel_verified、exit 0、无 timeout/abort，目标 sorry/admit/goals 全为 0，无 conditions，仅有 propext、Classical.choice、Quot.sound。

proof commit 为 `c9c9dba2430cca6189a64793f620e1d9530ac12c`，integration commit 为 `7061be826cef83e4924ebda357f35164fa97ddb8`。精确 commit 的 [证明源码](proof-source/Submission.lean) 和 [集成源码](integrated-source/Submission.lean) 只读取自 git show。27 个新增声明全部存在，canonical 定义与前一冻结基准相同，新增声明未调用未证原目标。

两份回执均未提供 references/declarationReferences，stdout 的引用标记均为 null。 不宣称公开整文件 SHA 等于 host proofHash，也不宣称已核对根 reference SHA。[verification-summary.json](verification-summary.json) 分别记录公开源 SHA、sourceDigest、proofHash、sandbox targetCommit、精确 statementHash 与 caller-bound-to-committed-declaration 绑定。

本结论只覆盖固定宽度 3。原题 initial_goal_1 仍 conditional/未解，公开整文件仍保留原题 sorry；零 sorry 仅指本辅助目标及其实际依赖闭包。本结果不是 OpenAI 托管认证。

[任务记录](task-record.json)、原始 verification JSON、公理输出、[安全原生日志](events-safe-raw.jsonl)、[事件索引](events-index.json)、[身份](identity.json) 与 [工具链身份](toolchain-provenance.json) 保留完整证据。本次未重跑 Lean、未改活动 state/source/runtime/cache/队列/配置、旧包或结果库顶层 README/manifest，未 commit/push。[delivery-files.json](delivery-files.json) 与 [SHA256SUMS](SHA256SUMS) 提供精确交付清单。
