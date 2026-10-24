# Snaky V8 原目标与集成源码身份核对

原目标 `712ecd…` 与实际集成 `dc40df…` 的差异**恰好是删除 1,101 个只含 LF 的空行（共 1,101 字节）**。15,263 行非空源码的全部字节（含缩进和行末 LF）及顺序完全相同；没有新增行、非空内容变化或缩进变化。源码不含双引号字符串或块注释，因此这些空行不可能位于跨行字符串或块注释内。

所有声明名称、类型、证明体以及 namespace/section/open/end 命令的源码均一致（仅省去空行）。复用的冻结 `canonical-v8-native-merge-projection-receipt.json` 已记录全限定声明序列相同、原冻结 merge/projector 未变及源保护通过；实际正在编译的源码与其 merged/projected 输出逐字节一致。本次没有再运行 parser 或 Lean。

原目标原始事件 `check.kernel_checked` 明确记录 `exitCode=0`、`durationMs=8072025`、`timedOut=false`、`aborted=false`。原生日志在 2026-10-24 06:55:01.632 UTC 确认 `task_checked: passed=true`，06:55:01.647 进入集成队列；06:59:54.784 UTC 的只读观察已发现正在编译 `dc40df…` 的新 Lean PID 1659442（保持原 32 GiB 上限）。

本证据只确认源码差异与原目标成功，尚未授予集成或最终验收通过。没有改动活动链、运行时、缓存、checkpoint 或源码，也没有启动新编译。详细字节身份、删除行号及已有回执引用见 `original-integration-static-identity.json`。
