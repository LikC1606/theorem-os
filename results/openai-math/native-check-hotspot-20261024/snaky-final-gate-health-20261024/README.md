# Snaky 最终验收健康检查

截至 2026-10-24T22:35:29.974902+08:00，运行正常，无需干预。固定版本复审已 accepted，宿主最终整文件内核重检仍在进行。尚无新的最终通过回执。

当前真实编译进程是 PID 543389，开始于 2026-10-24T13:50:30.645089+00:00。两次观测间隔 82.86 秒，CPU 增加 82.87 秒，约为单核的 100.0%。内存 9.61 GiB，地址空间限额 32 GiB。Lean 的主线程处于 futex 等待，但工作线程运行、进程 CPU 持续增加；这不是死锁证据。该阶段为 CPU 密集计算，采样间磁盘 I/O 不变。

只发现一个属于该运行的活动 Lean 编译进程和一次 evaluation_started。复审后那次 proof_checked 只花 28 ms，reused=true，没有再次编译。当前独立宿主检查是原有 S3 验收边界。

后续顺序为：完成整文件内核及声明/公理检查，核对 commit/sourceDigest；随后执行冻结的 publisher 构建 `lake build Challenge Submission`，再执行官方 comparator；最后持久化终态。publisher 使用干净副本，后续再次构建 Submission 是该旧运行已冻结的既定行为，可能继续耗时。未跳过或改动这些门。官方 comparator 在本机执行，不等于 OpenAI 托管认证。

宿主 workspace、canonical worktree 和当前最终 sandbox 的 Submission 均为 967683 字节，SHA256 全为 `dc40df160330f9058ff0af4e85adac6ed1be8be0b2d54c7fba5f10f71450eaae`。五项预算均为 0。未重启、kill、调用编译器，未修改活动 runtime、state、源码、回执、配置或预算；未读取 ProducedSolution 文件或隐藏推理。

证据：[report.json](report.json)、[前次进程采样](process-before.json)、[后次进程采样](process-after.json)、[公开事件索引](events-index.json)、[公开事件原行摘录](events-safe-excerpt.jsonl)、[验收代码索引](gate-source-index.json)、[冻结验收命令](frozen-evaluator-command.sh)、[源身份](source-identities.json)、[资源限制](lean-resource-limits.txt)。
