# 两条在途原生检查的调度调整

2026-10-24：已将 SnakyConditional 的 Lean 进程安排到 CPU 80–87，CharacterVarieties 安排到 CPU 16–23。两组分别位于对应进程主要匿名内存所在的 NUMA 节点，各组共享 L3 缓存。原调度快照、进程启动身份、源码 SHA、资源限制和实际读回保存在 `locality-receipt.json`。

| 检查 | 调整前 20 秒内 CPU 迁移 | 调整后 20 秒内 CPU 迁移 | 调整后 CPU 时间 |
| --- | ---: | ---: | ---: |
| SnakyConditional V8 | 0 | 0 | 20.0001 秒 |
| CharacterVarieties V12 固定点 | 3 | 0 | 20.0012 秒 |

这只证实调度设置已生效、两条检查仍持续使用约一个核心。CPU 迁移和 CPU 时间不能证明数学检查吞吐提升，尚无整题提速倍数或完成时间估计。两个检查进程继续运行，32 GiB 地址空间限制保持原值，源码及冻结 runtime/state 未修改。

`apply-locality.py` 已实际执行成功；它在修改前核对精确源码、进程启动身份和限制，修改后读回全部线程的设置。必要时可在本地执行 `/usr/bin/python3 apply-locality.py restore`，仅恢复仍具有相同启动身份的进程；不要对归档副本运行应用操作。

辅助源码试验也已收敛：Character 的局部 `irreducible` 对照为 42.762 秒，先前原写法为 42.661 秒；Snaky 的 15-helper 闭包 `def`/`opaque` 对照为 3.656/3.622 秒。均未显示足以采用新候选的收益，没有因此重启正式检查。小闭包通过不构成整题或原生最终验收。

后续仍使用现有严格缓存。Character 的固定点源码为候选检查与集成复用提供了源码条件，实际命中待回执；Snaky 当前候选与合并结果相差空行，不能据此复用为同一源码。首次全部目标检查、独立 S3 和原 publisher comparator 继续按既有标准执行。固定复审后的成功对象复用要求同一进程和完全相同的 commit，不能只比较 Submission 的 SHA。

截至本记录，原生最终通过仍为 5 题；SnakyConditional 和 CharacterVarieties 无新增最终通过回执。Honeycomb 在新构建上持续求解，两项关键引理仍未关闭。五项求解预算保持无限。

原始证据：[调度测量](locality-receipt.json)、[当前运行与五项预算](status-summary.json)、[Snaky 配对试验](source-trials/snaky/paired-probe.json)、[Character 试验](source-trials/character/opaque-helper-diagnosis.json)。`SHA256SUMS.json` 覆盖本包其余 16 个文件。
