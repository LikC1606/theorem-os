Snaky V8 合并检查性能诊断（2026-10-24）

完整符号栈把当前调用者定位到 `decide +kernel → mkAuxLemma → addDecl → environment::add_theorem`。采样瞬间在释放 C++ 类型检查器缓存中的表达式引用；尚无证据支持保持当前链路不变即可实施的提速。此报告是辅助诊断，`official: false`，不构成 Snaky 最终验收。

证据区间与含义：

- 单次栈采样始于 08:51:11.808 UTC，热点线程 1659446 共 5580 帧，未截断。前 36 帧及前端调用者保存在 [stack-excerpt.txt](stack-excerpt.txt)，原始全线程栈见 [symbolized-stack-sample.json](symbolized-stack-sample.json)。
- 帧 0–3 是 `lean_dec_ref_cold`、表达式哈希表节点释放和 `type_checker` 析构；帧 4–22 进入定理加入内核、`mkAuxLemma` 和 `evalDecideCore.doKernel`。这描述的是内核检查调用内的引用计数回收，不能据此断定整个运行主要耗于回收，也不能据析构帧判定定理已成功。
- 所有采样线程中均无 `LibrarySuggestions`、`localSymbolFrequencyMap`、`foldRelevantConstants`、`writeModule`、`mkModuleData` 或 `computeExtEntries`。本次没有看到引理搜索元数据导出路径；单次采样不能描述未采样时段。
- 08:50:05–08:50:08 的 3.000059 秒窗口累计 3.00 CPU 秒，其中用户态 2.82 秒、系统态 0.18 秒；活动均在上述线程。该线程运行 2.999910 秒、调度队列等待约 61.7 微秒。证据见 [proc-three-second-cpu-sample.json](proc-three-second-cpu-sample.json)。
- 08:53:04 快照中没有 CPU quota/throttle、交换使用或主缺页，源 SHA-256 仍为 `dc40df160330f9058ff0af4e85adac6ed1be8be0b2d54c7fba5f10f71450eaae`。共享 cgroup 的历史 `oom_kill=1` 不可归因于此仍存活进程。见 [final-process-and-gate-snapshot.json](final-process-and-gate-snapshot.json)。

附加与释放已核实：GDB 附加 0.152315 秒，完整调用耗时 0.814187 秒，退出码 0，正常 detach；目标仍存活，`TracerPid: 0`。见 [symbolized-gdb-invocation.json](symbolized-gdb-invocation.json)。`perf` 仅尝试一次，被 `perf_event_paranoid=4` 拒绝；未更改 sysctl 或提升权限，见 [perf-attempt.json](perf-attempt.json)。

当前没有可据证执行的即时提速：单线程已取得接近完整的一核计算时间；本次不支持调度等待、交换或元数据导出是当前原因。固定 Lean 4.34.1 的 [Decide.lean](/home/lzh/.elan/toolchains/leanprover--lean4---v4.34.1/src/lean/Lean/Elab/Tactic/Decide.lean:104) 已通过 `mkAuxLemma` 使用按类型的模块内缓存，并同步交给内核检查。不能从这次记录推出增加 jobs 或修改缓存会有效。

离线可研究的点是证书规模与跨目标结构引理复用。静态文件有 718 处字面 `decide +kernel`，其中包括有限表结构正确性的检查；源码上下文及计数见 [source-static-context.json](source-static-context.json)。这些计数不能确定采样命中了哪个声明，也不能证明存在重复全表计算。压缩证书或共享结构不变量的收益尚未实现、测量或验证，只适合作为后续独立候选研究。

截至 08:53:04 UTC，原始 V8 目标已有通过回执，当前仍在合并任务的原生编译检查，尚无 `Submission.olean`。其后的声明查询、`task_integrated`、整体目标与 review、S3 和 publisher 验收仍待完成。Snaky 的最终验收数仍为 0。

本诊断只写入证据目录；未启动新编译，未改动候选、运行时、缓存、checkpoint 或参数，未停止或重启长进程。已有采样足以支持本报告，诊断在此收尾。

机器可读结论：[diagnosis.json](diagnosis.json)。
