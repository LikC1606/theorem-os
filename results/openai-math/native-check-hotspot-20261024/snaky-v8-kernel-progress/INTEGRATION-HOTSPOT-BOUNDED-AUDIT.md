# Snaky V8 当前集成热点：有界只读核查

截至 2026-10-24T07:53:46.447675+00:00，Snaky 仍等待原生 **合并任务检查**：PID 1659442 正运行 `lean -j1 -R . -o .lake/build/lib/lean/Submission.olean Submission.lean -j1`。实际沙箱副本与集成投影均为 `dc40df160330f9058ff0af4e85adac6ed1be8be0b2d54c7fba5f10f71450eaae`（967,683 字节），原 32 GiB 地址空间上限保留。尚无 `Submission.olean`；父 shell 尚在等此编译，之后的 declaration 查询还没执行。

单次 GDB 短采样用时 0.133 秒，已正常 detach，`TracerPid: 0`。调试器无法自动加载命名空间内的 executable，故仅得浅栈；按匹配的共享库 inode 与 ELF 虚拟段偏移离线解析，工作线程顶部为 Lean C++ `instantiate_lparams` 的表达式遍历和宇宙参数 `instantiate`。**没有采到 `LibrarySuggestions → localSymbolFrequencyMap → foldRelevantConstants` 导出链**。这些底层函数也可能被更高层调用，浅栈不足以判定完整上层阶段，不能据此把 Snaky 归因于 Character 的同一元数据热点，也不能说证明已经检查完成。

原生日志仍止于原目标 `task_checked passed=true` 后的 `integration_queue_started`；没有新 `task_integrated`、`evaluated_passed` 或 publisher 成功回执。当前 `result.json` 仍是 startup-only 的 prepared/skipped 记录，并非最终失败。尚须本关通过后继续 whole-target、固定审查（按原生流程）、独立 S3、原 publisher build/comparator 及监督进程完成。

只读扫描了 256 个正式 verifier 缓存文件，无解析错误；只发现三个历史/当前原目标 Snaky 结果，**没有 `dc40df…` 的成功整题回执**。原目标 `712ecd…` 回执绑定不同字节、任务身份、commit 和 project root；静态合并/预检和 focused probe 回执均不能冒充本关。未发现可按当前协议省去本关的现成真实回执。

没有启动重复编译、终止进程，或修改活动源码、runtime、cache、checkpoint。本次只归档状态、既有事件、单次短采样及其离线符号解析。
