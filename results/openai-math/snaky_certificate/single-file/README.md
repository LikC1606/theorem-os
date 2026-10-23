# 单文件提交版与原比较器通过证据

`Submission.lean` 是原隔离流程验收的完整单文件，SHA-256 为 `87a3c359ef740fe32fe1ac2fda0216d708421163bc04194aa48ca8be0d742cdb`，901,417 字节，保留原 Challenge 定义与目标。文件使用外部代理辅助完成。

2026-10-23 08:13:38 UTC，完整构建、独立目标公理检查和原比较器在固定 Lean / Mathlib、32 GiB 地址空间限制、单 CPU、无时间上限的隔离环境中自然 exit 0。输出包含 `Lean default kernel accepts the solution` 和 `Your solution is okay!`，公理仅 `propext`、`Classical.choice`、`Quot.sound`。七项原源码与容量保护均通过。

`isolated-evaluator-serial-entrypoint.sh` 保留实际验收命令；其中串行编译参数为 `-j1 -DElab.async=false`，原比较器与目标配置保持不变。`SubmissionCanonicalV2Audit.lean` 是独立公理检查输入。原始配置、入口命令、源码和 Challenge 的 SHA 均记录于 `../evidence/canonical-v2/sealed-canonical-v2-comparator-receipt.json`；该回执保留完整 stdout/stderr。其余回执与资源采样保存在同一目录，回执内运行路径指向原始任务工作区。

本结果证明本地完整隔离原比较器通过。TheoremOS 原生交付与最终验收仍待完成，OpenAI 托管接受尚无确认。

后续 `SubmissionCanonicalV5.lean` 的 SHA-256 为 `66d0cf5eecbcffcf0de7933acaec1c16da6f5ba8592173e1e9228c350663fdd7`，898,691 字节。该版本通过冻结原比较器和同源宿主检查；正常原生目标检查亦通过，条件列表为空、公理仍为标准三项。原始回执保存在 `../evidence/canonical-v5/`。

正常集成只删除空行，得到 `SubmissionCanonicalV5Integrated.lean`，SHA-256 为 `b7dc0b2898b8d4ee8ed4a3b10394429f939ff9e4d73761dcd6968e46a4579751`，896,495 字节。该源码已通过原生集成和全部原目标检查，固定版本复审正在运行，尚无原生最终通过回执。
