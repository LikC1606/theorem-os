# Hadamard 矩阵三次纤维上的行比值消去

完整原题 OAI.HadamardSix.rowRatio_cubeFiber_sum_zero 已通过 Lean 内核、原版源码保护检查及真实隔离发布方比较器，exit 0，stderr 为空。原定义、声明和上下文保持。

由 H 与逐项平方矩阵的 Hadamard 条件得到行比值一、二次矩为零；单位模给出逆矩，再以两种三次值构造纤维投影恒等式求和消去。无 sorry/admit，公理仅 propext、Classical.choice、Quot.sound。

- [Submission.lean](Submission.lean)：独立比较器通过的候选源码。
- [NativeSubmission.lean](NativeSubmission.lean)：TheoremOS 原生最终接受的精确源码，SHA 与候选分别记录。
- [原生验收回执](evidence/native-acceptance-update.json)：固定审阅、全原目标内核复核和发布方比较器全部通过。
- [Challenge.lean](Challenge.lean)：冻结原题，占位 sorry 保留。
- [verification.json](verification.json)：范围、精确 SHA 和归因。
- [provenance.json](provenance.json)：手稿 266-02 与上游身份。
- [内核回执](evidence/kernel-axiom-receipt.json)、[源码保护回执](evidence/source-guard-receipt.json)、[比较器回执](evidence/sealed-comparator-receipt.json)。
- [manifest.json](manifest.json)：文件大小和 SHA。

2026-10-23 03:14:47 北京时间，原 comparator 输出 Lean default kernel accepts the solution 与 Your solution is okay!。仅适配 Challenge/Submission 模块名，目标和许可公理不改，Nanoda 未启用。固定 Lean v4.34.1、Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612。

2026-10-23 03:39 北京时间，TheoremOS 原生最终状态 evaluated_passed，campaignAcceptance=true。接受 commit 为 be3ac1e85859e7f88229dd3eab02a492b9ca2d5a，原生源码 SHA-256 为 d818e4c8217e53057b254f92285bb22930f2b47504ed68d7e8def9d2547fa3a1；模型将外部辅助证明内联，故与独立候选字节不同。

这是外部辅助证明经原生系统集成和最终验收的成果，不算 deepseek-flash 单模型从零成绩，也不是 OpenAI 托管验收。C 档为本项目判断。

复验依次执行 LEAN_NUM_THREADS=1、lake exe cache get、lake build Challenge Submission、lake env lean AxiomAudit.lean。[隔离命令](run-sealed-comparator.sh) 需要固定 comparator、可信依赖与 TheoremOS 沙箱预备。内核回执的审计源码含公理打印，实际 Submission SHA 单列于源码保护回执。

原题和配置按 [Apache-2.0](LICENSE.openai-math) 保留许可，变更见 [NOTICE](NOTICE)。未读取已发表解答。
