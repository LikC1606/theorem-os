# Honeycomb 固定高度四的无条件可求和性

已在官方定义不变时证明 `Summable (weight (h := 4)) ∧ Summable (firstLengthWeight (h := 4))`。精确定理为 `OAI.PolynomialVacuumBridge.Corridor.width_four_summability_diagnostic`。这是固定高度四的结果，完整全高度原题仍未解决。

证明用八类顶点的真实邻接关系，核验 22 类有向入边的一步势能不等式。势能取整数 29 至 64，比较率 β=1847/1000。随后对有限 continuation 枚举做归纳，得到 card≤edgeWeight·βⁿ；canonical BridgePath 4 的 connectedness、Nodup、source、terminal 和 inStrip 保证每条真实路径被覆盖，有限路径族因此满足 card≤128·βⁿ。精确有理数与平方根比较证明 β<2cos(π/8)，已有无条件计数到一阶可求和性助手给出结论。没有展开 14 步树，也没有把 Python 证书作为公理。

[最终真实回执](summability-02-final-result.json) 记录 Lean 4.34.1、固定 Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612，退出码 0，耗时 11.999551 秒。[最终源](WidthFour.lean) SHA256 为 `a8462a1922c107fde21cde91cb10c505f57860c5d926b3bb30df2869cd804e91`。12 个关键定理的 [原始公理输出](summability-02-final.stdout.log) 均只有 propext、Classical.choice、Quot.sound；没有 sorry、admit、新公理或 native_decide。stderr 为空，保留 1 条无影响的 unnecessarySimpa 风格提示。首轮仅因 beta 缺 noncomputable 的代码生成错误失败，原日志完整保留。

检查使用单 CPU、单线程和 32 GiB，maxHeartbeats=0，无 wall/CPU/调用次数预算上限。[完整性报告](verification-audit.json) 核对 source、launch、result、源快照和增量字节；归档没有重跑不变源。

递送入口：[native-task-proposal.json](native-task-proposal.json)、[delivery-contract.json](delivery-contract.json)、[HANDOFF.txt](HANDOFF.txt)。后两者内联完整已核验增量。只需把 [WidthFour.lean.inc](WidthFour.lean.inc) 插在 canonical namespace 的两个既有无条件 counting-to-summability 助手之后；这些助手来自已集成 sums_reduction。[dependency-snapshot.json](dependency-snapshot.json) 记录当前状态和无重名核对。完整 harness 含规范定义与既有 reduction，只用于独立验证，不能替换活动 Submission.lean。

[certificate-input.json](certificate-input.json) 保存父任务提供的精确 h4 有理数证书及来源 SHA，新增 Lean 证明独立核验全部邻接行、归纳和路径联系。[provenance.json](provenance.json) 记录复用 h2 模板和固定依赖的来源。没有读取发布方解答或隐藏推理。

本包没有触碰活动 runtime、源码、state、队列、缓存、旧包、h3 工作或结果库顶层，没有模型调用、commit/push。这里只具有本地 Lean 核验，正常 native TaskProof 与集成仍需宿主执行，不代表 OpenAI 托管认证。[delivery-files.json](delivery-files.json) 与 [SHA256SUMS](SHA256SUMS) 给出精确清单。
