# Truffet 优化过程的有限反例

完整原题定理 `OAI.TruffetV4Counterexample.finite_execution_not_optimal` 已获 Lean 内核检查及本地原发布方比较器通过。证明覆盖全部 13 项合取，包含 91 个辅助引理，无 sorry 或 admit；公理依赖仅为 propext、Classical.choice、Quot.sound。

这份记录是本地复验结果，尚无 OpenAI 托管或人工验收确认。D 档是本项目按研究难度给出的评价，OpenAI 没有官方 S–D 分档。未将此项加入仓库 accepted/ 或已送交 LeanEval 的 submitted/。

## 文件与证据

| 文件 | 内容 |
| --- | --- |
| [Submission.lean](Submission.lean) | 已验证证明的逐字节归档，572 行、26,256 字节 |
| [Challenge.lean](Challenge.lean) | 上游冻结原题；其中的 sorry 是待证明目标占位，刻意保留 |
| [provenance.json](provenance.json) | 上游提交、原题和配置 SHA-256、手稿 104-03 与目标映射 |
| [verification.json](verification.json) | 验证范围、模型和人工干预归因、归档时原生运行状态 |
| [内核回执](evidence/host-kernel-receipt.json) | 对此精确证明 SHA-256 的宿主检查、公理输出和完整目标类型 |
| [固定版本审阅](evidence/fixed-version-review.json) | 本地 reviewer accepted，原声明与保护文件检查摘要 |
| [隔离比较器回执](evidence/sealed-comparator-receipt.json) | sealed bwrap 实验的原命令、完整 stdout/stderr 和退出码 |
| [manifest.json](manifest.json) | 本目录全部归档文件的大小与 SHA-256（不含 manifest 自身） |

证明 SHA-256：

```text
442334bfd22cf81c9582b071cd6b370f2b6969d961418e6b084a25cc87ae4a91
```

比较器于北京时间 **2026-10-23 02:27:46**（2026-10-22 18:27:46 UTC）退出 0，stderr 为空，输出 Lean default kernel accepts the solution 和 Your solution is okay!。仅有弃用和无用 simp 参数等警告。

原发布方配置见 [comparator.upstream.json](comparator.upstream.json)；[comparator.json](comparator.json) 只将模块路径适配为本项目的 Challenge 与 Submission，定理目标和公理白名单不变。原配置 enable_nanoda=false，本次没有进行 Nanoda 验证。

## 复验

此目录是独立 Lake 项目，固定 Lean v4.34.1 与 Mathlib 提交 d13f23b723b8a846827a245b89c10fc7d3f11612。具备 Elan/Lake 的环境可运行：

```bash
export LEAN_NUM_THREADS=1
lake exe cache get
lake build Challenge Submission
lake env lean AxiomAudit.lean
```

Challenge 中的占位 sorry 不属于 Submission 的证明。AxiomAudit 打印 Submission 中最终定理的公理依赖；应只有 propext、Classical.choice、Quot.sound。

要运行发布方比较器，另需准备与本次固定上游版本一致的 comparator 和沙箱工具；此成果包不内置比较器二进制。完整 sealed 验收命令保存在 [run-sealed-comparator.sh](run-sealed-comparator.sh)，也逐字记录于原回执。该命令需要预备可信 .lake/packages 和 TheoremOS 隔离运行环境，不能视为任意宿主上的一键脚本。

验收修复只处理依赖副本写权限、封存包省略 .git 后的路径映射、单线程预编译及固定 Lean 路径，没有修改原题、证明字节、比较器程序或公理白名单，网络隔离保持。原 run 的原生最终验收因内层线程创建失败仍记录 evaluated_failed；续跑 attempt 已复用同字节证明，归档时尚未原生验收完成。具体快照见 verification.json，原日志未被覆盖。

本成果包含既有 run 的继续运行和人工交付/环境修复，不能据此计算当前 TheoremOS 版本从零解题的成功率。未读取上游已发布解答来构造本证明。

## 来源与许可

原题和原比较器配置来自 openai/math 提交 1581d4cbdd69a0faf34b2089614fe2a814316a6a，按 [Apache-2.0](LICENSE.openai-math) 保留许可。Submission.lean 在冻结原题基础上新增 91 个辅助引理并填充最终证明；comparator.json 仅修改模块名称。修改说明和归属见 [NOTICE](NOTICE)，其余本项目材料遵循仓库根许可证。

## 后续原生验收更新

北京时间 2026-10-23 02:44:45，续跑 de7a57e9-becf-4f94-9276-2090ab3f2738 完成 evaluated_passed，campaign accepted=true。同版本审阅、全目标检查和本地比较器通过，official=false。见 [新增原生通过回执](evidence/native-acceptance-update.json)；归档时 pending 快照及旧 run 失败历史原样保留。
