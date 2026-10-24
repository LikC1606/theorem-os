# Snaky 616 行证书

完整证明 OAI.SnakyCertificate.certificate_correct 的七个合取：表合法性、placementCount = 1837、557/595/603/615 四项输出，以及全部 616 行的集合与高度条件。有限集合计算均生成由 Lean 内核核查的证明。

完整原题已在固定 Lean v4.34.1 / Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 下通过模块化内核验证。最终公理输出仅有 propext、Classical.choice、Quot.sound；证明模块无 sorry、新增公理或内核绕过。Challenge.lean 单独保留发布方原题占位，不参与证明模块的 imports。

TheoremOS 原生最终验收已于 2026-10-23 22:15:51 UTC（北京时间 10 月 24 日 06:15）通过，status 与 run_outcome 均为 evaluated_passed。原目标、集成、全部原目标检查、固定版本复审和 S3 原发布比较器全部通过，最终 exit 0，无超时或中断，completion 与 solver-ready 标志均有效。见[验收审计](evidence/canonical-v5/native-acceptance-audit.json)与[原生最终结果](evidence/canonical-v5/native-final-result.json)。

最终源码为 [V5 集成版](single-file/SubmissionCanonicalV5Integrated.lean)，SHA-256 b7dc0b2898b8d4ee8ed4a3b10394429f939ff9e4d73761dcd6968e46a4579751，896,495 字节；相对[模型安装的 V5](single-file/SubmissionCanonicalV5.lean)只删除空行，未改变原题或证明。原 32 GiB 限制、冻结运行时、比较器和五项无限求解预算保持不变，无假设辅助输入，公理仅 propext、Classical.choice、Quot.sound。原始阶段回执见 [原生目标](evidence/canonical-v5/native-original-goal-check.json)、[集成](evidence/canonical-v5/native-integration-check.json)、[全部原目标](evidence/canonical-v5/native-full-original-target-check.json)和[固定复审](evidence/canonical-v5/native-fixed-review.json)。原 V2 单文件及比较器回执亦保留。

这是本机冻结原比较器与 TheoremOS 原生最终通过，OpenAI 托管接受尚无确认。最终运行时仅保留 stdout 尾部 12,000 字节与完整流 SHA；审计明确 storedStdoutIsComplete=false。本地 20 份只读快照全部核对哈希，results 包含关键回执和[原快照清单](evidence/canonical-v5/native-terminal-snapshot-manifest.json)。C 档为本项目判断。新增证明含外部代理辅助，不算模型从零独立发现。

源码顺序见 module-order.json，最终声明及公理输出见 CertificateFullKernel.lean 和 evidence/axioms.txt；各模块均有源码 SHA 与 exit 0 回执摘要。原始冗长 linter 输出未复制；回执记录原日志和原回执的 SHA。

复验：先在本目录执行 lake exe cache get，再运行 /usr/bin/python3 verify-kernel.py。脚本按依赖顺序从源码构建全部模块，串行 elaboration，不设置时间或 token 上限。构建产物位于 .build/，未包含在归档中。

保留 OpenAI math 固定 commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a 原定义及 Apache-2.0 许可。未读取上游目标答案。
