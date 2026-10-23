# Snaky 616 行证书

完整证明 OAI.SnakyCertificate.certificate_correct 的七个合取：表合法性、placementCount = 1837、557/595/603/615 四项输出，以及全部 616 行的集合与高度条件。有限集合计算均生成由 Lean 内核核查的证明。

完整原题已在固定 Lean v4.34.1 / Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 下通过模块化内核验证。最终公理输出仅有 propext、Classical.choice、Quot.sound；证明模块无 sorry、新增公理或内核绕过。Challenge.lean 单独保留发布方原题占位，不参与证明模块的 imports。

完整单文件已通过原隔离比较器。原 V2 源码见 [single-file/Submission.lean](single-file/Submission.lean)，原始回执见 [V2 comparator receipt](evidence/canonical-v2/sealed-canonical-v2-comparator-receipt.json)。后续 [V5 源码](single-file/SubmissionCanonicalV5.lean)在原 32 GiB 限制与冻结运行时下通过原比较器、同源宿主公理检查，并于 2026-10-23 17:43 UTC 通过正常原生目标检查，条件列表为空。回执见 [V5 evidence](evidence/canonical-v5/native-original-goal-check.json)。集成检查仍在运行，固定 review 和最终验收尚未完成，原生 accepted 仍为 false；OpenAI 托管接受尚无确认。C 档为本项目判断。新增证明含外部代理辅助，不算模型从零独立发现。

源码顺序见 module-order.json，最终声明及公理输出见 CertificateFullKernel.lean 和 evidence/axioms.txt；各模块均有源码 SHA 与 exit 0 回执摘要。原始冗长 linter 输出未复制；回执记录原日志和原回执的 SHA。

复验：先在本目录执行 lake exe cache get，再运行 /usr/bin/python3 verify-kernel.py。脚本按依赖顺序从源码构建全部模块，串行 elaboration，不设置时间或 token 上限。构建产物位于 .build/，未包含在归档中。

保留 OpenAI math 固定 commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a 原定义及 Apache-2.0 许可。未读取上游目标答案。
