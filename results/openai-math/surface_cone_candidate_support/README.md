# 三维完备局部复代数的存在性

完整目标 OAI.SmallCM.candidate_ring_properties 已通过固定 Lean 内核与本地隔离原发布方比较器。取三变量复形式幂级数环，证明整环、Noetherian、整闭、局部、极大理想完备、维数为 3，且复数到剩余域的代数映射双射。只证明手稿 195-01 的支持结果，不代表论文主结论。

原生 TheoremOS 最终验收已完成 evaluated_passed；本地验证不等于 OpenAI 托管验收。D 档是本项目判断，证明含外部辅助，不计作 deepseek-flash 独立从零的成绩。

- [Submission.lean](Submission.lean)：独立完整候选，274 行，无 sorry/admit。
- [Challenge.lean](Challenge.lean)：固定原题，保留目标占位。
- [verification.json](verification.json)：精确 SHA、工具链、状态、归因。
- [provenance.json](provenance.json)：上游身份及手稿映射。
- [内核与公理回执](evidence/kernel-axiom-receipt.json)：exit 0，仅 propext、Classical.choice、Quot.sound。
- [隔离比较器回执](evidence/sealed-comparator-receipt.json)：bwrap、exit 0、stderr 为空。
- [manifest.json](manifest.json)：全部归档文件的大小和 SHA-256。

北京时间 2026-10-23 03:02:18，隔离比较器输出 Lean default kernel accepts the solution 和 Your solution is okay!。配置只适配 Challenge/Submission 模块名，目标、公理白名单不改；原配置未启用 Nanoda。运行包含可写依赖副本、路径映射、单线程预编译与固定 Lean 路径适配。

固定 Lean v4.34.1、Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612。复验：依次执行 LEAN_NUM_THREADS=1、lake exe cache get、lake build Challenge Submission、lake env lean AxiomAudit.lean。[隔离命令](run-sealed-comparator.sh) 需要预备固定 comparator、可信依赖与 TheoremOS 沙箱环境。

归因：map_official_targets 提供维数和完备性，inspect_campaign_runner 提供幂级数整闭性，父代理补剩余域及组装。仅使用固定 Mathlib 与原题，未读取已发布解答。原生 canonical 对辅助定义作内联，字节不同，最终应另附精确源码与 SHA 登记。

原题和比较器按 [Apache-2.0](LICENSE.openai-math) 保留许可，修改与归属见 [NOTICE](NOTICE)。

## 原生最终验收

北京时间 2026-10-23 03:21:22，原生 run cbfa1f3c-2760-4d7e-987a-97b48698fd49 完成 evaluated_passed，campaign accepted=true，official=false。同版本 review、全目标检查、原比较器通过。

原生集成时将辅助等价定义内联，精确接受字节见 [NativeSubmission.lean](NativeSubmission.lean)，SHA bc4a1cec74196b46dd726a46dc467c40b8657527dbd235a49a3cf0b5e4355ac9。独立候选 Submission.lean 与原回执保留，避免混用；[新增原生回执](evidence/native-acceptance-update.json) 和 [同字节内核公理审计](evidence/native-canonical-kernel-receipt.json) 分别记录最终证据。归档时 pending 快照保持原样。
