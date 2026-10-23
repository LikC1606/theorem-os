# Snaky 普通 35 步必胜策略

证明覆盖原题的全局合法策略、35 步获得 Snaky、Maker/Breaker 集合不交与每步棋子数要求。先由 616 行证书建立威胁语义，再组合开局几何，最后构造合法普通策略。最终声明使用原目标名 OAI.SnakyConditional.snaky_winning_strategy_with_legal_states。

完整原题已在固定 Lean v4.34.1 / Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 下通过模块化内核验证。最终公理输出仅有 propext、Classical.choice、Quot.sound；证明模块无 sorry、新增公理或内核绕过。Challenge.lean 单独保留发布方原题占位，不参与证明模块的 imports。

后续 [V6 单文件提交](single-file/SubmissionCanonicalV6.lean)于 2026-10-23 17:46:19 UTC 通过冻结原比较器，自然 exit 0，保留完整 stdout/stderr；原始回执见 [V6 comparator receipt](evidence/canonical-v6/original-comparator-receipt.json)。源码 SHA-256 为 `94e1154db63070c8dd4b2344a5f040200fe9174937e578d95f327cd803cc9f77`，968,086 字节。原目标、比较器、32 GiB 地址空间限制和运行时均保持固定，未增加时间上限。同源宿主的独立公理检查正在运行，通过后才进入正常原生投递和最终验收。

此题尚不能计为原生 accepted，OpenAI 托管认证也无确认。C 档为本项目判断。新增证明含外部代理辅助，不算模型从零独立发现。

源码顺序见 module-order.json，最终声明及公理输出见 ExactTarget.lean 和 evidence/axioms.txt；各模块均有源码 SHA 与 exit 0 回执摘要。原始冗长 linter 输出未复制；回执记录原日志和原回执的 SHA。

复验：先在本目录执行 lake exe cache get，再运行 /usr/bin/python3 verify-kernel.py。脚本按依赖顺序从源码构建全部模块，串行 elaboration，不设置时间或 token 上限。构建产物位于 .build/，未包含在归档中。

保留 OpenAI math 固定 commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a 原定义及 Apache-2.0 许可。未读取上游目标答案。
