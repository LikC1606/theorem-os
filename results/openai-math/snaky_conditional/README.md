# Snaky 普通 35 步必胜策略

证明覆盖原题的全局合法策略、35 步获得 Snaky、Maker/Breaker 集合不交与每步棋子数要求。先由 616 行证书建立威胁语义，再组合开局几何，最后构造合法普通策略。最终声明使用原目标名 OAI.SnakyConditional.snaky_winning_strategy_with_legal_states。

完整原题已在固定 Lean v4.34.1 / Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 下通过模块化内核验证。最终公理输出仅有 propext、Classical.choice、Quot.sound；证明模块无 sorry、新增公理或内核绕过。Challenge.lean 单独保留发布方原题占位，不参与证明模块的 imports。

后续 [V6 单文件提交](single-file/SubmissionCanonicalV6.lean)于 2026-10-23 17:46:19 UTC 通过冻结原比较器，自然 exit 0，保留完整 stdout/stderr；原始回执见 [V6 comparator receipt](evidence/canonical-v6/original-comparator-receipt.json)。源码 SHA-256 为 `94e1154db63070c8dd4b2344a5f040200fe9174937e578d95f327cd803cc9f77`，968,086 字节。同源宿主亦于 20:00:51 UTC 通过，公理仅标准三项，见 [V6 host receipt](evidence/canonical-v6/host-full-result.json)。原目标、比较器、32 GiB 地址空间限制和运行时均保持固定，未增加时间上限。

原生入口按短名比较声明，V6 中不同命名空间的三个新增 projection 同名被拒。后续 [V7 源码](single-file/SubmissionCanonicalV7.lean)只重命名这三个新增 helper 及引用，保留原题和计算表，SHA-256 为 `2edd54515230fd886561c1a79a37155c90162f85611567f2fbb63db9ea5284a3`，968,236 字节。V7 经正常投递，于 23:31 UTC 获得原生目标检查通过，完整 verification 见 [V7 goal proof](evidence/canonical-v7/native-goal-proof.json)，仅标准三公理、无剩余目标或 sorry。此后集成阶段于 2026-10-24 01:46 UTC 报 math_verifier_unavailable 并停止，最终比较器未执行；具体底层诊断未保留，原因仍在定位，见 [V7 阶段与错误摘要](evidence/canonical-v7/goal-pass-integration-error-summary.json)。V6 的历史整题回执不作为 V7 最终验收证据。

最新 V8 已于 2026-10-24 06:53:48 UTC 获得真实原生原目标内核回执 `lean-9d717a842be4b918425377eb`，exitCode=0，耗时 8,072,025 ms，仅标准三公理；原生事件确认 `task_checked passed=true, conditional=false`。后续集成源码只删除 1,101 个空行，15,263 行非空源码逐字节相同，见[V8 回执与集成核查](../native-check-hotspot-20261024/snaky-v8-kernel-progress/ORIGINAL-INTEGRATION-IDENTITY.md)。集成内核检查现已通过，回执 `lean-78b317b5823543bbdf5c270f`，耗时 8343.538 秒，仅三项标准公理；09:17:09 UTC 原生状态已记录 integrated，进入 lead 全目标检查。见[原始集成回执](../native-check-hotspot-20261024/snaky-integration-cost-20261024/native-integration-verification-20261024T0917Z.json)。最终比较器及原生最终验收仍待完成。

此题尚不能计为原生 accepted，OpenAI 托管认证也无确认。C 档为本项目判断。新增证明含外部代理辅助，不算模型从零独立发现。

源码顺序见 module-order.json，最终声明及公理输出见 ExactTarget.lean 和 evidence/axioms.txt；各模块均有源码 SHA 与 exit 0 回执摘要。原始冗长 linter 输出未复制；回执记录原日志和原回执的 SHA。

复验：先在本目录执行 lake exe cache get，再运行 /usr/bin/python3 verify-kernel.py。脚本按依赖顺序从源码构建全部模块，串行 elaboration，不设置时间或 token 上限。构建产物位于 .build/，未包含在归档中。

保留 OpenAI math 固定 commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a 原定义及 Apache-2.0 许可。未读取上游目标答案。
