# Snaky 单证书复用：实测否决

本轮只评估一个已有静态候选：将 `qescapestep_11` 的 `decide +kernel` 换为坐标变换后复用不透明定理 `qsmall_step11`。实测结果不支持采用。原声明证明段已完成，只需 **340 ms**；新写法在同一编译上下文的同步证明段已运行 **至少 150268 ms**，仍未完成，观察下界超过原证明 **441 倍**。按主代理最新指示结束该候选，只给本隔离检查进程发送 SIGTERM，真实 actualExitCode=-15、timedOut=false。没有新增时间或调用预算，也没有中断活动原题或 review。

| 检查 | 真实结果 | 可解释范围 |
|---|---|---|
| 新的轻量适配上下文 | exit 0，10.585 s | 复用既有 olean，仅加入规范源的4个适配声明 |
| 原 qescapestep_11 | exit 0，证明段340 ms，整进程10.941 s | 导入和导出成本计入整进程；标准三公理 |
| 静态复用候选 | 人工否决，exit -15，整进程161.013 s | 证明段下界150268 ms；未核验成功、无 olean |
| 规范712ecd和集成dc40df的完整候选源 | 两份冻结 source guard 均通过 | 只证明源边界保持，未执行完整 Lean 目标 |

不要递送或应用本包补丁。保留原 `qescapestep_11`。它的 340 ms 成本不能解释之前整题数小时的内核检查；此前栈采样也没有确定具体声明，不能把全程热点归到这一个证书。

已检查可复用依赖为 `CandidateLargestRowSmallCommon.olean`、`CandidateLargestRowChunkListData.olean`、`CandidateSemanticsCoreProbe.olean`、`CandidateDataProbe.olean`，每份原源码均与既有成功回执 SHA256 匹配。直接相关的45个声明，包括完整 `ql614` chunks、`qm614`、坐标变换、qRow结构和qsmall证书，与 V8 规范源逐项规范化文本完全一致。记录在 [compiled-source-correspondence.json](/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/snaky-certificate-reuse-followup-20261024/compiled-source-correspondence.json)。新上下文及原证书的公理打印均只有 propext、Classical.choice、Quot.sound。规范源使用 proposition-valued def，因此保留 defProp linter 提示；候选没有完成，不能声称候选公理检查通过。

原始完整源身份：712ecd4ee1a6cf29e5dc08a07510910addc1870b4039327836646b7a0f16daab 与 dc40df160330f9058ff0af4e85adac6ed1be8be0b2d54c7fba5f10f71450eaae。候选分别是803b58f1690d2b885b2a0214dc8fa643d2095194f8757c7a14b3e4a13a50affd 与 e079653d2a78f26ac1021c9ef86ec2cdff4ac3dd0fd4d46f083b8ab190b112ab。两份都仅替换同一声明的证明体，声明头、其余源字节和最终主定理块保持不变；完整名字列表不变，均低于1 MiB。`decide +kernel` 源码位置718降至717只是静态计数，未带来已证实的运行收益。

冻结 guard 直接使用先前 V8 原生 intake 使用的相同 runtime 实现，创建本目录内的独立 seed fixture。没有改 guard、原始 Challenge、依赖环境或原题文件。证据分别在 [source-guard-result.json](/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/snaky-certificate-reuse-followup-20261024/source-guard-result.json)、[single-declaration-diff-audit.json](/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/snaky-certificate-reuse-followup-20261024/single-declaration-diff-audit.json)。guard 的 seed Git 提交仅属于本目录下的 disposable fixture；没有主仓库提交、候选提交或发布。

完整退出和计时证据：

- [baseline-01-result.json](/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/snaky-certificate-reuse-followup-20261024/baseline-01-result.json)，原声明源和逐段 monotonic 标记随回执保存。
- [reuse-01-result.json](/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/snaky-certificate-reuse-followup-20261024/reuse-01-result.json) 与 [reuse-01-rejection.json](/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/snaky-certificate-reuse-followup-20261024/reuse-01-rejection.json)，保留未完成、SIGTERM及理由。
- [result.json](/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/snaky-certificate-reuse-followup-20261024/result.json)，机器可读否决结论、边界及全部主证据路径。

固定 Lean4.34.1、Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612、只读封存环境身份2d808da67c8ab8ad74458d8a53ecc2ee8da9c63a825e0429439ebf56a9a78c87，32 GiB、单核 -j1、maxHeartbeats=0，无 wall/CPU/invocation cap。证明段时间来自同一进程中相邻 `IO.monoMsNow` 标记，关闭异步检查；比例是单次局部检查的观察下界，不是全题性能估计。未定位替换体中具体慢的 tactic，也没有为追求正收益再开长编译。

现有静态清单表明 `qtable_valid_probe` 已只证明一次并被15个根行复用；615个qmeq声明是不同的行输出等式。没有证据证明此源内还有一份相同命题的大型证书可直接删除。下一项最小研究方向是由主代理检查验收协议中未变源码的重复完整检查，只有完整源SHA、固定环境、目标查询与允许公理证据全部匹配时才讨论复用；本包未改该协议或任何必需验收门。

全部写入仅本目录；未碰活动review、原题链、runtime/state/队列、原缓存或既有回执，未读ProducedSolution。否决后无额外Lean调用。目录归档后不再修改，`SHA256SUMS` 校验载荷与索引；源保护fixture作为隔离证据保留。
