# 原生检查热点与加速候选（2026-10-24）

最新状态见 [21:19 北京时间进度快照](optimization-progress-20261024T131920Z.json)。五项预算仍全部为 0，Honeycomb 持久服务正常运行。

最新本地原生最终通过总数为 **6**，尚无 OpenAI 托管认证。Character 于北京时间 2026-10-24 20:26:55 完成完整验收，`result.status=evaluated_passed`、固定复审 accepted、原比较器 exit 0；见[冻结终态包](character-native-final-20261024/README.md)。

本轮[固定支持模块复用及复审上下文修复](fixed-support-artifact-reuse-20261024/README.md)已完成：261 项聚焦测试、typecheck、三个 headless bundle 和只读构建 manifest 校验通过。真实 Lean 4.34.1 小型封存样例中，冷检查 2.405 秒、跨工作区暖检查 1.592 秒；前 3 次检查只编译一次支持模块，每次当前目标仍真实编译，错误目标在缓存命中时仍被拒绝。支持源码、配置及包身份变化均触发重新编译；含非可信 owned 依赖时回退原路径。复审上下文只展示匹配 commit、源码摘要及全部原目标的回执，宿主最终验收权限不变。见[独立静态审查](fixed-support-reuse-independent-review-20261024.json)。

新构建 `46551899-4922-4905-b81e-0ff4503842e6` 基于隔离的 exact-source 修复构建，[尚未切入当前冻结链](fixed-support-reuse-activation-20261024.json)。Snaky 长检查和 Honeycomb 数学探索继续运行；上述小型样例不代表整题提速倍数。

SnakyConditional 已通过原目标、集成和全目标内核检查，全目标回执 `lean-63766151ffe8a0523a860487`，耗时 8188.206 秒。当前在固定版本复审；此前一轮模型请求超时后已自动恢复，见[全目标及重试原始事件](snaky-all-target-review-20261024/README.md)。仍需最终工作区检查和原比较器，不计入最终通过数。

[单条 Snaky 证书复用实测](snaky-certificate-reuse-followup-20261024/REJECTION.md)未带来收益：原声明证明段 340 ms；复用候选至少 150268 ms 未完成，故只终止并否决该隔离候选，没有递送或重跑整题。静态减少 `decide +kernel` 次数不能代替实测。

Honeycomb 又新增[四条完整列 word 结构引理](honeycomb-column-word-followup-20261024/README.md)和[两个精确任务包装](honeycomb-column-task-adapters-20261024/README.md)，真实 Lean 检查分别耗时 2.658 秒、4.334 秒，公理仅 `propext/Quot.sound`。两批完整增量已通过正常队列共享，分别于 `12:58:41 UTC`、`13:09:52 UTC` 应用；见[结构引理递送回读](honeycomb-column-word-advisory-20261024/native-advisory-applied-readback.json)和[任务包装递送回读](honeycomb-column-adapters-advisory-20261024/native-advisory-applied-readback.json)。尚无新增 native TaskProof；严格增长界、统一有限盒质量界和精确有限转移编码仍待证明，原题未解。

以下为先前各阶段的时间截点；最新验收状态以上述终态包为准。

Honeycomb 本轮新增 18 条辅助定理通过固定 Lean 检查：
[九条几何引理](honeycomb-column-cardinality-followup-20261024/README.md)给出有限列盒和占据 slab 的长度界；
[九条分层与一阶矩接口](honeycomb-length-profile-followup-20261024/README.md)将这些长度界接到原六项结论。
完整增量已分别于 `10:18:14 UTC`、`10:26:16 UTC` 通过正常队列共享给四个 worker，
全部原任务与 assignment 保留。见[几何回读](honeycomb-geometry-advisory-20261024/native-advisory-applied-readback.json)
和[分层回读](honeycomb-profile-advisory-20261024/native-advisory-applied-readback.json)。
尚未证明桥总质量可和性与准确的有限转移系数恒等式，原题仍未完成；这些是辅助成果，没有新增原生 TaskProof。

分层包的首次宽导入局部检查经诊断中断，精简依赖后上下文准备耗时 5.240 秒，
主八接口耗时 3.372 秒、occupied-slab 组合推论耗时 3.994 秒。
失败、诊断中断与最终成功记录均保留；没有给求解链新增预算上限或重启整题检查。

[保留交付源码的集成修复](exact-source-integration-reuse-20261024/README.md)已完成：
126 项测试、typecheck、三个 bundle 和只读 manifest 校验通过。
真实 Snaky 源码样本中新路径保留了旧合并丢失的 1101 个换行，完整投影和缓存 key 与 delivery 相同。
机制测试使用 mock verifier，没有新增数学验收；单次合并耗时由 28.36 秒降至 0.271 秒，
没有测量完整 Lean 提速。见[根代理审查](exact-source-reuse-review-20261024.json)。
新构建 `1537a457-5694-4896-99fe-f2e9248cb6fc` 已就绪，
[本轮不迁移当前运行](exact-source-reuse-activation-20261024.json)：两条补验已完成集成，
Honeycomb 上次集成仅 21.577 秒，而现有三项数学探索仍在继续。

Character 又于 `09:41:50 UTC` 通过原生集成检查，回执
`lean-7e3b44ab0595415016076711`，整批耗时 2339.924 秒，源码 SHA 与原目标交付一致，
公理仍仅三项标准公理。随后进入 lead 全目标检查；见
[集成原始回执](character-native-stage-cost-20261024/native-integration-verification-20261024T094150Z.json)。

[Honeycomb 最新构建的缓存修复](honeycomb-runtime-reuse-fix-20261024/README.md)也已完成：
保留最新工作流，仅加入两行产品修复；27 项聚焦检查通过、0 失败，三份 bundle 和只读 manifest 校验通过。
构建 `554d6726-fa7b-4b1c-b84b-f846f20b609d` 已可供新的续跑使用，
但[当前未切换](honeycomb-runtime-reuse-fix-20261024/activation-decision.json)：
Honeycomb 最近一次集成只耗时 21.577 秒，尚无证据证明中断长探索并重建会话可以带来净提速。
原有三个活动验核/求解链继续运行，未用新构建改写其缓存或回执。

[Honeycomb 吞吐审查](honeycomb-throughput-review-20261024/README.md)发现 lead 连续 15 轮
没有新进展，而三名数学 worker 均有新的工具活动。减少重复检查的共享建议已通过正常队列应用，
lead 上下文可见；全部数学 assignment 保留。尚未测得性能改善，原生 120 秒检查点规则未改。

[有限矩阵一阶矩引理](honeycomb-finite-matrix-followup-20261024/README.md)已独立检查成功：
有限非负矩阵的单个标量 Green 级数可和，足以推出其一阶长度矩可和，无需先证明全矩阵可和或谱半径界。
两个定理的最终检查 `exitCode=0`，4.673 秒，仅三项标准公理；
完整增量已于 `09:55:44 UTC` 通过正常队列追加到共享参考，四个 worker 的上下文均可见，
全部现有 assignment、其它任务、groups 和 proofRoutes 保留。
这关闭了所提有限状态路线中的分析步骤；桥路径的精确状态编码和有限盒总质量界仍待证明，
不是原题通过或原生 TaskProof。见[回读](honeycomb-finite-matrix-followup-20261024/native-advisory-applied-readback.json)。

Character V2 已完成整份编译（635.03 秒、exitCode=0）、公理审计和独立原比较器检查
（41.15 秒、exitCode=0）。原比较器真实输出 `Lean default kernel accepts the solution`
和 `Your solution is okay!`。加速版于 `09:02:33 UTC` 通过原生原目标检查，
回执 `lean-adc266b0e003d64e5ebdf91b`，原生事件为 `task_checked passed=true, conditional=false`。
整批检查耗时 2375.071 秒，包含 57 个支持模块、主证明及声明查询；该回执不是原生最终验收。
当前已进入集成检查，通过总数仍为 5。原始回执见
[原目标验证](character-native-stage-cost-20261024/native-task-verification-20261024T090233Z.json)
和[进度快照](continuation-progress-20261024T090646Z.json)。

`08:53:13 UTC` 已将新 Character 原生进程树和线程限制到 NUMA 0 的 CPU 40–47，
后续进程继承同一核组，保持单线程和 32 GiB。调整有完整前后回读，但未测得独立提速倍数。
[阶段与缓存审查](character-native-stage-cost-20261024/README.md)确认生成的
`.lake/package-overrides.json` 导致现有集成缓存身份失配；当前冻结链保留原规则，
不能将已有 `.olean` 直接导入后续检查。

[隔离缓存修复](future-runtime-reuse-fix-20261024/README.md)现已完成：仅在封存环境真实校验成功后，
规范化该生成文件的摘要，保留实际包身份、语义配置和非封存环境的失效规则。
真实交付源与两份干净投影的新摘要一致；171 项测试通过、0 失败、1 项按原约定跳过，
三个 headless bundle 构建成功。补丁和已构建产物供审阅，完整本地隔离副本路径见该说明；
results 仅保存列明的交付文件。新构建未切换进当前活动链，不能据此声称当前集成已免编译。

截至 `08:31:32 UTC`，新入口环境准备已真实 exitCode=0（3629.13 秒），resume 准备命中缓存，耗时 6.432 秒。
正常队列编辑已应用，engineer 仅执行一次载入，宿主提交 `aaaf7a217b8df185b467ec71348048b553dfe339`
中的 795645 字节与已验证 V2 的 SHA 完全一致。独立宿主已有 44/57 个依赖模块产物，随后才编译主文件。
精确记录见 [递送核查](native-sync-def-attempt/delivery-observation.md)和
[进度快照](continuation-progress-20261024T083132Z.json)。

模型手写的一条 JSONL 曾因 `kind=delivery` 被冻结协议拒绝；协议仅接受 `progress/proof/research`，
proof 还须绑定 commit。随后模型正常结束，宿主自动提交源码并启动原生验证，故该拒绝未阻断当前检查。
没有为此重复载入、重启或修改活动现场；`candidate.status=completed` 仍只表示模型回合完成。

Character 的正式 Lean 进程在只读栈采样时已经进入模块写出：
`writeModule → mkModuleData → computeExtEntries → localSymbolFrequencyMap → foldRelevantConstants → getFunInfoAux → collectDeps_visit`。
这是引理搜索元数据的参数依赖扫描。采样事实不等于完整验证成功回执。

固定 Lean 4.34.1 的 `Lean/LibrarySuggestions/SymbolFrequency.lean` 仅对
`!isDeniedPremise env m && wasOriginallyTheorem env m` 的本模块声明计算该频率。
新候选把 168 个新增、带显式类型的辅助 `theorem` 改为现有 `noncomputable section` 内的 `def`，
保留名称、类型和证明体。原题 theorem 保持不变。未修改 Lean 内核、Mathlib、活动源码或冻结 runtime。

- 原正式候选 SHA256：`0ec8e7e2fbe9ff7f2d4c849c7558c152e24d707d79943d6f7ac08d0b27fa98c9`。
- 新候选 SHA256：`f8f952feb2ac4894946e6f6cd4089e7e20320cc0312217597b91fde2e7e8f200`。
- `guard-preflight/receipt.json`：冻结源码守卫通过，全部声明名称、类型 header、证明体保持一致；
  候选、目标投影、集成合并和二次投影字节一致。
- `character-sync-def-candidate/build-started.json`：隔离整题编译已启动，固定 Lean、`-j1`、32 GiB，
  不设置时间或心跳预算。依赖从活动原生沙箱的已编译原题上下文复制，排除 `ProducedSolution*`。
- 是否完成编译以自然退出后生成的 `build-receipt.json` 为准；之后还需公理审计和完整原生验收。
  在这些检查完成前，不把该候选记为原生通过，也不报告整题加速倍数。

第一版完整检查在 `634.98 s` 后 `exitCode=1`。仅有两处类型错误：
`external_positive_ne_input` 和 `external_negative_ne_output` 改用 `def` 后，
Lean 从证明体自动纳入了额外 section 参数，后续应用因参数不匹配而失败。
这说明源码显式类型逐字相同，仍须通过真正 elaboration 检查实际声明类型。
没有生成 `.olean`，不能计为加速成功或内核通过。

第二版只将这两项恢复为原来的 `theorem`，其余 166 项仍使用 `def`。
全部显式类型和证明体仍与基线相同；源码 SHA256 为
`5c0cbc35bd6335ab7c6d8d57bdece22a3065c6fdc7dee871d2577826b50396d3`，
完整检查见 `character-sync-def-v2-candidate/`。
第二版于 `07:25:31 UTC` 自然完成：`635.03 s`、`exitCode=0`，成功写出完整 `Submission.olean`。
随后监督执行的公理审计用时 `1.51 s`、`exitCode=0`，原目标仅依赖
`propext`、`Classical.choice`、`Quot.sound`。首次公理打印未保存退出码，故保留其原始输出，
待它退出后重新监督执行审计，以第二次有明确退出码的 `audit-receipt.json` 为准。

独立比较器检查见 `character-sync-def-v2-comparator-prebuilt-v2/`。它直接使用这次真实编译的
同 SHA 产物，独立编译原始 Challenge，保持原目标、公理白名单和 comparator 二进制不变。
独立 Lake 工程将两个已编译模块登记为预构建模块；比较器仍执行声明导出、类型比较、公理检查
和 Lean 内核回放。两次工程入口配置失败的原始记录也保留。活动原生 evaluator 的完整构建命令未改动。

同题旧完整 V12 在新版本完成时已运行超过 6 小时仍未结束；旧正式 canonical 检查也仍在运行。
这支持“新候选完整编译已在十多分钟内完成”的结论，没有把未结束的基线虚写成精确加速倍数。
`native-sync-def-attempt/` 通过源码、可信文件、原 comparator 和完整递送载荷预检，
已用原冻结构建完成新环境准备并进入正式验收；五项预算和 preparation timeout 均为 0。
独立完整编译、公理审计均已通过，原生最终验收仍待真实回执。旧正式链继续运行。

`native-sync-def-attempt/continue-native.py` 已作为持久控制器启动；它已在真实 startup 成功后
自动 resume、验证当前 plan 并通过正常队列递送 V2，继续等待并记录真实终态，没有总时间上限。
`adopt-verified-character-candidate/` 保存了完整旧链 dry-run 和逐模块缓存核查。
同路径恢复旧链仍会触发约 29 分钟的依赖准备，故采用继续新入口的决策；旧链未停止、未恢复、未追加编辑。

Snaky V8 的原题检查已取得原始 `kernel_verified` 回执
`lean-9d717a842be4b918425377eb`：`exitCode=0`，耗时 `8072025 ms`，
仅依赖 `propext`、`Classical.choice`、`Quot.sound`。
原生日志随后记录 `task_checked passed=true, conditional=false`，并进入集成检查。
原验证源码 `712ecd…` 与集成源码 `dc40df…` 只相差删除 1101 个空行，
15263 行非空源码逐字节相同；活动冻结链因字节身份不同，重新启动了完整 Lean 编译。
该集成检查现已通过，原始回执为 `lean-78b317b5823543bbdf5c270f`，
耗时 8343.538 秒，仅三项标准公理。`09:17:09 UTC` 原生日志记录 `task_integrated`，
随后进入 lead 全目标检查，见[完整验证](snaky-integration-cost-20261024/native-integration-verification-20261024T0917Z.json)
和[阶段回读](snaky-integration-cost-20261024/native-integration-progress-20261024T0919Z.json)。
原目标证据见 `snaky-v8-kernel-progress/`；集成成功仍不等同于最终原生验收成功。

[Snaky 集成性能采样](snaky-integration-cost-20261024/DIAGNOSIS.md)定位到
`decide +kernel → mkAuxLemma → 内核检查`，采样瞬间在回收类型检查器缓存引用。
3 秒窗口取得 3 秒 CPU，未见调度等待、交换或 Character 的元数据导出调用链。
没有由此得到即时提速方法，当前检查继续运行，未启动重复大编译。
另有一个[单声明复用候选](snaky-integration-cost-20261024/static-reuse-followup/STATIC-REUSE.md)
已完成静态坐标与补丁回放检查；尚未编译、应用或测得提速，保留供后续独立验证。

现有正式检查继续运行，Honeycomb 继续使用新的冻结构建求解，预算不设上限。
`honeycomb-scheduling-observation/` 记录已有归约源未正式交付及 engineer 被消费者占用的调度问题，
以及通过正常完整 plan 队列修复后取得归约内核验收和集成成功的证据。
原交付和集成回执分别为 `lean-0289d782383448bdadd0ef5e`、`lean-c48c9c7223a04b1246cd7274`。
被验收的归约声明零 sorry/admit，仅三项标准公理；归档整题源码仍含原目标占位。
监督器已在真实证明通过后通过正常队列恢复消费者，08:13:33 UTC 回读 engineer 已重新处理原目标，
监督器完成后 exitCode=0。其提交编号匹配错误及修复前后记录均保留。
核心增长率估计仍未证明；归约交付不等于 Honeycomb 整题完成。

[恢复后的核查](honeycomb-scheduling-observation/post-resume-progress-20261024T083134Z/README.md)
确认第 98 轮仍复用已集成归约，没有新调度故障；一般宽度增长界暂无新源码或验收回执。
已有有限 DFS 不能覆盖全部长度，旧方格图实验也不适用于本题的 honeycomb 邻接。
当前不据这些实验宣称已找到核心证明。

第 104 轮已通过正常队列向 researcher-2 提供
[直接可求和性替代路线](honeycomb-math-route-20261024/native-advisory-handoff.md)：
研究有限矩形桥权重和的统一上界，以及保留连通信息的有限状态转移。
有限矩阵论证可在精确编码和有限质量已证的前提下导出一阶矩；这些几何输入仍未证明，
`K_h=1` 也未确立。该建议包含外部辅助归因，不是 proof delivery。
[应用后核对](honeycomb-math-route-20261024/native-advisory-applied.json)确认只有 advisory 任务修订，
研究员已处理新版任务，原增长界、主目标 assignment、已集成归约和全部数学合同保留。

新路线的[有限列盒辅助归约](honeycomb-finite-box-reduction-20261024/README.md)已有四个新声明通过
真实 Lean 检查及三公理审计：任意有限桥族共处一列盒；统一有限盒权重上界推出任意有限和上界、
`Summable(weight)` 和 `bridgeMass ≤ K`。无预算复验用时 13.47 秒，保持固定 Lean/Mathlib、
32 GiB 和单线程。首次低内存 import 失败指向的工具链文件实际存在，相关失败及入口纠正记录均保留。

`09:09:16 UTC` 已通过正常队列新增共享 advisory `finite_box_zero_mass_reference`，
[回读](honeycomb-finite-box-reduction-20261024/native-advisory-applied-readback.json)确认原六个任务、
完整 assignment、groups 和 proofRoutes 保留。engineer 与 researcher-2 的宿主上下文已包含完整增量，
没有把上下文可见性当成模型已使用。此交付是辅助材料，尚无原生 TaskProof；统一有限上界、
精确有限状态编码和一阶矩仍待证明，Honeycomb 原目标尚未解决。

本目录不包含手写验收回执、伪造缓存或活动 checkpoint 修改。
