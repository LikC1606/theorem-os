# 原生检查热点与加速候选（2026-10-24）

Character V2 已完成整份编译（635.03 秒、exitCode=0）、公理审计和独立原比较器检查
（41.15 秒、exitCode=0）。原比较器真实输出 `Lean default kernel accepts the solution`
和 `Your solution is okay!`。加速版已通过正常递送进入独立宿主检查；完整原生最终验收仍在运行，通过总数仍为 5。

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
原始证据见 `snaky-v8-kernel-progress/`；当前不把原题内核成功等同于最终原生验收成功。

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

本目录不包含手写验收回执、伪造缓存或活动 checkpoint 修改。
