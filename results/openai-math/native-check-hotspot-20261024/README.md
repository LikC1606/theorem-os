# 原生检查热点与加速候选（2026-10-24）

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

同题旧完整 V12 在新版本完成时已运行超过 6 小时仍未结束；旧正式 canonical 检查也仍在运行。
这支持“新候选完整编译已在十多分钟内完成”的结论，没有把未结束的基线虚写成精确加速倍数。
`native-sync-def-attempt/` 通过源码、可信文件、原 comparator 和完整递送载荷预检，
现正以原冻结构建启动新的正式验收；五项预算和 preparation timeout 均为 0。
独立完整编译、公理审计均已通过，原生最终验收仍待真实回执。旧正式链继续运行。

Snaky V8 的原题检查已取得原始 `kernel_verified` 回执
`lean-9d717a842be4b918425377eb`：`exitCode=0`，耗时 `8072025 ms`，
仅依赖 `propext`、`Classical.choice`、`Quot.sound`。
原生日志随后记录 `task_checked passed=true, conditional=false`，并进入集成检查。
原验证源码 `712ecd…` 与集成源码 `dc40df…` 只相差删除 1101 个空行，
15263 行非空源码逐字节相同；活动冻结链因字节身份不同，重新启动了完整 Lean 编译。
原始证据见 `snaky-v8-kernel-progress/`；当前不把原题内核成功等同于最终原生验收成功。

现有正式检查继续运行，Honeycomb 继续使用新的冻结构建求解，预算不设上限。
本目录不包含手写验收回执、伪造缓存或活动 checkpoint 修改。
