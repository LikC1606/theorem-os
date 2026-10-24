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

Snaky V8 的原题检查已取得原始 `kernel_verified` 回执
`lean-9d717a842be4b918425377eb`：`exitCode=0`，耗时 `8072025 ms`，
仅依赖 `propext`、`Classical.choice`、`Quot.sound`。
原生日志随后记录 `task_checked passed=true, conditional=false`，并进入集成检查。
原验证源码 `712ecd…` 与集成源码 `dc40df…` 的字节身份不同，活动冻结链重新启动了完整 Lean 编译。
原始证据见 `snaky-v8-kernel-progress/`；当前不把原题内核成功等同于最终原生验收成功。

现有正式检查继续运行，Honeycomb 继续使用新的冻结构建求解，预算不设上限。
本目录不包含手写验收回执、伪造缓存或活动 checkpoint 修改。
