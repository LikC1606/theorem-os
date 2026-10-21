# 模块对照实验

目前还没有完成的模块效果实验。模块编辑、可视化、排序合同测试和预设回放，
均不能作为模块提高解题率或降低成本的证据。

当前按用户选择只完成实验工具、方案和离线验证，暂停真实模型调用。
此前已启动的预算校准试跑已经停止，记录见 [2026-10-19 试跑说明](PILOT-20261019.md)。
后续实验按用户选择使用现有 Westlake 凭据，模型为 `deepseek-flash`，推理强度为 `high`。
接入与密钥配置见 [Westlake DeepSeek 配置](WESTLAKE.md)；此前 GPT 试跑不并入 DeepSeek 的比较结果。
DeepSeek 官方服务仍可单独选择，见[官方配置](DEEPSEEK.md)。

## 首轮比较什么

[module-experiment.json](module-experiment.json) 固定四个方案，所有方案使用相同的
四名协作 Agent、原题、模型、环境、解题预算与独立最终验收：

| 方案 | 相对默认方案的变化 | 可回答的问题 |
| --- | --- | --- |
| `default` | 无 | 固定的参照组 |
| `essential-context` | M4 移除可选上下文；原题、来源和必要接口仍保留 | 额外上下文的收益及用量是否值得 |
| `critical-path` | M3 关键路径排序和 M5 共享分工同时替换 | 这一组合策略是否优于默认分工 |
| `construction-rule` | 经 M4 注入一条 M1 追加规则 | 这条提示规则是否有效 |

`critical-path` 是 M3 + M5 的组合实验，不能把差异单独归因于 M3。
自定义规则替换或追加的是模型收到的策略文字，不是 M1 的调用实现或 M5 的分配函数。
报告列出实际组件版本差异，M1 规则的 M4 注入版本也会被记录。

`goals-first` 不再是内置调度策略，仅保留为 [README.md](README.md) 的组件示例：在研究者仍活跃时，默认 M5 已分别优先分配引理和原题目标，
会抵消这种跨任务种类的排序变化。只检查 M3 输出数组不足以说明整个调度行为发生变化。

M2 检查和 S3 完整原题验收在所有组中保持固定。
若研究局部验证的收益，应替换中间反馈策略，仍保留相同的最终完整验收。
单 Agent、独立并行和协作方式的比较另见 [COMPARISON.md](../imo2026/COMPARISON.md)。

## 准备方案

当前小样本改用 [PutnamBench](../putnambench/README.md)：固定种子抽取三道兼容原题，
每题分别生成下面的四组策略，共 12 次计划运行。使用 `sample-putnam --phase prepare`
准备、`sample-putnam --phase report` 汇总，两个阶段都不调用模型。
题目与依赖版本、抽样限制和完整命令见该说明；下方保留单道 IMO2026 的准备方式。

先完成 [IMO2026 环境准备](../imo2026/README.md)，确认固定源码、Lean、Mathlib 缓存和
Codex CLI 可用。从仓库根目录构建，再使用构建命令打印的 `buildManifestRef`：

```bash
bun run build
bun run math compare --phase prepare \
  --provider westlake --model deepseek-flash --effort high \
  --module-experiment examples/components/module-experiment.json \
  --repo /absolute/path/to/imo2026 --problem imo2026_q1 \
  --task-file examples/components/experiment-task.md \
  --build-manifest /absolute/path/to/manifest.json \
  --repetitions 1 --workers 4 \
  --max-turns 20 --max-run-seconds 600 --max-turn-seconds 180 \
  --max-total-tokens 30000 \
  --directory /absolute/new/module-pilot-q1
```

这会准备一题、四组、每组一次的探索性计划，每组解题时间设为十分钟，最多 20 次调度。
30,000 个服务商上报 token 是请求门槛，不是硬用量上限。新 Westlake 运行会逐次检查
上游请求；单次或已经并发发出的请求仍可能超额。其他直接 Responses 服务和历史记录
仍标为调度级限制。该数值仅用于配置示例，已发现不足以覆盖本次 Q1 规划阶段，
不应直接用于正式效果比较。依赖准备和最终验收另计时间。
该命令固定模型为 Westlake `deepseek-flash`，推理强度 `high`；该模型的预算仍需独立校准。
当前兼容器还会限制初始 Lead 规划：达到总门槛的四分之一或两次上游请求后，
在完整记账和源码检查通过的前提下交接保存的方案，或回退到原题目标任务。
具体适用范围见[初始规划交接](WESTLAKE.md#初始规划交接)。该策略尚未经过真实模型校准，
新模块版本须重新构建并准备新计划，不能套用到历史实验上。

`prepare` 不调用模型，会冻结题目、构建、环境摘要，以及每次运行的模块配置与启动参数。
每组和每次重复均使用新的隔离工作区，不从其他组复制候选证明。
`--provider westlake` 或 `--provider deepseek` 还会为每次尝试生成无密钥的独立 Codex profile，冻结服务商配置与模型目录。
启动文件固定各自的 profile，避免随后运行时继承其他服务商的配置。
方案顺序随重复轮转；重复编号不是模型采样 seed。

读取 `comparison.json` 检查计划。汇总已保存的证据使用 `report`，不调用模型；
尚未执行的计划会保留为缺失结果，不会生成成功或费用估算：

```bash
bun run math compare --phase report --directory /absolute/new/module-pilot-q1
```

真正执行时需单独使用 `run`。本轮只准备方案和离线验证，不再执行这条命令：

```bash
bun run math compare --phase run --directory /absolute/new/module-pilot-q1
```

中断后使用相应 `launch.json` 的原参数添加 `--resume` 恢复单次运行，随后重新生成报告。
更改策略或构建后准备新实验，保留原实验的文件和依赖。
单次运行也可以用 `bun run math run --module-plan /path/to/module-plan.json ...` 加载同格式方案；
此时保留 `--method direct --scheduler plan`，由方案决定内部策略。

## 如何读结果

`report.json` 保存所有计划尝试、完整验收数、调度次数、用量缺失、超额、错误和耗时。
`batchStatus`、`signal` 和 `batchError` 保留批处理状态、终止信号与启动错误，
与运行时的 `status` 分开记录，便于区分主动取消、跳过和证据缺失。
`moduleExperiment.variants` 列出每组方案、方法摘要及组件版本差异。
计划的 `configuration.provider` 和报告的 `provider` 记录服务商、上游端点与协议；
Westlake 还标明会话内 Responses 兼容器，不混淆为 DeepSeek 官方直连。
`pairedComparisons` 按同一题目和重复编号匹配参照组与实验组，记录胜、负、双方通过、
双方未通过以及缺失的配对；通过率差使用全部计划尝试为分母。
token 和解题耗时差只在双方都有对应完整记录时计算，并同时给出可用配对数。
负差表示实验组较少使用 token 或较快结束，不表示它在失败时更有效。

只有完整原题经相同独立 Lean 验收通过才记为成功；准备完成、辅助引理通过、模型宣告完成、
超时和记录缺失均不能算成功。报告读取已保存证据，不重跑 Lean；这里是本地验收，
`official: false`。服务商未上报用量时保留 `null`，不估算费用。

试跑只用于发现环境故障、调度是否实际触发和失败模式，不能说明模块化有效。
这些对照衡量具体策略和上下文的作用，不能单独证明模块化架构优于单体实现。
正式比较应预先固定多道题目与重复次数；当前 PutnamBench 三题、每题一次仅为探索性计划。
先单独校准能覆盖规划、证明和复核阶段的预算，再准备新的冻结计划。
对每题使用相同四组方案和预算，记录策略实际触发的阶段，保留所有失败，再报告每题结果与总计。
不要只挑成功题、使用事后改过的配置补跑，或把多模块组合的效果写成单模块收益。
