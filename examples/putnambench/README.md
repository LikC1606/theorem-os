# PutnamBench 小样本模块实验

从 [PutnamBench](https://github.com/trishullab/PutnamBench) 的 Lean 原题中固定抽取三道，
每题分别准备默认方案、精简上下文、关键路径组合和自定义规则四组，共 12 次计划运行。
服务商沿用 Westlake `deepseek-flash` / `high`。准备与汇总命令不调用模型。
已完成一题默认方案的[真实网关预算校准](CALIBRATION-20261019.md)，尚无通过验收的证明。
四组策略的区别见[模块实验说明](../components/EXPERIMENTS.md)。

## 来源与抽样

来源固定为提交 `13d042960189f55d748048317c24064a0e2215ea`，使用 Lean 4.33.0、
Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`，与当前运行时一致。
适配器检查工具链和全部依赖版本，从该提交的 Git blob 读取原始字节；工作区修改和
`informal/putnam.json` 中的解答不会成为模型输入。原文件内的题目注释保持原样。

第一版只支持单个命名定理、答案定义已完整、且原有证明洞全部位于可编辑证明区域的题目。
在固定提交的 672 题中，46 题符合条件；排除 346 题带答案定义洞、279 题的证明洞不受
当前证明区域解析器支持，以及 1 题在定理类型中使用推断占位符。
不会通过改写原题、填入参考答案或放宽冻结定义约束来扩大题池。
因此这是兼容子集的样本，不代表对整个 PutnamBench 的均匀抽样。

默认种子为 `theorem-os-putnam-pilot-v1`。按 `SHA256(seed + NUL + problemId)` 升序选题，
记录候选池摘要、种子、来源文件 SHA-256、依赖身份和每个子计划的摘要。
相同代码、来源提交和种子可重现相同题目。这个种子只控制选题，不是模型的生成 seed。

| 默认样本 | 题目内容 |
| --- | --- |
| [`putnam_2025_b2`](https://github.com/trishullab/PutnamBench/blob/13d042960189f55d748048317c24064a0e2215ea/lean4/src/putnam_2025_b2.lean) | 单调连续函数对应的平面区域与旋转体的重心不等式 |
| [`putnam_1963_a4`](https://github.com/trishullab/PutnamBench/blob/13d042960189f55d748048317c24064a0e2215ea/lean4/src/putnam_1963_a4.lean) | 正实数列的上极限不等式及常数最优性 |
| [`putnam_2025_b1`](https://github.com/trishullab/PutnamBench/blob/13d042960189f55d748048317c24064a0e2215ea/lean4/src/putnam_2025_b1.lean) | 在外心封闭条件下证明平面染色为单色 |

这是按种子得到的探索性样本，未按解题难度筛选。三道题不足以评价整个系统或数据集。

## 准备与汇总

需要 Git、Bun 和已安装的项目依赖。准备阶段不需要 API Key，也不下载或编译 Mathlib。
先取得包含固定提交的源码仓库，再从 TheoremOS 仓库根目录构建：

```bash
git clone https://github.com/trishullab/PutnamBench.git /absolute/path/PutnamBench
bun run build
```

使用构建命令输出的 `buildManifestRef`，并选择源码仓库之外的新目录：

```bash
bun run math sample-putnam --phase prepare \
  --repo /absolute/path/PutnamBench \
  --build-manifest /absolute/path/to/manifest.json \
  --directory /absolute/new/putnam-pilot

bun run math sample-putnam --phase report \
  --directory /absolute/new/putnam-pilot
```

`--count 1..20` 和 `--seed TEXT` 可在准备时调整抽样；默认题池由固定提交读取，
不要求当前 checkout 位于该提交。模型默认 Westlake DeepSeek，可显式传入
`--provider westlake --model deepseek-flash --effort high`。

每题每组使用独立工作区、原始 Lean 文件和无密钥的 Codex profile。
默认四名协作 Agent、一次重复、20 次调度、解题十分钟、单次调度三分钟，
服务商上报 token 门槛为 30,000。预算为探索性配置；单题校准在首轮中断前已上报
129,989 token，完整用量仍缺失。该历史运行使用调度级门槛，一个回合内连续推理未被阻止。
新 Westlake 运行改为每次上游请求前检查共享用量，超额或缺失回执后阻止回合内续发；
已发出的单次和并发请求仍可能超额，因此不是硬计费上限。该修复已通过离线验证，
尚未开展新的真实校准；旧计划与结果保留原限制标签。依赖准备和最终验收另计时间。
`--repetitions`、`--workers`、`--max-turns`、`--max-run-seconds`、`--max-turn-seconds`、
`--max-total-tokens` 和 `--module-experiment` 可在准备时显式固定。

根目录的 `sample.json` 保存抽样与共同配置；每道题的目录保存自己的 `comparison.json`、
四组工作区与启动文件。`report` 读取已保存记录，不调用模型或重跑 Lean。
它先校验子计划摘要、题目身份及共同配置，再生成逐题报告和总计；
只在同一题目、同一重复编号内进行组间配对。不同题目的同号重复不会互相配对。
未执行的 12 次计划保持 `missing`、用量 `null`，不是失败实验或模块效果证据。

`sample-putnam` 只提供 `prepare` 和 `report`。单组校准可显式启动一个冻结的 launch：

```bash
bun run math batch \
  --launch /absolute/new/putnam-pilot/putnam_2025_b2/1-default/launch.json \
  --concurrency 1 \
  --output /absolute/new/putnam-pilot/putnam_2025_b2/batch.json
```

`compare --phase run --directory /absolute/new/putnam-pilot/putnam_2025_b2` 会启动该题全部四组。
运行前需完成 [Westlake 配置](../components/WESTLAKE.md)与对应 Lean/Mathlib 环境检查。
代码、构建或预算改变后，应重新准备到新目录，保留旧计划与结果。
原 IMO2026 实验使用不同的依赖版本，不能直接复用其编译缓存。
目前没有配对完成的模块实验，也没有模块收益或完整成本结论。

## 验收边界与许可

适配器复用 `lean-task` 的原题冻结、隔离运行和独立完整目标验收，保留原始源码、
定义、声明类型和导入。使用运行时固定的 Mathlib 项目包装，未运行 PutnamBench 官方评测，
所以报告始终是本地验收 `official: false`。
原题保留 `sorry` 时的 Lean 加载检查只验证环境和声明可用，不能作为证明通过。
模型完成消息、局部引理或准备成功同样不能算成功。

原题归属 PutnamBench，Lean 文件许可见上游
[`lean4/LICENSE`](https://github.com/trishullab/PutnamBench/blob/13d042960189f55d748048317c24064a0e2215ea/lean4/LICENSE)（Apache 2.0）。
本目录只包含适配流程与任务说明，原题在准备时从本地的固定 Git 对象导入。
