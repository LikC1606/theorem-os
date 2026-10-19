# PutnamBench 请求级预算校准

2026-10-19 使用 Westlake `deepseek-flash` / `high` 重跑 `putnam_2025_b2` 默认方案。
请求门槛在真实网关中生效，冻结 profile 没有漂移；两次请求完整上报 38,104 token，
第三次请求在本地拒绝。只完成一次 Lead 规划调度，没有通过验收的证明。
这次是网关和预算校准，不能据此判断模块效果。

## 固定输入

- PutnamBench 提交：`13d042960189f55d748048317c24064a0e2215ea`。
- 原题 SHA-256：`5cfb42eef38b09ea4a1464f010bf495ca4d24a5d0cea3c8d57ce5d182221d638`。
- Lean 4.33.0，Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`。
- 默认模块方案、4 名协作角色、20 次调度、解题 600 秒、单次调度 180 秒。
- 服务商上报 token 门槛 30,000，限制类型 `provider-observed-upstream-request-limit`。
- 构建 `4512b2b4-5ad0-4427-a4b1-83caef8eed16`；配置隔离及请求级预算修复均包含在内。

原题、任务、模块方案、模型与预算保持与[此前校准](CALIBRATION-20261019.md)相同，
使用独立新目录 `theorem-os-runs/putnambench-request-budget-20261019/putnam_2025_b2/`。
旧计划、配置和结果没有被覆盖。Lean 环境的 21 项预检通过后，只启动了默认组。

## 观察结果

解题阶段 170.055 秒，最终状态 `limit_reached`，原因 `math_total_token_limit`。
批处理将退出码 4 记作 `failed`；本次原因是预期的预算停止。

| 上游请求 | 本次完整上报 | 累计上报 | 后续行为 |
| --- | ---: | ---: | --- |
| 第 1 次 | 14,834 | 14,834 | 尚未达到门槛，允许续发 |
| 第 2 次 | 23,270 | 38,104 | 达到门槛，禁止续发 |
| 第 3 次尝试 | 无上游请求 | 38,104 | 本地 HTTP 403，`math_total_token_limit` |

运行状态记录 `startedRequests: 2`、`reportedRequests: 2`、`pendingRequests: 0`、
`incomplete: false`；`usageComplete: true`。本地拒绝没有增加请求数或缺失用量。
仅 Lead 发生模型请求，另外三名角色均为零次调度，不计为缺失用量。

| 用量 | Token |
| --- | ---: |
| 输入 | 25,034 |
| 其中缓存输入 | 16,256 |
| 输出 | 13,070 |
| 其中推理输出 | 12,307 |
| 合计 | 38,104 |

缓存输入和推理输出分别是输入和输出的子项，不另行相加。
第二次请求发出时累计用量仍低于门槛，完成后超出 8,104 token；这仍不是硬计费上限，
也没有验证多角色并发超额或真实网关缺失回执的路径。这两类路径仍依赖离线测试。

本次完成 3 次成功的 `exec_command`，没有 `apply_patch` 或 Lean 证明检查记录。
`completion_signal_valid` 和 `solver_ready_receipt_valid` 均为 false，
`solution_commit: null`，最终 evaluator 为 `skipped / proof_incomplete`。
没有把工具往返、模型输出或预算停止当作证明成功。

原生 Codex 将本地 HTTP 403 显示为认证类错误，角色的 `lastFailure` 留下
`math_model_authentication_failed`。宿主的预算事件、最终结果和比较报告均正确使用
`math_total_token_limit`；该角色字段仍需改善错误分类，不能据此认定真实密钥失效。

## 身份与工件

`report.json` 中默认组保留 `limit_reached`、完整用量与请求级限制标签，
没有出现此前的 `comparison_provider_profile_changed`。原题、launch、模块方案、
receipt、任务、环境、模型、角色和 profile 摘要均匹配冻结计划。
其他三个模块组保持 `missing`、用量 `null`，配对观察数为 0。
总报告的限制标签为 `mixed`，原因是未运行组没有限制记录；默认组的实际限制见其逐行记录。

运行期间原工作目录发生了额外源码变更，汇总开始时存在合并冲突。
运行结束后的核对确认 3 个已执行 bundle 均匹配原 manifest。随后公共 `out/main`
在 06:08:53 UTC 被后续构建更新，`math-solver.js` 已不再匹配旧摘要；收尾复核时合并冲突
已清除，但当前源码也不同于该冻结版本。旧 launch 仅保留为证据，不能直接重跑。
汇总使用独立只读用途的 checkout：`ff61a74116cbb94229b9bb098e9de9a8787448a1`。
该版本全部 144 个构建源码输入逐项匹配 manifest；报告仍读取原计划和结果的绝对路径，
保留身份校验，没有修改 manifest、冻结 profile 或覆盖原工作目录的源码。
这一步只读取已保存的记录，没有再次调用模型或 Lean。

本地保留 `comparison.json`、`batch.json`、`report.json`、`1-default/result.json`、
运行状态、原生客户端记录及 `CALIBRATION.md`。相关运行子进程均已退出。
对该实验目录的普通文件检查未发现实际 API Key；没有复制认证文件。

## 后续工作

后续实验使用与合并后源码一致的构建和新计划；优先改善本地预算拒绝的错误分类，
约束 Lead 规划开销，使有限预算能进入实际证明步骤，再验证完整目标的独立 Lean 验收。
本次没有扩大预算、启动其他模块组，或开展三题四组的效果比较。
