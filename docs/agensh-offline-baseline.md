本文记录 2026-10-23 对 Agensh 采用计划的离线基线核查。范围仅为已有文档、源码和下列三个已知运行目录；未启动或恢复运行，未调用真实模型。结论不覆盖其他历史运行。

**实际运行证据**

逐一读取各目录的 `1-default/result.json`、`1-default/result.json.runtime/state.json`，并统计 `batch.json.logs/1.log` 的事件名：

1. `/home/lzh/theorem-os-runs/putnambench-request-budget-20261019/putnam_2025_b2/`
2. `/home/lzh/theorem-os-runs/putnambench-calibration-20261019/putnam_2025_b2/`
3. `/home/lzh/theorem-os-runs/putnambench-calibration-20261019/vllm-compatible/putnam_2025_b2/`

| 目录序号 | 最终状态 | Lead planning dispatch / turns | 三名 peer 各自的 turns / dispatchCounts | 最终任务 |
|---|---|---|---|---|
| 1 | `limit_reached` | 1 / 1 | 0 / `{}` | 0 |
| 2 | `limit_reached` | 1 / 1 | 0 / `{}` | 0 |
| 3 | `limit_reached` | 1 / 1 | 0 / `{}` | 7 个，全部 pending |

三次运行的 taskDigest 均为 `0d13f60ff203118458a61a65a5e8af9163267c55b926dbd7a911506ddfebfd53`，environmentDigest 均为 `05042f71f3f5d4f507d5f45df80bd3f03a3d68820ae270c1f489407f23b86b4b`，methodDigest 均为 `86f027370a4b05bd816abd4f9949d5ae081f6415176816a1a98b7de5438a86f9`，moduleConfiguration 为 `direct-v1`。buildDigest 按目录序号分别如下，不能当作同构建的效果对照：

1. `1dc7c27db0ba600c365709eb81f4c69b8a281cdadb1d60fa83ea7ede888019bc`
2. `1c4a2e839cdad305737159e4bbd3382a250b27b8973077c2578caa3cdeba2e23`
3. `0a7241a605c566fb4ad654c05924fcdc4d29e94f91040435976e5d5d1b9ac10b`

三名 peer 分别为 `researcher-1`、`researcher-2`、`engineer`，均未开始模型回合。三个日志均没有 `delivery_published`、`proof_ready_checked`、`task_checked` 或 `task_integrated` 事件。一次 planning dispatch 可以包含多次上游请求，不能将 dispatch 数当作请求数；目录 1 的两次请求及预算停止见[请求级校准报告](../examples/putnambench/CALIBRATION-REQUEST-BUDGET-20261019.md)。

这些记录没有显示 Lead 故障丢失了已启动 peer 的成果。目录 3 的七个 pending task 也不是已启动工作。因此，[阶段三](agensh-adoption-plan.md)所要求的实际损失证据尚未取得，不能用这三次运行支持扩大故障收尾行为。

旧运行没有保存足以逐时刻解释派发等待的观察记录。目录 3 只能确认“最终有任务且 peer 未执行”，其间是否受 owner、依赖、Lead、独立工作范围或其他条件限制仍为未知。最终的预算停止不能倒推出此前每段等待的原因；没有可连接的贡献链，也不能把缺失耗时填成 0 ms。

**贡献流已有字段及其边界**

以下描述此次核查时已有的记录能力。通用事件由 [run.ts](../src/solver/run.ts)写入 `at: Date.now()`；worker 事件另带 workerId。已核实的日志载体是上文的 `batch.json.logs/1.log`，不假定存在独立 `events.jsonl`。

| 环节 | 可读字段或事件 | 不能据此确定的内容 |
|---|---|---|
| 研究发布 | [DeliveryRecord](../src/solver/deliveries.ts) 的 id、producer、taskId、taskDigest、assignmentKey、commit、createdAt；`delivery_published` | createdAt 是宿主记录时间，不是模型首次发现时间；事件缺 taskDigest，须按 deliveryId 回连 |
| handoff 决定 | [ResearchHandoffDecision](../src/solver/researchHandoffs.ts) 的 id、deliveryId、status、taskId、taskDigest、contextDigest、waitsOn；`research_handoff_decided` | durable decision 无时间戳；需日志恢复决定时间，且不能丢弃 deferred、重激活及再次决定的历史 |
| 领取和执行 | `task_assigned` 带 workerId、taskId、seedCommit；`turn_started` 带 workerId、turnId | 领取不等于模型回合已启动；既有事件缺完整 assignment 身份，不能总能精确连接任务版本与首次执行 |
| ready | [ProofReadyRecord](../src/solver/proofReady.ts) 的 requestedAt、assignmentKey、taskDigest、snapshotCommit、sourceDigest、receiptIds、status、evidence | 无 frozenAt；requestedAt 不是冻结完成时间 |
| 检查 | `proof_ready_checked` 带 receiptId、commit、passed、conditional；task proof 的 verification 有 startedAt、checkedAt、durationMs | ready 到 verifier 开始包含停写、冻结和等待，现有时间不能进一步拆分 |
| 集成 | `task_integrated` 带 taskId、groupId、commit，批量另带 batchSize；节点保存 integratedCheck | 事件缺 taskDigest，节点无独立 integratedAt；需结合精确 proof、commit 及事件，不能只按 taskId 连接 |
| 集成队列 | `integration_queue_started.waitedMs` | 事件无 taskId，不能总能归属到某一成果 |

检查时间定义见 [verifier.ts](../src/math/verifier.ts) 的 MathematicsVerifierBatchResult；[archive.ts](../src/solver/archive.ts) 的 verification passthrough 保留这些字段。ready 可通过 receiptIds 和 snapshotCommit 与检查结果连接。delivery 内只保留 Lean receipt ID，完整检查时间应从 proof 或 integratedCheck 读取。

恢复或任务改版时，必须同时核对 taskDigest、assignmentKey、源码 commit、题目与环境身份。无法唯一连接、缺少日志或出现版本歧义时保留未知。已保存的检查记录描述历史证据，不替代恢复后的重新核验。

`notification_deferred` 只记录通知失败。发布、通知或 handoff 采纳都不能证明 peer 实际使用了知识；实际使用以检查得到的 references 为依据，模型自报另列。条件证明、辅助引理、研究交付和任务集成都不替代完整原目标所需的独立 S3 验收。

**模拟与后续验证口径**

[solverDispatchWait.test.ts](../tests/solverDispatchWait.test.ts) 使用可丢弃 fixture 验证等待观察合同，属于模拟证据。忙碌 owner 场景记录 owner 原因，完整计划显式改为共享后空闲 peer 可以领取；保存过的 assignment 仍然独占。用例还覆盖自定义策略拒选、越权建议、预检竞争、预算门控、停止结束及私有范围投影。它们不能补写旧运行的等待原因，也不能证明实际等待减少或解题提速。

新观察保存在 worker.scheduling.wait，经现有 inspect 展示，并产生去重的 dispatch_wait / dispatch_wait_ended 事件。observedAt 是观察时间，endedAt 是结束时间；两者都不证明该原因在首次观察前已持续多久。旧记录显示 unknown，已记录计划或任务身份失效显示 stale；每次最多列出 16 个候选，其余及 scope 隐藏项计入 omittedCandidates。

现有 handoff 发布、延期重激活、持久化和原子性回归验证各自的流程行为，不构成真实模型收益证据。

**实施与验证记录**

本轮完成 [module 设计](agensh-module-design.md) 的离线切片 1–3：统一职责 assessment、等待观察及检查报告、新 helper 共享归属指示。M4 增加 `shared-new-helper-ownership-v1`，M5 增加 `shared-responsibility-assessment-v1/recorded-dispatch-waits-v1`；现有 M5.assign interface 与 handoff 发布协议保留。

`bunx vitest run tests/solverDispatchWait.test.ts tests/taskResponsibility.test.ts tests/inspection.test.ts tests/solverTaskTypePreflight.test.ts tests/solverOrganization.test.ts tests/researchAdvance.test.ts`：142 项通过。新增职责合同用例 6 项，等待整合用例 12 项。`bun run typecheck` 与 `bun run build` 通过。

首次离线构建 ID 为 `ec50a7f3-0f16-4e98-9d5e-b71430f6c799`，[冻结 manifest](/home/lzh/.deepscientist-math-standalone-state/builds/ec50a7f3-0f16-4e98-9d5e-b71430f6c799/manifest.json) 的 SHA256 为 `e4728d32d10914c2bbc10425b3fcd10c2ea1f2b1fc26f83fe42387f6b27ac747`，其中保存全部源码输入及三个 bundle 的摘要。它包含工作树中其他进行中的修改，只标识首次离线验证构建，不能单独归因本计划的效果。

首次 `bun run test --maxWorkers=4`：4692 项通过、5 项失败、3 项跳过。三个失败文件及复核如下；首次核查未修改这些断言或其无关 implementation：

| 失败位置 | 实际结果 | 移除本次源码改动后的复核 |
|---|---|---|
| `frontierPriorityContext.test.ts:210`，10/100/500 alternatives 三项 | mandatoryBytes 为 20753/20732/20753，超过 20480 上限 | 相同三项失败 |
| `solverContinuationCapacity.test.ts:266` | 期待空 deliveries，实际保留 capacity research advisory | 相同失败 |
| `solver.test.ts:1788`，Lead handoff 恢复 | 在调用 next 前，pendingResearchHandoffs 期待 1，实际 0 | 相同失败 |

复核在 `/tmp/theorem-frontier-baseline-VFVDdb` 进行：复制当前其余源码与原样测试，将本次涉及的七份源码恢复为实施前 `/tmp/theorem-agensh-baseline-yv13fnka` 的副本。日志为 [baseline-vitest.log](/tmp/theorem-frontier-baseline-VFVDdb/baseline-vitest.log) 和 [baseline-lead-handoff.log](/tmp/theorem-frontier-baseline-VFVDdb/baseline-lead-handoff.log)。这说明五项失败不依赖本次源码改动；未保存全部并发修改的历史，不能进一步确定各自引入时间。单独复核实际依赖记录用例在当前与该快照均通过；全量轮已正常结束。

**五项失败修复**

2026-10-24 按用户要求修复上述失败。三个 frontier 用例的超限来自固定证明角色说明增长；[context.ts](../src/solver/modules/context.ts) 压缩与基础指示重复的文字，保留精确任务类型、数学推理、原声明保护、原始 def 只填写 body、条件前提约束及独立检查要求。20 KiB 上限和必需数学接口保持原有断言，M4 追加版本 `compact-proof-role-context-v1`。

另两项修正过时夹具：[solverContinuationCapacity.test.ts](../tests/solverContinuationCapacity.test.ts) 先确认续跑保留精确研究 advisory，再显式清空 live deliveries，继续验证完整笔记从不可变附件恢复；[solver.test.ts](../tests/solver.test.ts) 先确认仅修改已采纳目标的 revision 仍保留采纳，再改变真实前置引理合同，验证相同 handoff id 在新 context 下重新待决，以及失败请求恢复和重复交付幂等性。研究交付保留和 handoff 生产逻辑均未为迁就断言而改变。

修复后的聚焦验证通过：上下文 111 项，continuation 98 项，handoff 154 项，solver 局部 handoff 6 项，原始 definition 目标的独立验收 2 项。各组存在交集，不能相加作为独立用例总数。`bun run typecheck` 和 `bun run build` 通过。最终构建 ID 为 `aebc62ea-7886-4be9-a723-da551878424c`，[冻结 manifest](/home/lzh/.deepscientist-math-standalone-state/builds/aebc62ea-7886-4be9-a723-da551878424c/manifest.json) 的 SHA256 为 `13bb0218ccca14f439996463906c4847a9b8469c7d798c02da80bed96d521236`。与首次构建一样，它包含工作树中其他修改，不构成真实模型效果比较。

最终 `bun run test --maxWorkers=4` 全量通过：196 个文件通过、1 个文件跳过；4697 项通过、3 项跳过、0 项失败，耗时 405.25 秒。[完整日志](/tmp/theorem-five-failures-baseline-1g48gpxg/post-fix-vitest-final.log)、[类型检查日志](/tmp/theorem-five-failures-baseline-1g48gpxg/post-fix-typecheck-final.log) 和[构建日志](/tmp/theorem-five-failures-baseline-1g48gpxg/post-fix-build-final.log) 保存本轮结果。

上述五项失败修复阶段未实现贡献流聚合 interface，也未因缺少历史数据补造时间线。[真实模型调用的暂停约定](../examples/components/EXPERIMENTS.md)继续有效；本报告不启动校准、实验或旧运行。后续真实收益比较需另行冻结配置与身份，在获准执行后使用新的隔离运行。

**成果流诊断实施**

2026-10-24 按后续设计实现 [inspectStoredRun](../src/solver/storedRunInspection.ts) 高层 interface 与 [纯投影](../src/solver/contributionFlow.ts)，普通 inspect 支持显式指定互斥的 batch/log，并展示来源、逐次 handoff 决定、精确版本义务、assignment/start、ready/frozen/check/integration 与消费者引用。原始 reader 与 plan 导出保持独立。

新记录补充 run/problem/environment、task/version/assignment/seed、handoff 原 activation 和接纳后 planVersion、独立 Lean receiptIds，以及只写一次的 frozenAt。上文字段表描述最初核查时的能力；这些新增字段不会回填旧日志。历史决定和提案不依赖当前 inbox，旧任务检查继续可见；覆盖不足、冲突或缓存时间倒序不会生成伪耗时。

跨运行归因只展示本运行冻结 seed-history 的来源 run/state/build/commit，不读取可变的旧 checkpoint，不拼接同名任务执行史。检查与使用仍复用既有 recorded 语义，未恢复进程内信任或提供新验收。

成果流、stored inspection 与既有 inspection 聚焦 105 项通过；另有原事件生产路径聚焦回归通过。typecheck 与 headless build 通过，构建 ID 为 c11ac0e1-1303-40e3-a999-e8fb7da4ecd0，[冻结 manifest](/home/lzh/.deepscientist-math-standalone-state/builds/c11ac0e1-1303-40e3-a999-e8fb7da4ecd0/manifest.json) 的 SHA256 为 `0e7fb87bd7a097aa3bdc0cbd60c0c47990925cf59acd76f3fc4731a3d4543a80`。该构建包含工作树已有的其他修改，不单独归因本计划效果。

最终 `bun run test --maxWorkers=4`：198 个文件通过、1 个文件跳过；4760 项通过、3 项跳过、0 项失败，耗时 416.24 秒。[完整日志](/tmp/theorem-contribution-flow-tests.log)。测试使用可丢弃 fixture，未运行真实模型或恢复旧运行；它们证明诊断流程能力，不证明等待减少或解题收益。
