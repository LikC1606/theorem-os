# Agensh 吸收的 module 设计

日期：2026-10-23，更新：2026-10-24。状态：已实现切片 1–3 与后续成果流诊断，切片 4 按证据门槛暂缓。对应 [吸收计划](agensh-adoption-plan.md)，采用 codebase-design skill 的 depth、interface、seam、locality 和 deletion test；历史记录与证据限制见 [离线基线](agensh-offline-baseline.md)。

设计目标：让任务选择、宿主复检和等待解释共用同一份职责知识，减少分工等待，同时保持 M3 搜索、M5 职责、宿主执行及 M2/S3 验收各自的职责。第一轮深化现有 module；Lead 故障收尾单独演进。

**从当前调用链定位 seam**

当前普通任务派发的主路径是：

```text
M3.ready(完整任务图) → host 过滤准备/同步状态 → M5.assign(完整候选集)
  → host 校验建议 → 恢复草稿 / Git seed / Lean 类型预检
  → await 后复检 → 创建或延续 assignment → 模型请求前准入
```

同一组职责知识散在 [M5 资格筛选](../src/solver/modules/organization.ts)、[nextPeer 与预检复检](../src/solver/cooperation.ts)。它适合深化；Git、Lean 和模型会话仍留在现有执行路径。

以下判断保持各自含义：M3 ready 表示现在数学上可尝试；M5 matches 表示 worker 职责匹配；host admission 表示此刻允许实际执行；M2/S3 才决定证明接受。`hasAssignableTask` 判断现在可派发，`researchCanAdvance` 遍历未来依赖是否仍可推进，不能互换。

**三种 interface 设计及取舍**

方案 A：保留 `M5.assign → TaskRecord | undefined`，增加一个固定的 `assessTaskResponsibility → matches | blocked(reason)`。默认选择、host 复检及等待说明共用其 implementation。现有调用者和策略 interface 保持稳定，职责知识集中；它只解释职责，不承诺解释整个依赖图。

方案 B：建立短生命周期的 compiled frontier，公开 `offer(worker)`、`progress(roots)`、`recheck(offer)`、`observation()`。它能隐藏更多跨阶段判断，但要求调用者学习 snapshot、offer、失效、预检 reservation 和观察身份。对当前目标，新增状态投影与恢复语义的成本偏高；离线 inspection 也无法重建当时真实的 live worker 或进程内信任。

方案 C：将 `M5.assign` 改成 `selected(node) | unassigned(rejections)`，一次计算同时产出选择与诊断。常见调用者容易使用，但所有 M5 调用、替换策略和测试都需迁移；M3 未供给候选及 host 过滤原因依然不在该 interface 内。

| 设计 | Depth / leverage | Locality 与 seam 代价 | 本轮决定 |
| --- | --- | --- | --- |
| A：共享职责 assessment | 同一职责 implementation 支撑选择、复检、解释 | 保留现有 M3/M5 seam，只集中真正重复的规则 | 采用 |
| B：compiled frontier | 一次视图支持选择、未来推进与异步重验 | 新增跨阶段 interface 和派生身份，容易扩大为另一套调度器 | 暂缓 |
| C：带诊断的 M5 结果 | 选择与解释同次产生 | 修改现有可替换 interface，仍不能解释全部等待 | 有实测需求再考虑 |

采用 A。删除新 assessment 后，职责知识会重新散回默认选择、派发校验、恢复和预检复检，符合 deletion test。纯粹把 M3/M5 调用包进一个新 Scheduler，则只增加一层转发，不能产生同样的 depth。

**采用的 interface**

以下为已实现的 TypeScript interface；完整定义见 [organization.ts](../src/solver/modules/organization.ts)：

```ts
type ResponsibilityContext = Readonly<{
  tasks: readonly TaskRecord[];       // 完整图，不是 ready 或提示词裁剪视图
  groups?: readonly RouteRecord[];
}>;

type ResponsibilityAssessment =
  | Readonly<{ kind: 'matches' }>
  | Readonly<{
      kind: 'blocked';
      reason: 'role' | 'engineer' | 'owner' | 'saved-assignment'
        | 'review-independence' | 'running-duplicate';
    }>;

function assessTaskResponsibility(
  node: TaskRecord,
  worker: Pick<ResearchWorker, 'id' | 'role'>,
  context: ResponsibilityContext,
): ResponsibilityAssessment;

// 保持现有 M5.assign interface；筛选改为使用上述 assessment。
function assignSharedResearchTask(
  ready: readonly TaskRecord[], worker: ResearchWorker,
  peers: readonly ResearchWorker[], groups?: readonly RouteRecord[],
  tasks?: readonly TaskRecord[],
): TaskRecord | undefined;
```

`assessTaskResponsibility` 放在现有 [organization.ts](../src/solver/modules/organization.ts)。它是固定 implementation，host 直接引用，不从可替换的 `modules.M5` 对象取校验函数。普通不匹配返回结果，不抛异常；多个约束同时命中时按固定顺序返回首个原因，不声称穷尽所有原因。

现有 assign 的可选 tasks 参数保留兼容，生产 host 始终显式提供完整图；只有已知 ready 就是完整图的简化 fixture 才可依赖默认值，不能以缺少关联任务的输入判断审阅独立性或重复问题。

它隐藏角色及 typed helper 限制、已有 capacity exploration 例外、owner、saved assignment、指定 Engineer、独立可行性审阅、重复问题判断。默认 M5 的排序、最后槽位保留和 planned work 优先仍使用完整候选集；不能用逐任务 singleton 选择替代实际排名。

它不持有状态、不做 I/O、不生成 assignmentId，不修改 seed、源码、任务图或预算。同步调用不保留输入引用，不 JSON/structuredClone 复制含证明回执的图；原有进程内信任标记继续由证据路径读取。

`matches` 只表示职责匹配：不等于 ready，不授予领取权，不是证明回执。M3、host 生命周期、源身份和预算判断仍各自执行。

**调用顺序与失效语义**

```ts
const tasks = archive.tasks;
const ready = modules.M3.ready(tasks, groups).filter(hostAvailable);
const node = modules.M5.assign(ready, worker, allocationPeers, groups, tasks);

if (!node) {
  // 真实未选中分支：组合当时已发生的判断，再走原有补位/等待路径。
  recordWaitObservation(ready, worker);
  return existingNoSelectionPath();
}

// 固定 host 检查：候选成员、pending、数学可启动、路线及职责等。
assertHostCandidate(node, ready, worker);
await existingDraftSeedAndTypePreflight(node);

// 沿用现有 current 检查；读取 await 后的图与运行状态。
if (!preparationCurrent() ||
    assessTaskResponsibility(node, worker, currentGraph()).kind !== 'matches')
  return RETRY_DISPATCH;

// 同步保留最终 M5 复检和现有 assignment 落盘路径。
return existingCommitAssignment(node, worker);
```

上述 host 函数名仅说明现有 implementation 的位置，不是拟新增的公共 interface。`assertHostCandidate` 内复用固定 assessment，同时保留独立的 M3 成员、路线、scope 与 source 检查；M5 返回越权或候选集外任务，仍报 `math_task_assignment_invalid`。

跨 await 后，task 存在性与 digest、依赖版本、route、canonical/seed、Git HEAD、worker access、环境、assignment、归属、预算及生命周期变化均按原有规则重试。owner 变化必须单独判断，不能假设数学 digest 包含调度归属。过期返回 `RETRY_DISPATCH`，不记录为数学失败；类型无效仍维持原有 blocked/advisory 语义。

`hasAssignableTask` 继续查询当前候选；`researchCanAdvance` 保留未来依赖遍历。二者可通过现有回调使用同一职责 assessment，但不强制读取相同的 ready 列表或 peer 集合。现有全候选选择与预检后的 singleton 资格复检用途不同，予以保留。

**状态所有者与诊断**

| 状态或事实 | 唯一所有者 | 其他 module 如何使用 |
| --- | --- | --- |
| 正式任务图、数学路线、handoff 决定 | 现有 Lead 决策及 host CAS 接纳路径 | M3/M5 读取，不自动改图 |
| assignment、占用、预检、canonical、恢复状态 | 现有 CooperativeResearch host | assessment 不持有副本；选择只是建议 |
| 会话、模型请求、预算结算和停止 | 现有 research 执行路径 | 不由 M5 接管 |
| 新鲜证明信任与最终接受 | M2、进程内证据身份及 S3 | 诊断和存档 JSON 不授予权限 |
| 某时刻为什么等待 | host 在真实分支产生的只读观察 | inspect 展示记录，恢复与派发不使用观察授权 |

等待观察优先沿用事件与 worker.scheduling，仅缺少必要事实时补可选字段。第一版只承诺以下口径：

| 实际观察 | 可以报告 | 不能据此推断 |
| --- | --- | --- |
| M3 没有候选 | no-ready-task | 必然是依赖、路线失败或 Lead 拖延 |
| host 排除候选 | 实际命中的 preparing、synchronization 等条件 | 原数学路线无效 |
| 职责 assessment 不匹配 | 同一 implementation 返回的首个 reason | 移除 owner 就可执行，或已释放 assignment |
| M5 未选中但基础职责匹配 | policy-no-selection，细因未知 | 擅自归因为 owner 或依赖 |
| 请求准入被预算阻止 | budget-gated | 有可用预算却闲置 |

记录 observedAt、worker、所涉 taskId/taskDigest、当时 planVersion 和原因；每次最多保留 16 个候选并记录省略数。先保存 host 内部观察，再按现有 scope 投影后交给 worker。`dispatch_wait` 与 `dispatch_wait_ended` 标出观察区间；停止时保存 endedAt 以保留最后的历史观察，重复停止不重复结束事件。未知起点保留未知，观察区间不冒充原因的完整持续时间；scheduling.since 不能冒充某个 blocker 的起始时间。相同输入和原因不随 200 ms 轮询重复发事件。

inspect 标记 recorded-not-replayed；旧记录无观察时显示 unknown，版本变化后保留历史身份，不把旧等待原因写成当前事实。离线不重跑可替换 M5，也不建立另一张资格表或持久调度缓存。

**任务供给与 handoff 的接入**

在 M4 的 Lead 指示中明确：新建、未开始、无专属上下文需求的引理优先保持共享领取；显式归属和已有 assignment 继续保留。删除 ownerId 不释放已有 assignment，首版不自动重派保存中的工作。

handoff 继续使用 [现有完整发布 interface](../src/solver/handoffPublication.ts)：一个 dispatch 展示的全部请求都要显式决定，未展示及晚到项排队。回合内发布、CAS、通知已实现；先量延迟，有具体瓶颈才调整批次或呈现，不新增发布协议。

优先使用已检查成果、早期消费者连接与失败记忆，继续沿用 plan/continuation、精确条件检查和 scoped advisory。它们不纳入职责 assessment；不能为了填槽位制造缺乏消费者的 helper。

**Lead 故障收尾：独立的后续设计**

外部仍使用现有 `runResearchWorkers(input)` interface。收尾状态机放在其与 CooperativeResearch 的既有 host implementation 内，不向 M3/M5 增加故障模式参数；本轮不先抽象通用故障协调器。

```text
running → Lead 服务故障 → 暂停新派发、截取已确认启动的任务回合
       → 确认 Lead writer 停止 → settling → 保存固定成果并结束
       → 任一硬停止条件 / 无有限期限 / 停写未确认 → 原停止与隔离流程
```

实际启动以 `MathAgentSession.run` 的 onStarted(turnId) 为准；当前 `cooperation.started()` 是请求前准入和计数，active/claimed/opening 也不能替代启动确认。在现有 active 记录上补实际 turn 身份和已冻结期限，不再建立一张独立任务表。故障时尚无启动确认、之后才迟到的回调，不进入允许收尾的集合，仍关闭并确认相应 writer。

仅保留故障前已启动的 task 回合完成当轮，不续派、不增加预算。有限期限沿用已有 turn 与 run deadline 的较早者；均无限则保持当前中止行为。Lead writer 确认停止前不推进新的 canonical 写入；peer 已完成产物可等待固定快照处理，不凭活动源码授予接受。

停止确认须来自受管进程的回执。当前普通 close() 不等价于确认停止；实施时要在释放 session 引用前利用现有 stopForFreeze/进程确认能力，无法取得则回退原中止行为。用户停止、失锁、verifier 不可用及 writer 隔离继续优先。

保存的收尾状态只用于说明故障和恢复；重启不恢复“进程仍活着”的许可。恢复后重新检查固定成果，后续规划、审阅及 S3 沿用原路径。本阶段可以保存部分成果并仍报告 Lead 故障，不新增绕过所需审阅的最终成功路径。

**依赖、test seam 与实施切片**

| 依赖类别 | 设计处理 | 验证方式 |
| --- | --- | --- |
| In-process：职责、排序、等待观察 | 直接调用纯函数与既有 M3/M5，无新 adapter | interface 的可观察结果 |
| Local-substitutable：Git、Lean、预检 | 留在现有 host implementation | 可丢弃 worktree、现有预检 fixture 与集成用例 |
| True external：真实模型 | 复用 MathAgentSession 的真实与 mock adapter | mock 的启动、失败、迟到和停止；不调用真实模型 |

没有 remote-owned 依赖，不引入 HTTP/队列 port。M3 的现有策略差异已在现有 seam；无需为未来用途发明 registry。新 assessment 的参数只提供计算所需的现有图，不把 I/O adapter 塞进纯计算 interface。

实施分四个可独立检查的切片：

1. 已完成：在 organization.ts 集中职责 assessment，默认 M5、host 选择/恢复/预检复检和请求前准入复用；保留 assign interface、排序与现有例外。
2. 已完成：真实等待分支补必要观察，并接入现有 archive/inspect。旧记录缺失显示 unknown；已记录身份不匹配显示 stale；离线不重放 M3/M5。
3. 已完成离线部分：新建且不需要专属上下文的 helper 优先省略 ownerId；已有归属和 assignment 不自动改写。核验现有 handoff 路径，更新 M4/M5 版本身份；真实效果比较继续暂停。
4. 暂缓：三个已知校准运行均无 peer 回合启动，未取得 Lead 故障损失已启动成果的证据。保留当前中止行为；后续改变构建或方法时准备新运行，不迁移或重启旧运行。

测试跨 assessment、M5.assign 与 CooperativeResearch.next 的现有 seam，覆盖忙 owner、saved assignment 不迁移、Engineer、独立审阅、重复工作、非法自定义 M5、预检期间合同/归属变化及竞争分配。保留 future canAdvance、条件连接、Git/Lean 集成和 M2/S3 回归。

用新 interface 用例替换重复的内部实现断言，不再为每个布尔条件和 reason 字段铺镜像测试。Lead 收尾另测真实启动与仅预留的区别、迟到启动、有限期限、停止未确认、用户取消、恢复不重复集成，以及条件证明不升级。

第一切片主要改 organization.ts 与 cooperation.ts；观察切片再按实际缺口修改 cooperationCore.ts、archive.ts、inspection.ts；策略切片涉及 context.ts 与 modules/index.ts。首轮设计没有要求新增生产 module 文件。运行时边界的实施需完成相应回归、typecheck 与 headless build；真实实验沿用 [暂停约定](../examples/components/EXPERIMENTS.md)。

**后续切片：成果流诊断**

调用者只需学习一个高层 interface，详见 [storedRunInspection.ts](../src/solver/storedRunInspection.ts)：

~~~ts
inspectStoredRun(run, { journal: { batchFile } }); // 或 { logFile }，也可省略 options
~~~

这个 seam 隐藏结果与 checkpoint 读取、唯一 batch 映射、有界日志前缀解析、run 身份绑定、冻结续跑来源和成果流投影。现有 `readRunInspection` 保持轻量，人工修改、续跑初始化、比较与 plan 导出继续复用，不附带日志 I/O。CLI 普通 Markdown/JSON 改用高层 interface。

纯 implementation 位于 [contributionFlow.ts](../src/solver/contributionFlow.ts)：输入已读取的 state 与可选 journal，输出带证据路径或行号的 `recorded | unknown | ambiguous`。它复用 researchHandoffs、buildProofContinuation 和 recordedTaskProofStatus，隐藏多源 alias、逐次决定、任务版本与 assignment/start、ready/frozen/check/integration 的关联。删除这个 module 后，这些知识会重新散落到 CLI、展示和测试，符合 deletion test。

`sources` 保留被替换 delivery 的提案；`decisionOccurrences` 保留全部可读日志决定，`storedDecisions` 单列无时间戳的最新存档；`obligations` 按 taskId/taskDigest 分组。相同检查存于多个字段时只展示一个 check 与多个存放路径。M3/M5、模型会话和证明验收路径不读取该派生报告。

耗时只用精确身份和可核对的两端。决定到启动还要求原 activation/context、同一已接纳 planVersion、唯一决定及有序 assignment/start。重复派发不选择一个“最像”的时间；缺失、时钟反转和事件顺序矛盾不补零。worker 快照与合并检查按各自 commit/source/Lean receipts 记录；集成事件的 producer seed 与 canonical check seed 含义不同。ready ID 与 Lean receipt ID 保持分离。缓存检查早于 ready 时，回执时间仍可见，等待耗时未知。

必要的新记录只追加诊断字段：run/problem/environment envelope，派发与启动的精确 task/assignment/seed，发布和集成的版本及收据，handoff 原 action activation 与接受后 planVersion，以及首次成功冻结的 frozenAt。恢复与重复 freeze 不改写这个时间，不改变数学合同、策略版本或进程内信任。

续跑归因只读当前 runtime 的冻结 continuation snapshot 与 seed-history，不打开其 source.stateFile；源路径是归因信息。来源损坏、缺失、非 seed 或身份不匹配显式 unknown。同名任务在不同运行中的执行史不合并。所有结果标记 recorded-not-replayed，缺失实际引用不能解释为无用或未使用。

验证跨高层 interface、纯投影及原运行时 seam：缺失/混合/截断日志、冲突 batch、错 run/problem/environment、多来源、历史决定与旧版本、重复派发/启动、条件检查、缓存时间、合并检查、冻结续跑来源，以及 CLI plan 不读日志。源码保持无调度器、事件总线或持久增量投影；Lead 故障收尾继续暂缓。
