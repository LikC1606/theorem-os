# 协作路线、上下文与数学进展

本轮按 [Euler: Towards Human-Centered Multi-Agent Mathematical Discovery](https://arxiv.org/abs/2610.19864) 的局部障碍、任务交接、替代路线和人可检查进展四个方向，扩展 TheoremOS 原有的 M3–M5 与 S1。实现沿用现有任务图、隔离 worktree 和 Lean 回执，没有引入另一套 Agent 框架。本文描述已实现行为；尚无相同模型和预算下的真实解题成功率收益结论。

## 1. 局部阻塞与重开

研究任务可在 `RESEARCH.md` 的 JSON 结果中添加 `blockers`；所有分工也可在提示词指定的进度日志中追加：

```json
{
  "summary": "当前局部推理缺少索引控制，需要新的界。",
  "blockers": [{
    "mechanism": "missing-index-bound",
    "scope": "由短向量控制推出该饱和指标界的步骤",
    "evidenceRefs": ["RESEARCH.md"],
    "reopenOn": [
      {"kind": "contract-changed"},
      {"kind": "environment-changed"},
      {"kind": "dependency-checked", "taskId": "main_bound"}
    ]
  }]
}
```

`main_bound` 必须是当前分工的真实依赖。省略 `reopenOn` 时，宿主默认监听数学合同、环境和局部依赖的新检查证据。`mechanism` 应稳定描述失败机制，`scope` 应限定到具体推理；它们及数学输入共同构成复发标识。

同一任务或已选分支，在相同数学输入和环境下重复报告两次相同障碍后会暂停调度。一条消息中重复的条目只算一次。改写说明、增加 `revision`、重放相同证明回执或添加无关引理不能消除障碍；相关依赖得到新的、本进程重新检查的无条件集成证明后，宿主按记录条件重开。恢复读取 JSON 本身不授予新证据。

选定 `proofRoutes` 分支的阻塞只暂停该分支，其他分支可继续。没有选定分支时暂停的是该局部任务。Lead 看到阻塞后应提出判别实验、可行性检查或修改相关数学输入。已有证明和研究材料继续保存。这里的“暂停”只控制重复局部推理，不新增求解时间或轮次上限；局部反例始终是 advisory，不能将原题判为已反驳。

## 2. 完整必需上下文与省略清单

M4 在派发前编译上下文，必需部分包含：

- 冻结原题、假设、声明顺序和题目身份。
- 原始源码的 imports、namespace、section、局部实例及固定定义；原证明体擦除。
- 当前任务、分工版本、完整依赖接口和选定分支的精确闭合接口。
- 已存档检查证据及可检索的不可变 `commit:path` 来源。

已独立检查的无条件共享引理可封装别组私有实现。未解决的条件依赖或无关缺失接口不能被封装规则忽略。来源引用和存档检查状态用于交接，不授权跳过 Lean 检查。

默认提示词字节上限为 512 KiB，通过 M4 的 `ContextAccess.maxContextBytes` 可调整；这不是求解时限。必需项缺失、过期或超出预算时，在模型派发前明确返回 `math_context_missing_required`、`math_context_stale_required` 或 `math_context_mandatory_overflow`，不会静默裁掉假设。无效预算返回 `math_context_invalid_budget`。

多个任务重复引用同一声明时，必需的证据元数据通过完整引用字典去重。任务中的 `evidence.references.inputs`、`proof`、`statement` 数组按原顺序保存字典索引，字典保留每个对象的全部字段。`source.inputsFrom` 指向同任务的 inputs；输入提交取该任务的 `evidence.references.sourceCommit`，路径按 `path.posix.join(projectRelative, input.file)` 展开，字典中的项目路径已把反斜杠规范为 `/`。每项任务的类型、条件、回执 ID、来源提交和校验投影提交完整保留，来源提交不同的对象仍按各任务的来源解释。字典是必需上下文，不是省略记录，也不赋予历史回执新的验收权限。

研究发现、历史交付和 checkpoint 摘要按相关性选取。`CONTEXT-MANIFEST.json` 与 `state.json` 中各 worker 的 `lastContextManifest` 记录字节数、内容摘要、必需任务、已包含项和每个省略原因；每次编译还发送 `context_compiled` 事件。长 checkpoint 的摘要省略显式标注，完整笔记及历史提交仍可检索。该清单是宿主只读日志，不属于证明源码。

## 3. 替代证明路线

Lead 的计划和人工导出计划新增可选的顶层字段：

```json
{
  "proofRoutes": [
    {"id": "via_bound", "targetTaskId": "goal", "prerequisiteTaskIds": ["main_bound"], "closingTaskId": "closing_from_bound"},
    {"id": "via_structure", "targetTaskId": "goal", "prerequisiteTaskIds": ["structure"], "closingTaskId": "closing_from_structure"}
  ]
}
```

这些 ID 必须指向计划中已有任务：`goal` 是原题目标，所有前置项及 `closingTaskId` 都是具有完整精确 `type` 的 lemma。闭合引理的传递 `dependsOn` 必须包含该分支的全部前置项；跨组显式接口必须共享，循环依赖会被拒绝。

同一路线内的前置项是 AND，不同路线是 OR。原目标已有的 `dependsOn` 仍是额外的 AND 条件，宿主不会把两条替代路线改成目标必须同时证明的依赖。未暂停且取得新鲜无条件集成回执的路线才能使原目标就绪；恢复后的旧分工若指向失效分支，会重新选择就绪分支并重建一致的分工依赖。

闭合引理通过只允许继续尝试原目标。只有原目标自身通过严格检查，且 Lean 实际证明引用绑定到该版本闭合引理，报告才显示 `closed-by-original-check`。条件性桥梁、辅助引理、研究结论都不能替代原目标或官方评测。旧计划可以完全省略 `proofRoutes`；既有任务版本算法保持兼容。

## 4. 按数学义务变化报告进展

`math inspect` 的 JSON `mathematics` 和 Markdown 报告分别展示局部义务闭合／重开、原目标未闭合前沿变化、路线连接、阻塞暂停／重开，以及 advisory 研究结果。每条路线展示 `parkedBy`；暂停分支不会出现在可继续调度的候选中，尚未解决的数学义务仍保留。

`state.json` 保存最新数学快照和最近 64 条变化；完整已发出的变化保存在 `obligation_progress` 事件日志。首次快照建立 baseline，不把已有检查伪装成本轮新增成果。轮次、重试、worker 状态、相同证明的回执重放不算数学进展；完成研究笔记也不等于完成证明。没有完成百分比或预计证明时间。

所有快照和变化均标为 `recorded-not-replayed`、`acceptance: not-assessed`。畸形记录在恢复读取时拒绝。原题检查与匹配的最终评测独立决定验收，官方通过仍只出现在独立 Evaluation 结果中。

## 5. 交付回执与固定快照验收

研究日志和最终 `RESEARCH.md` 共用准入规则。显式 `math-result` fence 优先于说明用 JSON；没有显式结果时仍兼容旧结果对象和普通 Markdown。任务身份或字段无效时，宿主保存带具体字段路径的 `deliveryReceipts`，在当前分工继续纠正，不把协议错误当作数学路线失败。模型应在原分工日志追加完整修正版，通过 finding 的 `replacesReceipt` 指向待纠正回执；不要删除旧日志。通知失败不会丢失已保存的反馈，恢复后会按当前分工重新送达。回执只说明准入状态。

Lead 的 capacity/stagnation 请求保存稳定的 `requestId`、原始 `inputDigest` 和当前 dispatch nonce。未完成的请求续接沿用身份；完成回复须匹配当前请求和 nonce。有待处理 handoff/challenge 时，先走原有决策协议。没有独立可执行工作时，可提交上下文给出的 `assessment` 短回执和具体数学缺口。新输入可重新触发评估；worker 调度、inbox 变化或纯计划版本变化不会清除同一数学责任的无进展保护。探索耗尽要求当前全部 focus 实际完成，只有派发记录不算完成。

对于有类型的证明任务，worker 保存源码后，可向当前分工日志追加 `{"kind":"ready","summary":"saved proof ready for checking"}`，随即停止编辑并返回。宿主先持久记录请求，再等待 turn 结束、确认受管 writer 进程组停止，然后固定 Git commit 并独立检查。中断请求的应答和普通 `close()` 都不能代替停写确认；主动交回写权后的中断若未结束，复用现有 10 秒清理期限关闭会话。无法确认停止时，不提交或验收活动源码，回执记为失败，并持久隔离该 writer 的工作目录；禁止同目录重派或直接恢复，须恢复到新的隔离目录。普通验收失败可通过带新 id 的事件重试。自然 turn 完成仍兼容原交付协议。

`proofReadyRecords` 区分 `awaiting-freeze`、`frozen`、`checked`、`failed` 和 `superseded`，保存固定 snapshot、源码摘要和 Lean 回执。恢复未冻结请求必须在新会话重新提交 ready；已有 frozen snapshot 直接按原 commit 重新验收，不再启动写入 turn，也不替换为后续活动源码。条件证明明确保留依赖条件并释放当前 Engineer；它不能关闭原目标，仍须后续无条件集成与独立最终评测。停写确认针对本 runtime 管理的进程组；ready 协议要求合作式交回写权。

普通研究与证明任务在同一线程、同一冻结原题/环境及完整分工合同下使用增量上下文，持续携带当前诊断、待纠正回执和最新 inbox 引用。新线程、合同、seed 或 instructions 变化回到完整上下文。完整 M4 编译和 manifest 仍保留；增量消息不把相同任务摘要当作“没有新反馈”。

## 验证与运行边界

回归使用本地可丢弃 fixture 和 mock 模型／验证器，覆盖实际分工日志、计划修改、恢复、分支切换、严格原目标检查以及上下文日志的源码边界。未用真实模型测量解题收益。

2026-10-17 验证：`bun run test` 共 61 个文件通过，1316 项通过、2 项跳过（已有的 FUSE 与 Codex sandbox 显式启用用例）；`bun run typecheck`、`bun run build` 和产出 CLI 的 `--help` 均通过。最后的提示词澄清另由 19 项上下文测试与 2 项续跑测试复核。

M3、M4、M5 的方法版本已更新，旧构建的运行继续使用其冻结方法身份；本次没有迁移或重启现有求解运行。应用新构建需要遵守已有运行身份及恢复校验。最终候选审阅的完整作者排除和预留 reviewer 席位策略尚需单独处理，本轮不将其计为已修复能力。
