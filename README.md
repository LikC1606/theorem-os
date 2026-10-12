# DeepScientist Math

独立的数学证明 CLI。流程只有：准备公开题目 → Codex 在隔离 worktree 中写证明 → 宿主验证冻结提交 → 集成并独立评分。

没有 Core、Team、前端、HTTP 服务、角色队列或 MCP 编排。默认模型为 `gpt-6.1-sol`，推理强度为 `xhigh`。

## 使用

需要 Linux、Bun、Node.js 22+、Git、Codex CLI，以及已准备好的 Lean/Mathlib 环境。

```bash
bun install --frozen-lockfile
bun run build

bun run math bootstrap-imo \
  --repo /absolute/humanfia-imo2026 \
  --problem imo2026_q3 \
  --workspace /absolute/new-proof-workspace

bun run math run \
  --build-manifest /absolute/build/manifest.json \
  --workspace /absolute/new-proof-workspace \
  --task-file /absolute/public-task.md \
  --workers 4 \
  --output /absolute/private-results/run.json
```

`build` 生成 `out/main/math-solver.js`、`search-lean.js` 和 `check-lean.js`，并输出 `buildManifestRef`。源码和 bundle 均校验哈希；修改源码后需要重新构建。后两个 bundle 可挂载到隔离环境，供模型检索和编译诊断。

`run` 默认使用 `--workers 4`：1 个 Lead、2 个 Mathematical Researcher 和 1 个 Lean Engineer。Lead 写任务依赖图；Researcher 处理必要引理、替代路线或关键猜想；Engineer 持续负责原题证明节点。任务按依赖就绪并行执行，各自使用独立会话和 worktree，完成一项便检查、交付、合并一项。固定完整候选交给空闲 Researcher 切换为 Independent Reviewer，只读审阅；审阅意见与 Lean 证据分别保存，最后仍独立验收原题。`--workers 1` 使用单 agent；`2` 使用 Lead 和可兼任研究、审阅的 Engineer；`3` 使用 Lead、Researcher 和 Engineer。Lead 计入总人数，最多 3 个 worker 并发。

任务图、负责人、状态、固定源码版本、检查反馈和审阅保存在 `<output>.runtime/state.json`，进度事件写入标准输出。状态保存在 `<output>.runtime/` 私有目录中；用相同参数加 `--resume` 恢复各 agent 的证明、会话、失败记录和累计用量，恢复时不能改变 worker 数量。环境准备和依赖预编译使用独立的 `--prepare-timeout-seconds`（默认 1800）；之后才开始 `--max-run-seconds`（默认 1800）的共享解题预算。`--max-turns` 默认 20，计入所有 agent 的总轮次；`--max-turn-seconds` 默认 180，长轮次停止写入后由宿主检查已保存源码。时间和轮次限制可用 `0` 关闭。`check-lean --workspace DIR --file FILE` 提供默认 90 秒的局部诊断，保留失败退出码和最早错误；局部诊断不代表最终验收。`--startup-only` 只检查准备条件，不调用模型。历史 Team 状态不兼容，需要创建新运行。

`--method lemma` 启用辅助引理方法：先尝试原题，遇到失败后提出一个引理，分别检查条件性连接和引理证明，再完成原题。模型在 `RESEARCH.md` 的单个 `math-lemma` JSON 代码块记录 `proofPath`、原题完整名称 `target`、引理完整名称 `lemma` 和完整闭合 Lean 类型 `type`。引理使用普通 `:=` 证明，置于同一文件的目标之前；目标通过引理的局部名称引用它。宿主在临时 worktree 中将引理替换为目标的显式参数来检查连接，移除原题定理来独立检查引理及其完整类型。未证引理不能触发原题通过；所有操作共享原有预算，恢复时重新检查辅助义务。默认仍为 `--method direct`。

原题声明、已有定义和受保护文件不能修改；只有全部目标通过宿主 Lean 内核检查才进入评测。IMO 使用集成后再次执行的内核检查，Lean-Eval 使用独立官方评分；可用 `--evaluator-command` 指定额外评测。模型的完成消息不代表证明通过。

其他命令通过 `bun run math --help` 查看，包括 `bootstrap-lean-eval`、`freeze-retrieval` 和 `summarize`。

Codex 默认使用 `~/.config/deepscientist/math-sol-codex`；`CODEX_HOME` 可以指定已有 profile，`--codex` 可以指定可执行文件。认证信息不会复制到项目。数学环境默认读取 `~/.config/deepscientist-math/math.env`，可通过 `DEEPSCIENTIST_MATH_ENV_FILE` 指定。

使用外部隔离启动器时，按每个子进程的 `DEEPSCIENTIST_MATH_WORKER_ID` 和 `DEEPSCIENTIST_MATH_WORKER_WORKTREE` 绑定对应工作区和独立会话存储；不要把启动器固定到第一个 worktree。各 agent 通过宿主分发的任务、固定成果和检查反馈交换信息。

## 源码

- `src/solver/run.ts`：准备环境、恢复身份、集成和独立验收。
- `src/solver/research.ts`：多个 agent 的异步调用、共享预算、取消和职责切换。
- `src/solver/cooperation.ts`：依赖任务、逐项交付、主线集成、审阅和局部版本更新。
- `src/solver/cooperativeProof.ts`：指定义务的隔离检查与声明合并。
- `src/solver/lemma.ts`：引理提案、条件性连接和引理证明的隔离检查。
- `src/solver/modules/`：按[设计文档第 2、4 节](https://ucnndba7qjef.feishu.cn/docx/Zy8rdyGJXonkChxYsLecn2Rbntg)拆分的可替换运行模块。
- `src/runtime/codexSession.ts`：Codex stdio 协议适配。
- `src/math/`：数学契约、题目准备、Lean 验证、证明环境和结果汇总。
- `scripts/mathematics/`：CLI 命令入口。

| 模块 | 实现 | 输入与交付 |
| --- | --- | --- |
| M1 证明构造 | `modules/execution.ts` | 题目、上下文、操作与执行者 → 候选版本、来源及待检查义务 |
| M2 检查与反馈 | `modules/evidence.ts`、`cooperativeProof.ts` | 完整候选或局部义务 → 绑定目标、固定版本和环境的 Lean 证据；独立审阅分别记录 |
| M3 搜索决策 | `modules/search.ts`、`modules/value.ts` | 状态、依赖、估计和预算 → 可推进任务、继续/停止及重试计划 |
| M4 上下文选择 | `modules/context.ts` | 题目、当前任务及可见成果 → 指令、反馈和题目/回执/语料来源标识 |
| M5 协作与复用 | `modules/organization.ts` | 选定任务与可用 agent → 职责匹配、明确写入负责人及隔离 worktree |
| S1 任务与成果档案 | `archive.ts` | 保存和恢复任务身份、候选、回执、失败及运行状态 |
| S3 环境与评测合同 | `problem.ts`、`evaluation.ts`、`src/math/` | 冻结任务与环境，集成后重新检查原题并执行独立评测 |

agent 的常用协议只有两步：读取任务，写出成果。需要结构化回复时，在 `RESEARCH.md` 中保留一个 `math` JSON 代码块；普通说明可写在代码块外。

| 当前职责 | 需要交付什么 |
|---|---|
| Lead | `{"tasks":[...]}`。任务只需 `id`、`kind`、`objective`；形式任务加 `theoremName`，引理加闭合 `type`，有依赖时加 `dependsOn`。 |
| Researcher | `{"summary":"发现、依据与缺口"}`；需要 Lead 决策时加 `needsDecision: true`。 |
| Lean Engineer / 引理证明者 | 保存指定 Lean 证明，写简短笔记后返回，无须填写证明交付 JSON。 |
| Reviewer | `{"verdict":"accepted","summary":"审阅意见与依据"}`，有问题则用 `changes_requested`。 |
| 声明回译 | `{"mathematics":"数学表达、假设及相关定义"}`。 |

`dependsOn` 默认空，`revision` 默认 0；原题目标的 `proofPath` 自动确定，辅助引理在只有一个可写 Lean 文件时也可省略。Lead 的计划仍须恰好覆盖原题目标，并保持依赖无环。任务、版本、环境、检查回执和预算由宿主绑定，无须 agent 重复填写。提示词只说明当前职责；可选字段仍可显式设置。

需要提前共享时，向提示词指定的分工日志追加一行 `{"summary":"进展或卡点"}`；提前交付证明则先提交源码，再追加 `{"kind":"proof","commit":"完整 Git 提交","summary":"成果"}`。宿主自动补充消息编号、任务和版本，去重并随完成随检查、接入和通知；无须等待 Lead 或整批任务结束。`COOPERATION.json` 提供只读同伴状态。旧的 `math-plan`、`math-result`、`math-review` 等代码块及带版本字段的 `DELIVERIES.jsonl` 仍可读取，以便已有运行继续恢复。

<details>
<summary>可选协作配置与检查机制</summary>

形式任务可设 `conditional: true`，基于固定类型的待证引理先构造父证明；检查只在临时投影中添加显式引理参数。条件性成果保留未证义务，依赖闭合后自动组合并重检普通证明。猜想、研究、草图和审阅意见不能授予原题通过状态。

协作运行中可向 `<output>.runtime/edits.jsonl` 追加一行 `{"id":"edit-1","baseVersion":"state.json 中的 cooperation.planVersion","tasks":[完整的新任务表],"groups":[完整的新路线配置]}`。服务校验基准版本、原题覆盖、职责和无环依赖后应用修改，公布受影响的任务并停止相关旧分工；无关工作继续。可以修改引理、路线、负责人、任务暂停状态和路线预算。旧交付保留为历史，不能进入新版证明；审阅对象被修改后须重新审阅。冲突或无效修改写入 `cooperation.edits` 并发出拒绝事件。交付和修改日志只追加，每行以换行结尾；部分写入等待完成，游标随运行恢复。

`cooperation.edits` 分别记录 `received`、`applied`、`rejected`，附收到/应用时间、计划版本和受影响任务；`COOPERATION.json` 展示最近 16 条修改，完整历史保存在 `state.json`。`applied` 表示新计划已建立，证明检查另见 `recheck`：逐任务区分待检查、条件性通过、普通证明通过、失败、移除或被后续修改取代，并链接最近检查的源码提交、环境与 Lean 回执编号。仅调整暂停、负责人或预算时显示 `not-required`。恢复运行先重新验证已有证明；旧检查记录保留为历史，不能据此显示当前检查已通过。收到但未应用的修改可从追加日志继续处理，同一编号只应用一次。声明审阅和原题独立验收仍分别记录。

形式任务可设置 `statementReview: true`，并用 `informalStatement` 写明所需结论、假设和量词。声明固定后即可送审，证明任务可并行继续：先在独立目录和新会话中只依据 Lean 声明及定义回译，再由另一个新会话比较保存的回译与数学原意。回译输入去除原始说明、注释、证明、研究日志和 Git 历史；不发送同伴通知。每阶段均计入原题及路线回合预算。`COOPERATION.json` 并列展示原意和回译，`statementReviews` 保存版本、定义快照、环境标识和审阅结果；定义或任务版本变化会使旧结果作废，纯证明体修改保留声明审阅。恢复时可复用完成的回译，未完成阶段重新开会话。被请求的声明审阅须通过才能最终验收，但不能替代 Lean 证据或完整证明审阅。这是上下文与工作目录隔离，沿用现有 Codex 沙箱权限。

已检查的普通形式任务会保存 Lean 从 elaborated 声明和证明项抽取的项目内实际引用，包括传递使用和隐式实例；`actualReferences` 与计划中的 `dependsOn` 分别展示，绑定源码提交、声明/定义摘要和环境标识。Lead 修改辅助定义时，仅重检引用或上下文变化的已检任务；没有完整引用报告、生成常量无法定位、上下文或环境变化时采用保守检查。声明审阅获得可靠声明引用后，无关定义变化可保留已有审阅。同一运行内修改任务计划时，已集成证明按可靠的实际引用传播失效；未完成任务、条件性证明和引用不完整的任务仍按计划及分工中的依赖保守处理。保留的证明可继续供后续任务使用，证明交付固定记录实际依赖版本及原始提交，受影响的旧交付标为历史。运行恢复会重新验证证明回执，存档中的引用不能授权跳过检查；恢复前修改计划仍先保守处理计划依赖。条件性父证明须在依赖闭合后取得普通证明的实际引用。最终原题检查仍独立执行。

停止后仍可编辑 Lead 的 `RESEARCH.md` 并 `--resume`，沿用相同的依赖更新和重检规则。

计划可增加 `groups`，每组记录 `id`、数学目标 `objective`、`status`（`active` / `paused` / `stopped`）、路线 `revision`，以及可选 `engineerId`、`maxTurns`、`maxConcurrent`。任务用 `groupId` 绑定路线；不配置时使用默认 `main` 组。多个组时成果默认 `sharing: "group"`，跨路线引用需将生产任务标记为 `sharing: "problem"` 并在消费者中写入 `dependsOn`。宿主提供同组任务与已检查共享成果的摘要，附生产者、前提类型、依赖和版本；其他路线的私有辅助源码不进入任务的初始源码。各组共享现有 worker 名额，一条路线的原题节点持续交给指定 Engineer。

`maxTurns` 统计该组 worker 的任务尝试，恢复后累加；`0` 表示不给该组新任务。不设置则只受原题总预算限制。`maxConcurrent` 为 1–3，限制该组同时执行的任务，包括提前交付后仍在运行的生产者。Lead、最终审阅和通知引入的模型用量仍计入原题总预算。暂停、停止或预算耗尽保留已有成果，并允许无关路线继续；运行中追加修改，或停止后改计划并 `--resume`，可恢复路线或追加预算。修改路线目标或 `revision` 会更新该组任务及跨组依赖者；调整状态或预算保留数学成果。

</details>

`src/solver/modules/index.ts` 绑定默认模块及版本。`runSolver(args, root, modules)` 支持独立替换模块；模块版本参与恢复身份，宿主仍固定执行源码边界检查、总预算限制和最终验收。模块输出预测、生成候选或完成集成都不能直接授予原题通过状态。

两种方法均可使用协作团队；单 agent 时保留直接证明和条件引理流程。M3 默认返回未校准估计，M5 按职责分配选定任务；`cooperation.ts` 作为方法运行循环处理异步通知、逐项集成和版本。辅助引理回执记录各自检查的投影提交、原候选提交和源码摘要；最终验收仍独立检查全部原题目标。S2 跨任务学习尚未实现。

辅助义务的完整投影内容、提案和环境都一致时，可复用本进程已检查的成功回执；研究日志不参与证明检查。证明输入或环境改变即重新检查，恢复后的档案回执不能授权复用。同一失败义务连续两次没有证明输入变化时，控制器重新分解路线，并保留失败原因供下一轮参考。

测试不调用真实模型。`bun run test` 验证运行边界；`bun run typecheck` 检查接口。
