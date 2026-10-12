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

Lead 在自己的 `RESEARCH.md` 中保存一个 `math-plan` JSON 代码块。任务包含 `id`、`kind`（`research` / `lemma` / `goal`）、`objective`、`dependsOn`、`revision`；形式任务还包含 `proofPath`、`theoremName`，引理要求完整闭合 `type`。任务图须无环并恰好覆盖全部原题目标。暂停运行后可修改这个计划，再用 `--resume` 继续；修改任务版本会使它和依赖者重新检查，无关成果保留。原题陈述和前提仍固定。研究交付使用 `math-result`，固定版本审阅使用 `math-review`；二者均不能代替 Lean 证明。

计划可增加 `groups`，每组记录 `id`、数学目标 `objective`、`status`（`active` / `paused` / `stopped`）、路线 `revision`，以及可选 `engineerId`、`maxTurns`、`maxConcurrent`。任务用 `groupId` 绑定路线；不配置时使用默认 `main` 组。多个组时成果默认 `sharing: "group"`，跨路线引用需将生产任务标记为 `sharing: "problem"` 并在消费者中写入 `dependsOn`。宿主提供同组任务与已检查共享成果的摘要，附生产者、前提类型、依赖和版本；其他路线的私有辅助源码不进入任务的初始源码。各组共享现有 worker 名额，一条路线的原题节点持续交给指定 Engineer。

`maxTurns` 统计该组 worker 的任务尝试，恢复后累加；`0` 表示不给该组新任务。不设置则只受原题总预算限制。`maxConcurrent` 为 1–3，限制该组同时执行的任务。Lead 和最终审阅仍计入原题总预算。暂停、停止或预算耗尽保留已有成果，并允许无关路线继续；暂停运行后修改计划并 `--resume` 可恢复路线或追加预算。修改路线目标或 `revision` 会更新该组任务及跨组依赖者；调整状态或预算保留数学成果。

`src/solver/modules/index.ts` 绑定默认模块及版本。`runSolver(args, root, modules)` 支持独立替换模块；模块版本参与恢复身份，宿主仍固定执行源码边界检查、总预算限制和最终验收。模块输出预测、生成候选或完成集成都不能直接授予原题通过状态。

两种方法均可使用协作团队；单 agent 时保留直接证明和条件引理流程。M3 默认返回未校准估计，M5 按职责分配选定任务；`cooperation.ts` 作为方法运行循环处理异步通知、逐项集成和版本。辅助引理回执记录各自检查的投影提交、原候选提交和源码摘要；最终验收仍独立检查全部原题目标。S2 跨任务学习尚未实现。

辅助义务的完整投影内容、提案和环境都一致时，可复用本进程已检查的成功回执；研究日志不参与证明检查。证明输入或环境改变即重新检查，恢复后的档案回执不能授权复用。同一失败义务连续两次没有证明输入变化时，控制器重新分解路线，并保留失败原因供下一轮参考。

测试不调用真实模型。`bun run test` 验证运行边界；`bun run typecheck` 检查接口。
