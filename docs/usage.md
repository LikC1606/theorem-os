# TheoremOS 运行指南

[返回 README](../README.md) · [组件替换示例](../examples/components/README.md)

这里保留手动准备题目、配置运行环境、恢复实验和调整协作计划的完整说明。第一次使用可以先跑[小题示例](../examples/getting-started/README.md)，再尝试 [IMO2026 Q1](../examples/imo2026/README.md)。

## 环境诊断与小题示例

第一次使用可以先运行只依赖 Lean 标准库的[小题示例](../examples/getting-started/README.md)，
再准备 Mathlib 和公开题目。诊断命令会检查本地工具、Codex 登录、Bubblewrap 权限，以及指定项目的编译器和依赖：

```bash
bun run math doctor
bun run math doctor --project /absolute/path/to/lean-project
bun run math doctor --lean-only --json
```

`--lean-only` 跳过 Codex 检查，适合预设回放。`--network` 可额外检查 provider 的 HTTP 连通性，
不携带认证信息，也不发起推理。默认诊断不会连接模型服务；登录状态和网络可达都不能保证模型访问权限。
必需项失败时退出码为 1；警告仍需按具体题目的要求处理。FUSE 工具只在使用外部依赖时需要，
能打开设备也不等于实际挂载一定成功，完整运行条件继续由启动预检确认。

## 手动准备与运行

### 1. 准备环境并构建

| 依赖 | 要求 |
| --- | --- |
| 系统与基础工具 | Linux、Git、Node.js 22+、Bun 1.2+、`/usr/bin/python3` |
| 模型运行时 | 已安装并完成认证的 Codex CLI，且所选模型在当前 provider 中可用 |
| 证明工具链 | Elan、与题目 `lean-toolchain` 匹配的 Lean，以及对应版本的 Mathlib/Lake 依赖 |
| 验证环境 | Bubblewrap（`bwrap`）；只读依赖环境还需要 `squashfuse` 或 `snapfuse`、`fusermount3` 或 `fusermount`、`mksquashfs`，以及可用的 FUSE 挂载权限 |

```bash
git clone https://github.com/LikC1606/theorem-os.git
cd theorem-os
bun install --frozen-lockfile
bun run build
```

构建生成 `out/main/math-solver.js`、`search-lean.js` 和 `check-lean.js`，并输出 JSON。记录其中的 **`buildManifestRef`**，运行时需要传入这个文件的绝对路径。源码与 bundle 均校验哈希，修改运行时代码后需重新构建。

CLI 默认使用 `~/.config/deepscientist/math-sol-codex` 中的 Codex profile。请先为该 profile 配置认证，或通过 `CODEX_HOME` 指向你已有的 profile。

项目原名 DeepScientist Math。CLI 入口为 `theorem-os`，同时保留 `deepscientist-math` 别名与 `bun run math`；已有环境变量、默认配置路径和运行档案格式继续兼容。

### 2. 准备一道公开题目

以下示例使用 IMO2026 Q3，将题目仓库、求解工作区和结果放在项目目录之外：

```bash
export MATH_RUN_ROOT="$PWD/../theorem-os-runs/imo-q3"
mkdir -p "$MATH_RUN_ROOT"

git clone https://github.com/humanfia/imo2026.git "$MATH_RUN_ROOT/benchmark"
git -C "$MATH_RUN_ROOT/benchmark" checkout --detach 834c01f2ecac89b648759b1c95bc6180b0ede149

bun run math bootstrap-imo \
  --repo "$MATH_RUN_ROOT/benchmark" \
  --problem imo2026_q3 \
  --workspace "$MATH_RUN_ROOT/workspace"
```

适配器从固定提交读取公开题目，生成 `Submission.lean`、题目契约与 `active-problem.json`。`--workspace` 必须是新的空目录；支持 `imo2026_q1` 至 `imo2026_q6`。

为生成的 Lean 项目准备依赖。已有兼容缓存时可按[环境配置](#环境配置)指定，否则可在宿主上下载对应依赖与预编译缓存：

```bash
(
  cd "$MATH_RUN_ROOT/workspace/generated/imo2026_q3"
  lake exe cache get
)
```

创建给求解器的任务说明；具体 Lean 声明由题目契约提供：

```bash
cat > "$MATH_RUN_ROOT/task.md" <<'TASK'
Prove every target in the frozen IMO2026 Q3 statement.
Preserve the original declarations, definitions, and protected files.
Write complete Lean proofs in Submission.lean and repair them using compiler feedback.
TASK
```

### 3. 开始求解

将 `MATH_BUILD_MANIFEST` 替换为第 1 步输出的 `buildManifestRef`：

```bash
export MATH_BUILD_MANIFEST="/absolute/path/to/manifest.json"

bun run math run \
  --build-manifest "$MATH_BUILD_MANIFEST" \
  --workspace "$MATH_RUN_ROOT/workspace" \
  --task-file "$MATH_RUN_ROOT/task.md" \
  --workers 4 \
  --output "$MATH_RUN_ROOT/result.json"
```

默认启用四个 Agent，解题预算为 30 分钟、合计 200 次模型调度。运行向标准输出发送 JSON 进度事件，并将结果写入 `result.json`。

首次配置环境时，可在上述命令末尾加 `--startup-only`，只检查准备条件，不调用模型。预检会创建运行状态；之后使用相同参数加 `--resume` 开始求解。

### 4. 恢复运行

```bash
bun run math run \
  --build-manifest "$MATH_BUILD_MANIFEST" \
  --workspace "$MATH_RUN_ROOT/workspace" \
  --task-file "$MATH_RUN_ROOT/task.md" \
  --workers 4 \
  --output "$MATH_RUN_ROOT/result.json" \
  --resume
```

恢复时使用原有题目、构建、环境、模型和 Agent 数量。宿主校验运行身份，并重新验证已有证明；会话、失败记录和累计用量保留在运行档案中。

### 5. 查看研究状态与修改计划

```bash
bun run math inspect --run "$MATH_RUN_ROOT/result.json"
bun run math inspect --run "$MATH_RUN_ROOT/result.json" \
  --format plan --output "$MATH_RUN_ROOT/plan.json"
```

报告按路线和任务展示目标、负责人、已存档的证明检查、条件性依赖、声明回译、审阅与卡点。`inspect` 不调用模型或重跑 Lean；JSON 格式可用 `--format json` 导出。运行中尚未生成结果文件时，也可读取同一路径对应的 checkpoint。

报告还会分别记录数学义务闭合、原题前沿变化、替代路线与局部障碍重开。局部阻塞、必需上下文与省略清单、`proofRoutes` 的 AND／OR 规则见[协作路线、上下文与数学进展](cooperative-proof-routes.md)。

Lead 创建计划后，可以导出并修改引理类型、任务依赖、路线或暂停状态，然后提交修改：

```bash
bun run math edit --run "$MATH_RUN_ROOT/result.json" \
  --plan "$MATH_RUN_ROOT/plan.json" --dry-run
bun run math edit --run "$MATH_RUN_ROOT/result.json" \
  --plan "$MATH_RUN_ROOT/plan.json"
```

保留导出计划的 `baseVersion` 和全部原题目标。`edit` 校验计划并追加到修改队列；运行中或恢复后的求解器继续检查版本、应用修改和重检受影响证明。`queued`、`applied` 与证明重检结果分别展示；过期计划需要重新导出。导出文件默认拒绝覆盖已有文件。

### 6. 同时求解多道题

分别准备每题的工作区和任务文件，将原有单题命令的完整参数数组保存到各自的 `launch.json`：

```json
{
  "args": ["bun", "/absolute/path/to/theorem-os/out/main/math-solver.js", "--workspace", "/runs/q1/workspace", "--task-file", "/runs/q1/task.md", "--output", "/runs/q1/result.json", "--build-manifest", "/absolute/path/to/manifest.json", "--workers", "4"]
}
```

```bash
bun run math batch \
  --launch /runs/q1/launch.json \
  --launch /runs/q2/launch.json \
  --launch /runs/q3/launch.json \
  --concurrency 2 \
  --output /runs/batch.json
```

默认同时运行两题，剩余题目依次补位；每题保留自己的 Agent、预算、检查和最终评测，一题失败不影响其他题。`batch.json` 记录进程状态，每题完整日志写入 `batch.json.logs/`；`completed` 只表示进程正常结束，证明是否通过仍以该题的结果和验收回执为准。

启动文件可选 `cwd` 和 `envFile`，路径相对启动文件所在目录解析；默认工作目录为启动文件所在目录，环境继承调用者。需要恢复时在对应题目的参数中添加 `--resume`，并为新批次指定新的 `--output`。Ctrl+C 会通知运行中的求解器保存退出，并停止启动排队题目；30 秒后仍未退出的进程会被强制停止。并发题数与每题 `--workers` 一起决定资源占用。

## 协作方式

```mermaid
flowchart LR
    P[公开题目与固定环境] --> L[Lead：任务与依赖]
    L --> R[Researcher：引理与路线]
    L --> E[Engineer：Lean 证明]
    R --> C[宿主检查与集成]
    E --> C
    C -. 诊断反馈 .-> R
    C -. 诊断反馈 .-> E
    C --> V[完整候选的独立审阅]
    V --> A[原题重检与独立评测]
```

Lead 计入 `--workers` 的总人数。默认配置中，Engineer 持续负责原题，Researcher 处理辅助引理、替代路线和关键猜想；完整候选交给符合条件的同伴切换为只读 Reviewer。

| `--workers` | 角色配置 |
| --- | --- |
| `1` | 单 Agent 求解 |
| `2` | Lead + Engineer；Engineer 可兼任研究与审阅 |
| `3` | Lead + Researcher + Engineer |
| `4`（默认） | Lead + 两名 Researcher + Engineer |

任务按依赖就绪异步执行，最多三个 worker 并发。多条路线共享 Agent 名额与原题预算，可以分别设置任务、负责人、暂停状态和路线预算。

### 直接证明与辅助引理

`--method direct` 为默认方法。`--method lemma` 启用辅助引理流程：尝试原题 → 提出引理 → 检查引理对原题的条件性连接 → 证明引理 → 完成原题。两种方法都支持协作运行。

条件性检查在临时源码投影中将待证引理转换为显式参数，保留未完成义务；依赖闭合后再组合并检查普通证明。局部引理、研究笔记和审阅意见分别记录，最终验收检查全部原题目标。

## 验证与结果

**模型的完成消息是交付信号；证明通过由宿主验证与独立评测决定。**

宿主保护原题声明、已有定义和受保护文件，将检查回执绑定到固定提交、源码摘要和目标声明。全部目标通过 Lean 内核检查后，集成候选，并再次检查原题。

| 题目 / 评测方式 | 最终验收 |
| --- | --- |
| IMO2026 | 集成后对全部目标重新执行宿主 Lean 内核检查，记录 `official: false` |
| Lean-Eval | 执行独立官方比较器，记录比较结果与对应题目身份 |
| `--evaluator-command` | 使用指定命令作为最终评测，记录 `official: false`；它会覆盖默认评测器 |

完整候选的模型审阅与 Lean 证据分别保存。局部编译、条件性证明和模型审阅提供各自范围的反馈。

| 输出 | 内容 |
| --- | --- |
| `<output>` | 最终结果、评测状态、证明提交、轮次与用量 |
| `<output>.runtime/state.json` | 可恢复状态，包括任务图、负责人、固定版本、检查反馈和审阅 |
| `<output>.runtime/worktree*` | 各 Agent 的独立求解工作区 |
| 标准输出 | JSON 进度事件 |

最终 `status` 包括 `evaluated_passed`、`evaluated_failed`、`incomplete`、`limit_reached` 和 `runtime_error`；仅做启动预检时为 `prepared`。报告实验结果时，应注明题目版本、预算、评测方式，以及是否从已有成果续跑。

## 配置与命令

### 常用参数

| 参数 | 默认值 | 作用 |
| --- | --- | --- |
| `--model` | `gpt-6.1-sol` | 所选 provider 提供的模型 ID |
| `--effort` | `xhigh` | 推理强度 |
| `--workers` | `4` | Agent 总数，支持 1–4 |
| `--method` | `direct` | `direct` 或 `lemma` |
| `--coordination` | `cooperative` | 协作，或 `independent` 独立并行尝试 |
| `--scheduler` | `plan` | 按计划顺序调度；`goals-first` 优先已就绪原题目标；`critical-path` 按依赖链排序；`continuation` 优先承接已证成果的主路径任务；`primary-led` 直接解题、按需请求协助 |
| `--prepare-timeout-seconds` | `1800` | 环境准备与依赖预编译预算 |
| `--max-run-seconds` | `1800` | 准备完成后的共享解题时间预算 |
| `--max-turns` | `200` | 所有 Agent 合计模型调度次数 |
| `--max-total-tokens` | `0` | 全部角色累计的 provider 报告 token 阈值；`0` 不限。达到后停止新模型请求，在途请求仍可完成并产生超额 |
| `--max-turn-seconds` | `180` | 单轮时间限制；停止写入后检查已保存源码 |
| `--evaluator-timeout-seconds` | `1800` | 集成后 Lean 复核与最终评测共享的独立时间预算 |

`--max-run-seconds`、`--max-turns`、`--max-turn-seconds` 与 `--evaluator-timeout-seconds` 可设为 `0` 关闭对应限制。关闭总解题时间限制时，证明检查的期限也会关闭。

`--max-total-tokens` 包含规划、研究、证明和审阅角色，按跨线程累计消费计算；恢复时继续使用历史用量，省略参数时保留已存额度。它依据 provider 的事后通知阻止新请求，不能保证并发在途消费不超过阈值。报告保留超额与用量完整性；有限额度下缺失已执行请求的用量会停止继续派发。旧运行未记录逐轮用量完整性，不能直接当作严格 token 对照。默认不限 token，不为已有长跑增加停止条件。

### 环境配置

数学工具配置默认读取 `~/.config/deepscientist-math/math.env`，也可通过 `DEEPSCIENTIST_MATH_ENV_FILE` 指定。该文件保存工具路径与环境设置；Codex 认证由已有 profile 管理。

| 环境变量 / 参数 | 用途 |
| --- | --- |
| `CODEX_HOME` | 指定已有 Codex profile；默认 `~/.config/deepscientist/math-sol-codex` |
| `--codex` | 指定 Codex 可执行文件 |
| `DEEPSCIENTIST_MATH_ENV_FILE` | 指定数学环境文件 |
| `ELAN_HOME` | Elan 安装位置 |
| `DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS` | 可复用的可信 Lean 依赖缓存根目录；多个路径用 `:` 分隔，内容须匹配冻结的 Lake manifest |
| `DEEPSCIENTIST_MATH_SANDBOX_BACKEND` | 选择验证后端，例如 `bwrap`；只读依赖环境使用其文件描述符挂载能力 |
| `DEEPSCIENTIST_LEAN_EVAL_ROOT` | 本地 Lean-Eval 仓库，供对应适配器使用 |

使用外部隔离启动器时，按每个子进程的 `DEEPSCIENTIST_MATH_WORKER_ID` 和 `DEEPSCIENTIST_MATH_WORKER_WORKTREE` 绑定工作区与独立会话存储。

### CLI 命令

```bash
bun run math --help
bun run math run --help
bun run math bootstrap-lean-eval --help
```

| 命令 | 用途 |
| --- | --- |
| `build` | 构建求解器与检查 / 检索工具，生成构建清单 |
| `doctor` | 检查工具、登录、沙箱和指定项目环境，支持 JSON 报告 |
| `example` | 准备、回放或求解不依赖 Mathlib 的小型 Lean 题目 |
| `component` | 生成 M3 排序组件模板，检查基本任务约束 |
| `bootstrap-imo` | 从固定公开提交准备 IMO2026 题目 |
| `bootstrap-lean-eval` | 准备 Lean-Eval 题目与评测绑定 |
| `run` | 启动、预检或恢复运行 |
| `inspect` | 查看存档研究报告，导出 JSON 或带版本的可编辑计划 |
| `edit` | 校验并提交人工计划修改，支持 `--dry-run` |
| `compare` | 准备、运行并汇总固定预算的单 Agent / 独立并行 / 协作对照 |
| `check-lean` | 对保存的 Lean 文件获取局部诊断 |
| `search-lean` | 检索已验证的本地 Lean 包声明 |
| `knowledge` | [导入、搜索和读取历史已检查定理](theorem-knowledge.md)，以固定版本供后续运行复用 |
| `freeze-retrieval` | 冻结允许检索的本地源码语料 |
| `summarize` | 汇总保存的实验记录 |

例如，检查指定 Lean 文件并设置 90 秒超时：

```bash
bun run math check-lean \
  --workspace "$MATH_RUN_ROOT/workspace/generated/imo2026_q3" \
  --file Submission.lean \
  --timeout-seconds 90
```

`check-lean` 默认超时为 `0`（等待完成），保留失败退出码和最早错误；其诊断仅用于局部修复。

返回的 `firstBlocking` 与 `messages` 来自 Lean JSON 消息，并保留文本兼容路径。摘要不完整时按 `diagnosticArtifacts` 回读绑定源码和环境的捕获材料；`captureComplete: false` 表示超过每流 4 MiB 窗口，`null` 表示完整性未知。

新增闭合类型预检，可在不修改活动源码的固定副本中核对任务接口：

```bash
bun run math check-lean \
  --workspace "$MATH_RUN_ROOT/workspace/generated/imo2026_q3" \
  --file Submission.lean --context Submission.original \
  --type 'forall (n : Nat), n = n'
```

`--context` 指定文件中已有声明，恢复其命名空间和 open 作用域；类型模式要求恰好一个文件。`elaborated` 仅表示闭合类型可展开，不代表有证明、等于原题或已获验收，尚不存在的 helper 也不会自动注入。材料保存在项目 `.lake/type-diagnostics/`，默认不限时。

对照报告可用 `compare --phase check-report --directory DIR` 只读核对快照；续跑后旧报告标为过期，重新生成会保留 `report.json.history/`。预算等身份改变的续跑即使通过，也不会计入原固定预算对照。

## 架构与开发

研究组件的职责见[组件模型](../README.md#组件模型)，输入、产物及验收边界见[解题模块与交接协议](solver-modules.md)，扩展示例见[替换一个组件](../examples/components/README.md)。入口在 [run.ts](../src/solver/run.ts)，Agent 执行循环在 [research.ts](../src/solver/research.ts)，异步协作与集成在 [cooperation.ts](../src/solver/cooperation.ts)。

| 模块 | 职责 | 实现 |
| --- | --- | --- |
| M1 执行 | 在指定隔离工作区执行模型轮次，记录候选与来源 | [execution.ts](../src/solver/modules/execution.ts) |
| M2 证据 | 固定版本、精确声明的 Lean 证据与局部义务检查 | [evidence.ts](../src/solver/modules/evidence.ts)、[cooperativeProof.ts](../src/solver/cooperativeProof.ts) |
| M3 搜索调度 | 检查依赖与分配可行性、路线预算、继续 / 停止及重试 | [search.ts](../src/solver/modules/search.ts)、[value.ts](../src/solver/modules/value.ts) |
| M4 上下文 | 完整必需接口、工作契约、未决提案、反馈与省略清单 | [context.ts](../src/solver/modules/context.ts)、[contextCompiler.ts](../src/solver/contextCompiler.ts) |
| M5 职责分配 | 在存活工作槽中匹配职责、显式负责人和路线约束 | [organization.ts](../src/solver/modules/organization.ts) |
| S1 任务与成果档案 | 保存与恢复候选、回执、失败和运行状态 | [archive.ts](../src/solver/archive.ts) |
| S3 环境与评测合同 | 冻结题目，集成后重检并独立评测 | [problem.ts](../src/solver/problem.ts)、[evaluation.ts](../src/solver/evaluation.ts)、[src/math/](../src/math/) |

[index.ts](../src/solver/modules/index.ts) 绑定默认模块与版本；`runSolver(args, root, modules)` 支持替换模块，模块版本参与恢复身份。宿主固定执行源码边界检查、总预算限制和最终验收。当前 M3 采用规则与依赖调度，S2 跨任务学习尚未实现。

命令行可用 `--scheduler goals-first` 单独替换 M3 的就绪任务排序；`--scheduler critical-path` 同时替换 M3 排序和 M5 分配，按通往未完成原题目标的最长依赖链排序，同长度时优先覆盖更多目标的任务，由 Researcher 和 Engineer 共同领取。显式负责人、路线限制和恢复归属仍然生效；链长只作启发式排序，不预测证明耗时。模块版本写入状态，恢复时校验。这些策略尚无性能提升结论。[三组对照实验](../examples/imo2026/COMPARISON.md) 提供固定题目、模型和总预算的准备、运行与汇总步骤，保留失败、缺失记录和用量缺口。

`--scheduler continuation` 优先推进通往未完成原题、能够使用当前已证引理的就绪任务，再推进主路径的核心缺口；两项主路径工作并行时，为其他就绪路线保留一个探索机会。负责人、依赖、路线和固定版本检查继续生效。Lead、证明角色与 `inspect` 报告会看到原题的未闭合依赖前沿，并分别列出计划消费者、Lean 回执中的证明引用、声明引用和条件性引用。未记录消费者不代表引理无用；这些摘要不提供完成百分比或新的证明验收。重复两次交付未更新的继承研究笔记会交给 Lead 决策，正常长研究与 checkpoint 不按此计数。

`--scheduler primary-led --coordination cooperative` 让主智能体从第一轮直接证明整题，其他智能体等待具体协助请求。主智能体可在 `RESEARCH.md` 的 JSON `requests` 数组中请求独立引理或只读研究；辅助成果在隔离工作区验收，主智能体选择采用并保留自己的证明进展。无需预先拆分所有原题目标，完整证明仍须通过宿主 Lean 检查和固定版本独立终审。单智能体或 `independent` 模式继续直接解题。该策略尚无真实模型性能结论。

辅助引理方法在 [lemma.ts](../src/solver/lemma.ts)；Codex stdio 协议适配在 [codexSession.ts](../src/runtime/codexSession.ts)。

<details>
<summary>Agent 交付协议与提前共享</summary>

agent 的常用协议只有两步：读取任务，写出成果。需要结构化回复时，在 `RESEARCH.md` 中保留一个 `math` JSON 代码块；普通说明可写在代码块外。

| 当前职责 | 需要交付什么 |
|---|---|
| Lead | `{"tasks":[...]}`。任务只需 `id`、`kind`、`objective`；形式任务加 `theoremName`，引理加闭合 `type`，有依赖时加 `dependsOn`。 |
| Researcher | `{"summary":"发现、依据与缺口"}`；需要 Lead 决策时加 `needsDecision: true`。 |
| Lean Engineer / 引理证明者 | 保存指定 Lean 证明，写简短笔记后返回，无须填写证明交付 JSON。 |
| Reviewer | `{"verdict":"accepted","summary":"审阅意见与依据"}`，有问题则用 `changes_requested`。 |
| 声明回译 | `{"mathematics":"数学表达、假设及相关定义"}`。 |

`dependsOn` 默认空，`revision` 默认 0；原题目标的 `proofPath` 自动确定，辅助引理在只有一个可写 Lean 文件时也可省略。Lead 的计划仍须恰好覆盖原题目标，并保持依赖无环。任务、版本、环境、检查回执和预算由宿主绑定，无须 agent 重复填写。提示词只说明当前职责；可选字段仍可显式设置。

研究者可用 `lemmaRequests` 提出同路线的新引理，字段与正式 `lemma` 任务一致。宿主校验题目、可写文件、名称和依赖后把提案交给 Lead；采纳后另建证明任务，提案本身不授予通过状态。临时 Lean 探针恢复前，应把完整代码、命名空间、精确声明和预期使用者保存在 `RESEARCH.md` 的 `lean` 代码块中。显式报告本地成功检查可填写 `leanChecks: [{"status":"passed","path":"RESEARCH.md","declarations":["Qualified.name"]}]`；宿主将其绑定到可恢复代码的提交和哈希，仍按待独立检查的候选处理。未完成的形式任务也保留新增辅助声明的材料索引。完整研究笔记和任务图支持最多 1,000,000 字节，提示词的显示截断不会截断存档。

研究任务的 `reviewScope: "final-candidate"` 以及兼容的 `independent_candidate_review` 仅在全部原始目标经过本进程重新检查后派发；`reviewScope: "feasibility"` 用于独立检查尚未完成的数学路线。最终验收仍由完整原题检查和固定候选审阅决定。可恢复的工具调用解析、连接和会话中断最多重试三次，退避 10、20、40 秒；已有源码、笔记和累计用量保留。认证、未知错误及源码归属或冻结声明违规继续明确失败，不自动重试。该局部恢复策略不增加整体求解时限。

声明投影失败会在 `<output>.runtime/statement-diagnostics/` 保存实际投影源码、各最多 1MB 的标准输出和错误输出及题目/提交绑定的清单，异常摘要优先显示首条 Lean 错误。这些含证明擦除占位符的投影仅用于诊断。

需要提前共享时，向提示词指定的分工日志追加一行 `{"summary":"进展或卡点"}`；提前交付证明则先提交源码，再追加 `{"kind":"proof","commit":"完整 Git 提交","summary":"成果"}`。宿主自动补充消息编号、任务和版本，去重并随完成随检查、接入和通知；无须等待 Lead 或整批任务结束。`COOPERATION.json` 提供只读同伴状态。旧的 `math-plan`、`math-result`、`math-review` 等代码块及带版本字段的 `DELIVERIES.jsonl` 仍可读取，以便已有运行继续恢复。

任务图为空的初始 Lead 还可向提示词指定的独立日志追加一行 `{"kind":"plan","baseVersion":"当前基版本","summary":"路线说明","tasks":[...]}`，提前发布一次完整有效计划并继续研究。其他角色从 canonical 源码开始；普通笔记草稿不会自动发布。必需上下文中的研究反驳须用 `challengeDecisions` 明确修订、附证据反对或说明等待输入，不能由省略字段静默忽略。

单 Agent 的辅助引理提案使用 `RESEARCH.md` 中的 `math-lemma` JSON 代码块，包含 `proofPath`、原题完整名称 `target`、引理完整名称 `lemma` 和闭合 Lean 类型 `type`。引理置于目标之前，使用普通 `:=` 证明；目标通过引理的局部名称引用它。连接与引理分别在临时投影中检查。

辅助义务仅在完整投影、提案和环境一致时复用本进程的成功回执；输入变化或进程恢复后重新检查。同一失败义务连续两次没有证明输入变化时，控制器重新分解路线并保留失败原因。

</details>

<details>
<summary>路线管理、人工修改与声明审阅</summary>

形式任务可设 `conditional: true`，基于固定类型的待证引理先构造父证明；检查只在临时投影中添加显式引理参数。条件性成果保留未证义务，依赖闭合后自动组合并重检普通证明。猜想、研究、草图和审阅意见不能授予原题通过状态。

协作运行中可向 `<output>.runtime/edits.jsonl` 追加一行 `{"id":"edit-1","baseVersion":"state.json 中的 cooperation.planVersion","tasks":[完整的新任务表],"groups":[完整的新路线配置]}`。服务校验基准版本、原题覆盖、职责和无环依赖后应用修改，公布受影响的任务并停止相关旧分工；无关工作继续。可以修改引理、路线、负责人、任务暂停状态和路线预算。旧交付保留为历史，不能进入新版证明；审阅对象被修改后须重新审阅。冲突或无效修改写入 `cooperation.edits` 并发出拒绝事件。交付和修改日志只追加，每行以换行结尾；部分写入等待完成，游标随运行恢复。

`cooperation.edits` 分别记录 `received`、`applied`、`rejected`，附收到/应用时间、计划版本和受影响任务；`COOPERATION.json` 展示最近 16 条修改，完整历史保存在 `state.json`。`applied` 表示新计划已建立，证明检查另见 `recheck`：逐任务区分待检查、条件性通过、普通证明通过、失败、移除或被后续修改取代，并链接最近检查的源码提交、环境与 Lean 回执编号。仅调整暂停、负责人或预算时显示 `not-required`。恢复运行先重新验证已有证明；旧检查记录保留为历史，不能据此显示当前检查已通过。收到但未应用的修改可从追加日志继续处理，同一编号只应用一次。声明审阅和原题独立验收仍分别记录。

形式任务可设置 `statementReview: true`，并用 `informalStatement` 写明所需结论、假设和量词。声明固定后即可送审，证明任务可并行继续：先在独立目录和新会话中只依据 Lean 声明及定义回译，再由另一个新会话比较保存的回译与数学原意。回译输入去除原始说明、注释、证明、研究日志和 Git 历史；不发送同伴通知。每阶段均计入原题及路线回合预算。`COOPERATION.json` 并列展示原意和回译，`statementReviews` 保存版本、定义快照、环境标识和审阅结果；定义或任务版本变化会使旧结果作废，纯证明体修改保留声明审阅。恢复时可复用完成的回译，未完成阶段重新开会话。被请求的声明审阅须通过才能最终验收，但不能替代 Lean 证据或完整证明审阅。这是上下文与工作目录隔离，沿用现有 Codex 沙箱权限。

已检查的普通形式任务会保存 Lean 从 elaborated 声明和证明项抽取的项目内实际引用，包括传递使用和隐式实例；`actualReferences` 与计划中的 `dependsOn` 分别展示，绑定源码提交、声明/定义摘要和环境标识。Lead 修改辅助定义时，仅重检引用或上下文变化的已检任务；没有完整引用报告、生成常量无法定位、上下文或环境变化时采用保守检查。声明审阅获得可靠声明引用后，无关定义变化可保留已有审阅。同一运行内修改任务计划时，已集成证明按可靠的实际引用传播失效；未完成任务、条件性证明和引用不完整的任务仍按计划及分工中的依赖保守处理。保留的证明可继续供后续任务使用，证明交付固定记录实际依赖版本及原始提交，受影响的旧交付标为历史。运行恢复会重新验证证明回执，存档中的引用不能授权跳过检查；恢复前修改计划仍先保守处理计划依赖。条件性父证明须在依赖闭合后取得普通证明的实际引用。最终原题检查仍独立执行。

停止后仍可编辑 Lead 的 `RESEARCH.md` 并 `--resume`，沿用相同的依赖更新和重检规则。

计划可增加 `groups`，每组记录 `id`、数学目标 `objective`、`status`（`active` / `paused` / `stopped`）、路线 `revision`，以及可选 `engineerId`、`maxTurns`、`maxConcurrent`。任务用 `groupId` 绑定路线；不配置时使用默认 `main` 组。多个组时成果默认 `sharing: "group"`，跨路线引用需将生产任务标记为 `sharing: "problem"` 并在消费者中写入 `dependsOn`。宿主提供同组任务与已检查共享成果的摘要，附生产者、前提类型、依赖和版本；其他路线的私有辅助源码不进入任务的初始源码。各组共享现有 worker 名额，一条路线的原题节点持续交给指定 Engineer。

`maxTurns` 统计该组 worker 的任务尝试，恢复后累加；`0` 表示不给该组新任务。不设置则只受原题总预算限制。`maxConcurrent` 为 1–3，限制该组同时执行的任务，包括提前交付后仍在运行的生产者。Lead、最终审阅和通知引入的模型用量仍计入原题总预算。暂停、停止或预算耗尽保留已有成果，并允许无关路线继续；运行中追加修改，或停止后改计划并 `--resume`，可恢复路线或追加预算。修改路线目标或 `revision` 会更新该组任务及跨组依赖者；调整状态或预算保留数学成果。

</details>

### 参与开发

欢迎提交问题复现、Lean 适配器改进、搜索与协作策略，以及检查与恢复边界的测试。报告问题时，请附上命令、依赖版本、结果状态和相关诊断，并移除认证信息。

首个预览版的范围与限制见 [v0.1.0 发布说明](releases/v0.1.0.md)。

```bash
bun run test
bun run typecheck
bun run build
```

测试使用本地 fixture 与模拟会话，不调用真实模型。修改运行时边界时，运行对应测试并重新构建；研究模块的输出须继续经过宿主最终验收。

