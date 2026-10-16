# 网页研究工作台

`apps/web` 提供独立网页和 HTTP API，通过 Docker 启动一次性的求解 worker，复用现有 `runSolver()`、原题固定机制和最终 Lean 验收。CLI 不依赖此服务。

## 本地启动

需要 Linux、Docker Engine / Compose，以及允许非特权用户创建用户命名空间的宿主机。Mathlib 运行还需要可用的 `/dev/fuse`。每个容器上限为 2 CPU，Mathlib 内存上限 8 GiB、标准库 4 GiB，默认一次运行一个任务。建议为每个并发 Mathlib 运行预留 30 GiB 可用磁盘；冷准备会按依赖体积约三倍检查磁盘余量。

首次构建需联网下载 Bun、Codex CLI、固定 Lean 工具链、Mathlib 源码和预编译依赖，镜像较大，下载可能较慢。构建会复用下载缓存、重试失败下载，并执行完整 Mathlib 构建和 `import Mathlib` / `ring` 探针。

```bash
git clone https://github.com/LikC1606/theorem-os.git
cd theorem-os
docker compose -f apps/web/compose.yml build worker web
docker compose -f apps/web/compose.yml up -d web
docker compose -f apps/web/compose.yml ps
```

浏览器打开 <http://127.0.0.1:8787>，先选择证明环境，再选择模板或粘贴 Lean 源码，输入模型名称及自己的 API Key，开始研究。新建研究默认使用 Mathlib；可切换到 Lean 标准库。页面显示当前环境的固定 Lean 工具链和 Mathlib revision，模板列表只包含所选环境的示例。切换环境时，已选择的模板会更换为对应示例；自定义源码与任务保留，请自行确认其 import 和 tactic 属于所选环境。

默认模型沿用运行时的 `gpt-6.1-sol`，请使用所选服务商实际提供的模型。默认推理强度为 `xhigh`，服务商及模型也需支持对应参数。

```bash
# 停止服务；未完成任务会被取消并清理容器
docker compose -f apps/web/compose.yml down
```

默认仅监听本机 8787 端口。请使用 `127.0.0.1` 访问；服务会校验 Host 与公开地址一致。GitHub Pages 只托管静态官网，无法运行此后端。

## 配置兼容 Responses API 的服务

服务商由部署者配置，网页访客从列表选择。每个地址必须是可信的 HTTPS API 根地址，通常以 `/v1` 结尾，不能包含凭据、查询串或片段。工作台使用 Codex 的自定义模型服务配置 `wire_api = "responses"`、`env_key` 与 Bearer API Key；仅兼容 Chat Completions 的服务暂不支持。

启动前在 shell 设置以下环境变量，再运行 Compose：

```bash
export THEOREMOS_WEB_PROVIDERS='[{"id":"openai","name":"OpenAI","baseUrl":"https://api.openai.com/v1"},{"id":"compatible","name":"兼容服务","baseUrl":"https://api.example.com/v1"}]'
docker compose -f apps/web/compose.yml up -d web
```

上例的第二个地址需要替换。这里仅配置服务地址；用户的 API Key 在网页中逐次输入。

| 环境变量 | 默认值 | 用途 |
| --- | --- | --- |
| `THEOREMOS_WEB_PUBLIC_URL` | `http://127.0.0.1:8787` | 浏览器实际访问的 origin，不带子路径 |
| `THEOREMOS_WEB_PROVIDERS` | OpenAI `/v1` | 可选服务商 JSON 数组 |
| `THEOREMOS_WEB_CONCURRENCY` | `1` | 同时运行任务数，1–8 |
| `THEOREMOS_WEB_QUEUE_LIMIT` | `8` | 排队与运行中的任务总数，1–32；直接启动时可配置 |
| `THEOREMOS_WEB_WORKER_IMAGE` | `theorem-os-worker:local` | 运行镜像；Compose 使用固定本地标签 |
| `THEOREMOS_WEB_HOST` | `127.0.0.1` | 直接启动时的监听地址；容器内为 `0.0.0.0` |
| `THEOREMOS_WEB_PORT` | `8787` | 直接启动时的端口 |
| `THEOREMOS_WEB_STATIC_ROOT` | `out/web` | 直接启动时的静态文件目录 |

如本机依赖已齐备，也可只用 Docker 跑 worker、用 Bun 启动网页服务：

```bash
bun install --frozen-lockfile
bun run build:web
docker compose -f apps/web/compose.yml build worker
bun run web
```

## 功能范围与数据

- 提供 Mathlib 和 Lean 标准库两种固定环境。新网页任务默认 Mathlib，可使用 `import Mathlib` 和对应版本提供的 tactic；标准库环境不提供 Mathlib。单份源码最多 32 KiB，至少包含一个命名 theorem / lemma；保留原题声明，模型修改证明。暂不支持上传仓库或自定义 Lake 依赖。
- 环境选择随任务保存，运行列表和详情显示实际提交环境；详情显示对应工具链和 Mathlib revision。CLI 的既有行为不受网页默认值影响。
- 概览分别显示排队、环境准备、证明研究、独立验收四个阶段及用时。总用时包含等待与准备，研究用时从真正开始研究时计算，进入独立验收后停止。阶段开始时间独立保存在后端，不受最近 200 条活动日志上限影响；刷新页面后可继续查看。取消或提前结束的任务会标明尚未执行的阶段。
- 新建研究优先展示原题和源码，模型连接与执行配置随后排列。尚无运行时，详情区同步展示当前草稿的环境、模型、预算、Agent 数量与前 160 行源码，明确标记未提交；预览不包含 API Key，也不会创建任务。环境摘要显示短 revision，悬停可查看完整版本。
- 详情右上角可复用任务配置，重新载入该次任务固定的原始源码、研究任务、证明环境、模型和执行预算，API Key 需重新输入。Lean 源码视图可切换原始题目与候选 / 已验收证明，支持复制和下载。桌面端表单、历史与详情独立滚动，提交区保持可见。
- 有候选源码的运行支持逐行差异对比，展示原题 / 候选行号与新增、删除统计，默认折叠未改动内容并保留三行上下文，可展开和跳转更改位置。换行格式、末尾缺失换行分别标明；复制与下载仍保留完整候选原文。对比不改变验收结论。浏览器内使用 `diff` 库，在 80 ms / 2,000 编辑步骤预算内生成对比，最多展示 2,000 行；超限会提示，完整源码仍可查看和下载。
- 可从本机导入 UTF-8 `.lean` 文件，导入时只在浏览器读取，点击提交后才发送源码；错误文件和迟到的文件读取不会覆盖新草稿。支持展开源码编辑器、行数与字节计数，应用修改前检查大小和空白输入；取消或 Esc 保留原表单。
- 源码、研究任务和模型 / 执行配置自动保存在当前标签页的 `sessionStorage`，刷新后恢复，API Key 不写入草稿。重置配置会清除已保存的草稿；不支持存储或内容超限时显示未保存状态，不影响编辑和提交。可导出任务草稿 JSON，也可导入草稿或已下载的运行档案，文件上限 16 MiB；先预览，确认后载入原始题目并清空 API Key，不创建任务或恢复旧验收结论。源码和研究任务仍受各自大小限制。文件读取期间的新编辑不会被迟到内容覆盖。
- 历史记录可组合关键词和状态筛选，关键词匹配题目、研究任务、模型、运行 ID、源码和证明环境；只有完成独立验收的记录会进入“验收通过”。筛选不会清掉当前查看的详情，新任务提交成功后会清除筛选并选中新运行。
- 报告页默认展示验收摘要，分别列出候选检查与独立验收、定理级诊断、已有的研究轮次 / 耗时 / Token 统计和验收凭据。原始 JSON 仍可切换查看、复制和下载。缺失的统计不会被补成零，候选检查、单个定理或验收阶段的通过记录不会替代最终结论；最终成功同时要求任务结束和 `evaluated_passed`。
- 已完成、已取消或发生错误的历史记录可在确认后单条删除，删除前可下载包含原始题目与诊断的运行档案，即使任务尚未生成结果。排队或运行中的任务不能删除；删除不会自动取消任务。删除后释放会话的历史容量，不影响其他任务。删除请求的响应丢失时只刷新历史核对，不自动重发。
- 网络中断或请求超过 15 秒时显示连接状态并禁用提交，已有表单仍可编辑；网络恢复、返回页面或手动重连时自动刷新会话和历史。创建任务与取消请求均不自动重发；提交响应丢失时提示结果未确认，并通过历史列表核对，避免重复创建任务。恢复连接不重置未提交的源码、任务或模型配置。
- 可配置 1–4 个 Agent、任务协作 / 独立并行、1–20 轮和 30–900 秒解题预算。Mathlib 冷准备最长 600 秒，标准库准备和最终验收各有独立时限，均不计入解题预算；轮次和时间不等于 API 费用上限，服务商按自己的计费规则收费。
- 模型结束和网页显示“运行结束”都不代表证明成立。只有 `evaluated_passed` 才显示“验收通过”；这是本地独立 Lean 验收，不是 Lean-Eval 官方成绩。
- 浏览器不把 Key 写入 localStorage / sessionStorage；提交成功后清空输入框。Key 经同源后端内存、Docker stdin 与 Codex 子进程环境传递，不写入 Docker 参数、容器环境配置、Codex 配置文件、任务档案或服务日志。每个任务使用新的 Codex profile，不读取部署者的认证文件；工具 shell 环境排除该 Key。
- 运行记录、源码、进度与结果仅保存在服务内存。每个会话最多保留 20 条记录，可删除已结束的记录以释放容量。有效 API 请求会延长同一会话 Cookie，连续空闲一小时到期；服务重启后清空。需要保留的证明和 JSON 请及时下载。第一版没有账号、跨设备历史或运行恢复。

当前固定环境如下。Mathlib 的工具链、commit 和传递依赖 manifest 记录在 [`resources/mathlib/environment.json`](../resources/mathlib/environment.json)；页面版本信息由后端读取这份配置。

| 环境 | Lean 工具链 | Mathlib commit |
| --- | --- | --- |
| Lean 标准库 | `leanprover/lean4:v4.33.0` | 无 |
| Mathlib | `leanprover/lean4:v4.33.0` | `db584cd6d46c92f209a44c0f1c829460d327499d` |

Mathlib 模板包含以下形式的原题，任务要求模型构造证明，`ring` 可用于完成这个目标：

```lean
import Mathlib

theorem square_expansion (x y : ℝ) :
    (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  sorry
```

Lean 标准库模板保留自然数加法和命题逻辑示例。网页默认 Mathlib 与历史未指定环境的 API 请求有所区别：API 提交 `environment: "mathlib"` 或 `environment: "standard"` 明确选择环境；旧请求省略该字段时仍按标准库处理。

## 无模型费用的验证

基础 worker 构建完成后，可执行：

```bash
bun install --frozen-lockfile
bun run test -- tests/webServer.test.ts tests/webJobs.test.ts tests/webPresentation.test.ts tests/webReport.test.ts tests/webClient.test.ts tests/webDraft.test.ts tests/webSourceDiff.test.ts tests/webProviderFixture.test.ts tests/webProviderContainer.test.ts tests/webRunner.test.ts tests/leanTask.test.ts
bun run typecheck
bun run typecheck:web
bun run build:web
bun run test:web-ui
bun run test:web-recovery
bun run test:web-results
bun run test:web-drafts
bun run test:web-source-diff
bun scripts/test-web-runtime.ts
```

`test:web-ui` 使用 Playwright Chromium 与真实本地 HTTP 服务，通过可控 worker fixture 检查进度计时、日志轮转、刷新、取消、配置复用、源码切换、复制下载、本地文件导入、展开编辑、历史筛选，以及 320–1440 像素布局。`test:web-recovery` 检查离线、401 / CSRF 403、请求超时、POST 响应丢失、过时响应和页面恢复。`test:web-results` 检查可读报告、候选与最终验收的区别、诊断转义、JSON 导出，以及删除确认、失败和响应丢失。`test:web-drafts` 检查刷新恢复、草稿与档案导入导出、密钥排除、存储异常和导入预览布局。`test:web-source-diff` 检查逐行差异、上下文与更改导航、换行、原文复制下载和大输入边界。这些浏览器验证均不调用 Docker、Lean 或模型，报告和截图写入 `out/web-ui-smoke/`。首次使用需安装 Playwright Chromium：`bunx playwright install chromium`。

最后一项派生带明确 fixture 标记的测试镜像，用模拟 Codex app-server 生成候选，执行真实 Lean 检查。共 7 个场景：标准库正确 / 错误候选、运行中取消、创建时取消，以及 Mathlib 正确 / 错误候选和运行中取消；Mathlib 取消场景还核对设备权限、匿名卷和删除结果。不会调用模型或使用真实 Key。可用 `--case mathlib-valid` 单独排查；Mathlib 冷准备可能持续数分钟。报告写入 `out/web-runtime-smoke/report.json`，测试镜像默认自动删除。

已验证标准库和 Mathlib 的正确 / 错误证明、取消及容器清理；浏览器到 HTTP、Docker 和真实 Mathlib/Lean 的完整流程也通过验收，并检查了下载和 320–1440 像素布局。实际运行结果写入各次测试报告。不同服务商的 Responses API 兼容性与付费模型行为需要使用者通过自己的账户验证。

本机离线 Mathlib 正例总耗时约 159 秒，包含约 114 秒冷准备。资源采样中可见临时文件最大约 8.87 GiB，但不含 FUSE 持有的已删除镜像文件，不能视为完整磁盘峰值；部署仍应按上述预检余量准备磁盘。8 GiB 配置下未观察到 OOM。这些是本机运行观察，不是通用性能承诺。

## 部署到服务器

在 Linux 服务器按上述命令构建、运行，再用 Nginx / Caddy 将 HTTPS 域名反向代理至 `127.0.0.1:8787`。设置 `THEOREMOS_WEB_PUBLIC_URL=https://research.example.com`，保留原始 Host 请求头。服务设置 Secure / HttpOnly / SameSite Cookie，并检查请求来源与 CSRF token。不要在反向代理中记录请求体；其中包含访客 Key。

Web 容器是 Docker supervisor，挂载 Docker socket，有权限创建和删除运行容器；请将它部署在用于此产品的受控宿主机上。Worker 不挂载该 socket 或宿主目录，以 UID 10001 和只读根文件系统运行。每次 Mathlib 运行只映射 `/dev/fuse:rw`，并创建一个挂载到 `/var/tmp` 的匿名 local 磁盘卷供准备验证环境；正常结束、取消和失败清理均使用 `docker rm --volumes`。标准库 worker 不映射设备，也不创建磁盘卷。

为嵌套的非特权 Bubblewrap 验证器，worker 放开容器 seccomp / AppArmor profile，并使用 `systempaths=unconfined` 允许在独立 PID 命名空间内挂载新的 procfs。Mathlib 入口的外层 Bubblewrap 在新 user namespace 内仅授予 `SYS_ADMIN` 和 `SETFCAP`，用于构造冻结的依赖环境；Docker 容器仍保留 `--cap-drop=ALL`、`no-new-privileges` 和资源限制，不共享宿主机 PID 命名空间。`/tmp` 的 tmpfs 显式启用 `exec`，供验证器运行临时 Lean 启动脚本，并保留 `nosuid,nodev`。宿主机需要支持这一隔离方式；不支持时应修正宿主机配置，不能跳过 Lean 验证隔离。

没有登录系统，已能访问网站的访客均可提交任务。会话、队列、并发和输入有上限；需要限制公开访问时，可在反向代理配置访问控制。API 限流使用 TCP 对端 IP，每分钟 600 次；经单台反向代理转发的访客共享该限额。

如果首页提示“运行镜像尚未就绪”，确认 worker 镜像已构建，Web 服务能访问 Docker daemon，且镜像标签一致。如果镜像就绪但 Lean 验收无法执行，先运行上述离线 Docker 验证，检查用户命名空间和 Bubblewrap 的宿主机支持。

## 实现位置

| 文件 | 职责 |
| --- | --- |
| `apps/web/server.ts` | 同源静态服务、会话、CSRF、运行 API |
| `apps/web/jobs.ts` | 内存队列、并发、归属检查、取消、脱敏 |
| `apps/web/runner.ts` | Docker 生命周期、预算、私有 stdin 协议 |
| `apps/web/worker.ts` | 单次 BYOK profile、真实求解与验收 |
| `apps/web/client/` | 浏览器工作台 |
| `apps/web/presentation.ts` | 运行阶段、用时与结果展示 |
| `apps/web/report.ts` | 已知报告字段的验收摘要、诊断与统计 |
| `apps/web/client/sourceDiff.ts` | 有预算限制的逐行差异和折叠上下文 |
| `src/math/leanTask.ts` | 将输入源码固定为独立 Lean 题目 |

工作台遵循仓库的 AGPL-3.0-only 许可证。
