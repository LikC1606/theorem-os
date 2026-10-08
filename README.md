# DeepScientist Math

从 DeepScientist 拆出的独立数学研究与 Lean 证明 CLI。运行和构建都不需要 Rust Core、Electron、React、WebUI 或原来的 DeepScientist 源码目录。

保留现有数学行为：Lead 协调、持久 Lean Engineer、辅助研究、隔离 worktree、Lean 检查、源码集成、签名回执、独立评测和任务恢复。默认模型为 `gpt-6.1-sol`，所有角色使用 `xhigh`。

## 安装和启动

需要 Bun、Node.js 22+、Git，以及独立准备好的 Lean/Mathlib 环境。目前证明运行器的隔离与进程身份检查要求 Linux。

```bash
bun install --frozen-lockfile
bun run build
```

需要已安装的 Codex CLI（支持 `app-server`）。`math run` 自动启动内置 Bun 服务，直接连接 Codex 会话；每个输出文件的运行状态保存在 `<output>.runtime/` 私有目录，退出时关闭服务，恢复时复用原端口和 Codex thread。已启动的回合不会在重启后自动重放。

`build` 构建 7 个数学 bundle，并输出 `buildManifestRef`。源码、依赖锁、技能文件、Bun 可执行文件和生成的 bundle 都进入身份校验；修改运行源码后需要重新构建。

也可以手动启动服务，再给 `math run` 传入 `--runtime-url`：

```bash
bun run math runtime --data-dir /absolute/private-runtime --port 25820
```

服务仅监听 loopback，Ctrl+C 停止。`--codex` 或 `DEEPSCIENTIST_MATH_CODEX_EXECUTABLE` 可以指定 Codex 可执行文件。不再需要导入 Core 运行包。历史 `--core-url` 参数仍兼容；旧 ACP 专用 `--model-isolation-policy` 暂不支持，指定后会拒绝启动。Worker worktree、Codex workspace-write 和独立 Lean 验证仍保留。

## 数学任务

```bash
bun run math bootstrap-imo \
  --repo /absolute/humanfia-imo2026 \
  --problem imo2026_q3 \
  --workspace /absolute/new-proof-workspace \
  --receipt /absolute/new-proof-workspace/active-problem.json

bun run math run \
  --build-manifest /absolute/build/manifest.json \
  --workspace /absolute/new-proof-workspace \
  --task-file /absolute/public-task.md \
  --receipt-file /absolute/new-proof-workspace/active-problem.json \
  --output /absolute/private-results/run.json
```

`--build-manifest` 使用 `build` 输出的路径。工作区必须满足原数学 runner 的 Git/题目契约；输出父目录必须是当前用户拥有的私有目录。IMO2026 默认使用宿主管理的 Lean 内核评测，显式 `--evaluator-command` 优先；Lean-Eval 独立评分需要配置对应 evaluator。

`solver_ready` 是经过宿主集成的评测触发信号。最终成功还要求 evaluator 通过；模型叙述、算例通过或局部 probe 都不能替代原题证明。

其他命令：

```bash
bun run math --help
bun run math run --help
bun run math bootstrap-lean-eval --help
bun run math freeze-retrieval --help
bun run math summarize --help
bun run test
```

运行服务和 runner 默认使用现有隔离 Codex profile `~/.config/deepscientist/math-sol-codex`。设置 `CODEX_HOME` 可指定显式 profile；认证信息不会复制到这个项目。数学工具配置默认读取 `~/.config/deepscientist-math/math.env`；通过 `DEEPSCIENTIST_MATH_ENV_FILE` 可以指定既有配置文件。

## 源码

- `src/math/`：数学契约、证明环境、Lean 反馈、检索、验证、回执、运行绑定与恢复。
- `src/runtime/`：Bun 运行服务、持久队列、角色权限和 Codex app-server 适配。
- `src/team/`：Team 客户端、协作协议和数学 MCP。
- `src/project-git/`：Git worktree、assignment 日志与源码集成。
- `src/mcp/`、`src/common/`、`src/shared/`：数学入口所需的 Artifact、证据和共享契约兼容层。
- `scripts/mathematics/`：从原项目保留的 headless runner 与任务准备工具。
- `resources/skills/deepscientist-mathematics/`：数学 SOP 和参考材料。
- `extraction.json`：原始 commit、文件来源和原始文件哈希。

兼容层仅保留数学入口使用的通用 Artifact、报告、图表与证据能力；金融、目标发现、竞赛和旧桌面模块已移除。文献检索支持公共论文搜索和 PaperClip。历史 Git 元数据及回执密钥的环境变量、路径和签名格式保留兼容。

验证使用独立 bundle 构建、CLI 进程边界测试，以及原项目中覆盖数学状态、源码集成、恢复和精确代数的回归测试。测试不会启动真实模型；模型求解效果和真实题目的评测通过率需要另行实验。
