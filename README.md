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
  --output /absolute/private-results/run.json
```

`build` 生成 `out/main/math-solver.js`、`search-lean.js` 和 `check-lean.js`，并输出 `buildManifestRef`。源码和 bundle 均校验哈希；修改源码后需要重新构建。后两个 bundle 可挂载到隔离环境，供模型检索和编译诊断。

`run` 直接启动 Codex app-server。状态保存在 `<output>.runtime/` 私有目录中；用相同参数加 `--resume` 恢复。环境准备和依赖预编译使用独立的 `--prepare-timeout-seconds`（默认 1800）；之后才开始 `--max-run-seconds`（默认 1800）的解题预算。`--max-turns` 默认 20，`--max-turn-seconds` 默认 180，长轮次停止写入后由宿主检查已保存源码。`check-lean --workspace DIR --file FILE` 提供默认 90 秒的局部诊断，保留失败退出码和最早错误；局部诊断不代表最终验收。`--startup-only` 只检查准备条件，不调用模型。历史 Team 状态不兼容，需要创建新运行。

`--method lemma` 启用辅助引理方法：先尝试原题，遇到失败后提出一个引理，分别检查条件性连接和引理证明，再完成原题。模型在 `RESEARCH.md` 的单个 `math-lemma` JSON 代码块记录 `proofPath`、原题完整名称 `target`、引理完整名称 `lemma` 和完整闭合 Lean 类型 `type`。引理使用普通 `:=` 证明，置于同一文件的目标之前；目标通过引理的局部名称引用它。宿主在临时 worktree 中将引理替换为目标的显式参数来检查连接，移除原题定理来独立检查引理及其完整类型。未证引理不能触发原题通过；所有操作共享原有预算，恢复时重新检查辅助义务。默认仍为 `--method direct`。

原题声明、已有定义和受保护文件不能修改；只有全部目标通过宿主 Lean 内核检查才进入评测。IMO 使用集成后再次执行的内核检查，Lean-Eval 使用独立官方评分；可用 `--evaluator-command` 指定额外评测。模型的完成消息不代表证明通过。

其他命令通过 `bun run math --help` 查看，包括 `bootstrap-lean-eval`、`freeze-retrieval` 和 `summarize`。

Codex 默认使用 `~/.config/deepscientist/math-sol-codex`；`CODEX_HOME` 可以指定已有 profile，`--codex` 可以指定可执行文件。认证信息不会复制到项目。数学环境默认读取 `~/.config/deepscientist-math/math.env`，可通过 `DEEPSCIENTIST_MATH_ENV_FILE` 指定。

## 源码

- `src/solver/run.ts`：直接证明与辅助引理方法的调用循环，以及统一预算、取消、锁和事件。
- `src/solver/lemma.ts`：引理提案、条件性连接和引理证明的隔离检查。
- `src/solver/modules/`：按[设计文档第 2、4 节](https://ucnndba7qjef.feishu.cn/docx/Zy8rdyGJXonkChxYsLecn2Rbntg)拆分的可替换运行模块。
- `src/runtime/codexSession.ts`：Codex stdio 协议适配。
- `src/math/`：数学契约、题目准备、Lean 验证、证明环境和结果汇总。
- `scripts/mathematics/`：CLI 命令入口。

| 模块 | 实现 | 输入与交付 |
| --- | --- | --- |
| M1 研究执行器 | `modules/execution.ts` | 题目、上下文、操作与执行者 → 候选版本、来源及待检查义务 |
| M2 证据检查器 | `modules/evidence.ts` | 题目与候选源码 → 绑定冻结提交、源码摘要和原题目标的 Lean 回执 |
| M3 价值估计器 | `modules/value.ts` | 状态与选项 → 剩余轮次预测及不确定性；默认标记为未估计、未校准 |
| M4 搜索控制器 | `modules/search.ts` | 状态、选项、估计与预算 → 继续/停止，以及模型限流的重试计划 |
| M5 上下文构造器 | `modules/context.ts` | 题目、状态及访问范围 → 指令、反馈和题目/回执/语料来源标识 |
| M6 团队组织器 | `modules/organization.ts` | 行动、可用执行者与预算 → 单研究者安排及隔离规则 |
| M7 成果集成器 | `modules/integration.ts` | 成果与回执 → 集成候选、依赖闭合状态和待复验目标 |
| S1 任务与成果档案 | `archive.ts` | 保存和恢复任务身份、候选、回执、失败及运行状态 |
| S3 环境与评测合同 | `problem.ts`、`evaluation.ts`、`src/math/` | 冻结任务与环境，集成后重新检查原题并执行独立评测 |

`src/solver/modules/index.ts` 绑定默认模块及版本。`runSolver(args, root, modules)` 支持独立替换模块；模块版本参与恢复身份，宿主仍固定执行源码边界检查、总预算限制和最终验收。模块输出预测、生成候选或完成集成都不能直接授予原题通过状态。

两种方法均为单研究者执行：M3 默认返回未校准估计，M6 安排已有执行者，M7 接入完整证明。辅助引理回执记录各自检查的投影提交、原候选提交和源码摘要；最终验收仍独立检查全部原题目标。S2 跨任务学习尚未实现。

辅助义务的完整投影内容、提案和环境都一致时，可复用本进程已检查的成功回执；研究日志不参与证明检查。证明输入或环境改变即重新检查，恢复后的档案回执不能授权复用。同一失败义务连续两次没有证明输入变化时，控制器重新分解路线，并保留失败原因供下一轮参考。

测试不调用真实模型。`bun run test` 验证运行边界；`bun run typecheck` 检查接口。
