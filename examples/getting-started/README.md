# 跑通第一个例子

这个例子证明两件小事：自然数加上零不变，零加上自然数也不变。
只使用 Lean 标准库，不下载 Mathlib，也不需要 FUSE。

可以先回放预设的证明尝试，看看 TheoremOS 如何检查失败、接收修复并验收结果；
准备好模型后，再让 Agent 从未完成的证明开始求解。

## 准备工具

在 Linux 上安装 Git、Bun 1.2+、Node.js 22+、Python 3、util-linux 和 Bubblewrap。
宿主需要允许 Bubblewrap 创建用户命名空间。
安装 Elan 后，准备示例固定的编译器：

```bash
elan toolchain install leanprover/lean4:v4.33.0
```

从项目根目录执行 `bun install --frozen-lockfile`。配置了数学环境文件时，
其中的 `PATH`、`ELAN_HOME` 和 `LEAN_SYSROOT` 也需要对应这一版本；
可以为示例使用单独的环境文件，保留已有实验配置。

## 先看一次回放

选择一个仓库外的新目录：

```bash
export THEOREMOS_REPLAY="$PWD/../theorem-os-runs/first-replay"
bun run math doctor --lean-only
bun run math example replay --dir "$THEOREMOS_REPLAY"
```

这条命令会构建并固定运行时、准备题目，然后提交两个预设候选：

1. 两个目标都尝试 `rfl`，第二个目标应被 Lean 拒绝。
2. 用 `Nat.zero_add` 修复第二个目标，再检查并集成完整证明。

检查在当前主机上真实运行，最终验收沿用普通求解器的独立 Lean 检查。
回放不会连接模型服务，候选是事先写好的；它展示检查流程，不代表模型解题能力。
只有最终状态为 `evaluated_passed`，才表示本次主机上的验收通过。

```bash
bun run math inspect --run "$THEOREMOS_REPLAY/result.json"
```

## 再让 Agent 自己证明

使用另一个新目录。CLI 默认使用本机已配置的 Sub2API DeepSeek profile；需要其他配置时设置 `CODEX_HOME`：

```bash
export THEOREMOS_CASE="$PWD/../theorem-os-runs/first-model-run"

bun run math doctor
bun run math example prepare --dir "$THEOREMOS_CASE"
bun run math doctor --project "$THEOREMOS_CASE/workspace/generated/addition"
bun run math example check --dir "$THEOREMOS_CASE"
bun run math example resume --dir "$THEOREMOS_CASE"
```

`prepare` 和 `check` 不调用模型；`resume` 会调用模型并产生相应费用。
默认使用单 Agent、`deepseek-flash`、`max`，最多 5 次调度和 5 分钟解题时间。
需要其他模型时，在 `prepare` 中传入 `--model`、`--effort` 或 `--codex`，后续命令会使用保存的配置。
中断后保留原构建、环境和配置，重复 `resume` 命令继续。

## 文件与结果

| 文件 | 内容 |
| --- | --- |
| `workspace/generated/addition/Submission.lean` | 题目和最终集成的证明 |
| `case.json` | 固定构建与运行方式 |
| `result.json` | 最终验收状态，以及 `example.source` 标注的候选来源 |
| `summary.json` | 本次执行摘要，注明预设回放或模型运行 |
| `result.json.runtime/` | 会话状态、候选、检查反馈和可恢复记录 |

`prepared` 只表示预检完成；报错、超时和未完成都不会算作证明成功。
这是教学题，使用本地验收，记录为 `official: false`。
运行真实公开题目可以继续看 [IMO2026 示例](../imo2026/README.md)；
想改研究方法，可以继续看[组件示例](../components/README.md)。
