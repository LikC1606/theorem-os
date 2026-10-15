# TheoremOS

[![License: AGPL-3.0](https://img.shields.io/badge/license-AGPL--3.0-blue.svg)](LICENSE)
[![Bun](https://img.shields.io/badge/Bun-%E2%89%A5%201.2-black?logo=bun)](https://bun.sh/)
[![Node.js](https://img.shields.io/badge/Node.js-%E2%89%A5%2022-339933?logo=nodedotjs&logoColor=white)](https://nodejs.org/)

TheoremOS 是一个用于探索数学 Agent 研究方法的开源项目。它把证明构造、检查反馈、搜索决策、上下文选择和协作分工拆成五个可替换的组件，让你可以单独改进其中一部分，再用 Lean 检查生成的证明。

例如，你想试试“先证明原题中已经能处理的目标，再研究辅助引理”是否更有效，就可以换掉任务排序组件，沿用其余部分。在相同的题目、环境和预算下比较结果，才能看清这个改动有没有帮助。

项目使用 TypeScript 和 Bun，通过 Codex 执行 Agent 会话，目前支持 [Humanfia IMO2026](https://github.com/humanfia/imo2026) 和 [Lean-Eval](https://github.com/leanprover/lean-eval) 题目。

[快速开始](#快速开始) · [替换一个组件](examples/components/README.md) · [运行指南](docs/usage.md) · [发布说明](docs/releases/v0.1.0.md)

## 组件模型

一次求解会反复经历：选择任务、整理上下文、尝试证明、检查结果，再决定下一步。TheoremOS 把这些决定分开，方便尝试不同的方法。

| 组件 | 做什么 | 可以尝试的改动 |
| --- | --- | --- |
| M1 证明构造 | 调用模型，生成候选证明 | 换一种证明生成方式 |
| M2 检查与反馈 | 检查候选，把错误和未完成的部分反馈给 Agent | 提供更有用的诊断信息 |
| M3 搜索决策 | 选择下一步任务，决定重试或停止 | 优先处理更有希望的目标 |
| M4 上下文选择 | 整理本次尝试需要的题目、成果和失败记录 | 减少无关信息，保留关键线索 |
| M5 协作与复用 | 分配任务、安排审阅、复用已有成果 | 改变多个 Agent 的分工方式 |

这些组件与 Agent 数量无关：单个 Agent 也会用到多个组件，多个 Agent 也可以共用一套组件。你可以运行单 Agent、独立并行尝试，或让多个 Agent 协作。

想动手改一个组件，可以从 [M3 搜索组件示例](examples/components/README.md) 开始：保留其余四个组件，只替换就绪任务的排序。示例给出了代码和运行入口；内置的 `--scheduler goals-first` 也可以直接试用这一策略。

目前组件通过 TypeScript 源码接口替换，接口仍可能调整。运行时会保存组件版本，恢复运行时检查版本是否一致。当前版本尚未提供稳定 SDK 或动态插件加载。

## 快速开始

建议先跑仓库自带的 IMO2026 Q1 示例。它会从固定的公开题目版本开始，尝试证明全部五个目标，并保存过程与结果。

### 1. 安装并配置环境

目前支持 Linux，需要以下工具：

- Git、Bun 1.2+、Node.js 22+、`/usr/bin/python3`。
- 已安装并完成认证的 Codex CLI，以及可用的 Lean / Elan 工具链。
- Bubblewrap（`bwrap`）、`mksquashfs`、`squashfuse` 或 `snapfuse`、`fusermount3` 或 `fusermount`，以及 FUSE 挂载权限。

```bash
git clone https://github.com/LikC1606/theorem-os.git
cd theorem-os
bun install --frozen-lockfile
```

根据[环境模板](examples/imo2026/math.env.example)准备本地配置，填好工具和缓存路径。使用你已认证的 Codex profile：

```bash
export CODEX_HOME="/absolute/path/to/your/codex-profile"
export DEEPSCIENTIST_MATH_ENV_FILE="/absolute/path/to/your/math.env"
```

首次准备会下载 Mathlib 依赖，需要网络、足够的磁盘空间和内存。工具安装与资源要求见[示例说明](examples/imo2026/README.md#requirements)。

### 2. 准备题目并检查环境

选择一个仓库外的新目录，保存本次实验：

```bash
export THEOREMOS_CASE="$PWD/../theorem-os-runs/imo-q1"

bash examples/imo2026/reproduce.sh prepare "$THEOREMOS_CASE"
bash examples/imo2026/reproduce.sh check "$THEOREMOS_CASE"
```

`prepare` 构建运行时、准备题目和依赖；`check` 检查运行条件并保存初始状态。这两步不调用模型。

### 3. 开始求解

```bash
bash examples/imo2026/reproduce.sh resume "$THEOREMOS_CASE"
```

这一步会调用已配置的模型并产生相应费用。示例使用 `gpt-6.1-sol`、`xhigh` 和四个 Agent，共享 30 分钟解题时间、合计 20 次模型调度。预算内可能无法完成证明，结果会如实保留。

终端会输出 JSON 进度事件。也可以用 `inspect` 查看已保存的进展：

```bash
bun run math inspect --run "$THEOREMOS_CASE/result.json"
```

中断后，使用同一条 `resume` 命令继续，并保留原来的构建、环境和配置。准备其他题目或自定义运行参数，见[运行指南](docs/usage.md#手动准备与运行)。

## 验证与结果

Agent 写出证明后，TheoremOS 会检查原题声明和受保护文件，运行 Lean，并在集成后重新验证全部原题目标。模型说“完成了”或同伴审阅通过，都不能代替最终检查。

结果保存在实验目录的 `result.json` 中。**只有 `status: evaluated_passed` 表示最终验收通过**；`prepared` 表示环境已准备好，`incomplete`、`limit_reached`、`evaluated_failed` 和 `runtime_error` 则需要结合诊断继续查看。

IMO2026 使用独立的本地 Lean 验收，记录为 `official: false`；Lean-Eval 使用其官方比较器。检查记录、失败反馈、任务计划和累计用量都会保存，方便恢复和复查。

如果要比较单 Agent、独立并行和协作的效果，可以使用[三组对照实验](examples/imo2026/COMPARISON.md)。目前尚无证据表明协作一定更快或更容易解出题目；组件的效果需要通过具体实验判断。

## 架构与开发

想读代码，可以从 [SolverModules](src/solver/modules/index.ts) 看五个组件的接口与默认组合，再看 [run.ts](src/solver/run.ts) 如何准备和验收一次运行。[组件示例](examples/components/README.md) 展示了如何把自己的实现接进去。

欢迎贡献新的组件策略、题目适配器，以及可复现的问题和实验。提交问题时，请附上运行命令、依赖版本、结果状态和相关诊断，并移除认证信息。

开发时常用的命令：

```bash
bun run test
bun run typecheck
bun run build
```

测试使用本地 fixture 和模拟会话，不调用真实模型。参数、断点恢复、人工计划修改、批量运行和协作协议见[运行指南](docs/usage.md)。

当前发布为 [v0.1.0 Research Preview](https://github.com/LikC1606/theorem-os/releases/tag/v0.1.0)，适合尝试研究思路和源码扩展。跨任务学习尚未实现，版本范围与限制见[发布说明](docs/releases/v0.1.0.md)。

## 许可证与致谢

本项目从 DeepScientist 的数学证明运行时抽取，使用 [AGPL-3.0-only](LICENSE)；来源与第三方声明见 [NOTICE](NOTICE)。保留独立许可证声明的文件遵循其各自条款。

项目原名 DeepScientist Math，目前仍保留 `deepscientist-math` CLI 别名、`bun run math` 以及已有环境变量和配置路径，方便继续使用已有实验。

感谢 [Lean](https://lean-lang.org/)、[Mathlib](https://github.com/leanprover-community/mathlib4)、[Humanfia IMO2026](https://github.com/humanfia/imo2026) 与 [Lean-Eval](https://github.com/leanprover/lean-eval) 提供的形式化工具、数学库和公开评测资源。
