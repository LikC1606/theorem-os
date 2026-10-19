# 替换一个研究组件

TheoremOS 的扩展单位是带版本的 `SolverModules` 组件。
Agent 数量和角色由运行时组织；替换研究策略无需新增 Agent。
目前通过 TypeScript 源码组合组件，尚未提供动态插件加载或稳定 SDK。

## 生成自己的组件

从仓库根目录执行：

```bash
bun run math component init --name my-search
bun run math component check --name my-search
```

第一条命令生成 `src/components/my-search.ts` 和 `scripts/components/my-search.ts`。
在第一个文件中修改 `ready` 函数，就能改变就绪任务的顺序；其余四个组件继续使用默认实现。
已有同名文件会被保留，命令会提示换一个名字。

`check` 不调用模型或 Lean，用几个本地任务检查排序是否保留了依赖、暂停、路线和预算约束。
它只检查这个排序模板的基本约定，策略是否有效仍需要实验。
改变策略后，更新 `id` 和 M3 的 `version`，再运行检查。

可以把组件接到[小题示例](../getting-started/README.md)中。先配置好 Codex 和 Lean 环境，再使用一个仓库外的新目录：

```bash
export THEOREMOS_COMPONENT_CASE="$PWD/../theorem-os-runs/my-search"
bun run math example prepare --dir "$THEOREMOS_COMPONENT_CASE" \
  --component my-search --workers 3
bun run math example check --dir "$THEOREMOS_COMPONENT_CASE"
bun run math example resume --dir "$THEOREMOS_COMPONENT_CASE"
```

`prepare` 会构建并固定组件源码和配置，`check` 只做启动预检，`resume` 才会调用模型。
M3 的 `ready` 排序用于至少三名 Agent 的协作任务；单 Agent 和预设回放不展示分工排序效果。
小题预算只有 5 次调度，适合检查接入流程，不能据此判断策略优劣。

修改源码后使用新案例；恢复原实验时保留它原来的源码、构建、环境和配置。
下面保留手动组合组件和运行任意已准备题目的方式。

## 组件合同

| 组件 | 主要输入 | 主要输出 |
| --- | --- | --- |
| M1 | 题目、上下文、操作、worker 与模型会话 | 候选记录及保存到工作区的证明 |
| M2 | 固定题目、候选源码、环境与已有检查 | 绑定提交和源码摘要的 `ProofCheck`，或辅助义务证据 |
| M3 | 研究状态、候选操作、共享预算、任务与路线 | 下一步操作、重试决策、有序的就绪任务 |
| M4 | 题目、研究状态、当前任务与可见证据 | 带来源身份的 `ContextBundle` |
| M5 | 就绪任务、worker、负责人和路线约束 | 隔离 worker 配置、任务分配与独立审阅者 |

完整类型在 [modules/index.ts](../../src/solver/modules/index.ts) 及其引用的实现中。
S1 档案和 S3 最终评测独立于这些研究决策。
M2 的局部成功与模型审阅均不能跳过 S3 对完整原题的重检。

## 示例：只替换 M3

[runGoalsFirst.ts](../../scripts/mathematics/runGoalsFirst.ts) 是完整入口。
它保留默认的证明构造、检查、上下文和协作组件，只将已就绪原题目标排在辅助任务之前：

```ts
import { directSolverModules, type SolverModules } from '../../src/solver/modules';
import { goalsFirstResearchTasks } from '../../src/solver/modules/search';

const modules: SolverModules = {
  ...directSolverModules,
  id: 'goals-first-example-v1',
  M3: {
    ...directSolverModules.M3,
    version: `${directSolverModules.M3.version}/example-goals-first-v1`,
    ready: goalsFirstResearchTasks,
  },
};
```

`goalsFirstResearchTasks` 先调用原有就绪筛选，再排序，保留依赖、暂停与路线预算检查。
可以在此基础上实现自己的排序规则；返回值必须来自当前可启动任务。

按[快速开始](../../README.md#快速开始)准备依赖、题目和任务文件后，从仓库根目录执行：

```bash
bun run build
export MATH_BUILD_MANIFEST="/absolute/path/to/the/new/manifest.json"
export MATH_RUN_ROOT="/absolute/path/to/prepared/problem"

bun scripts/mathematics/runGoalsFirst.ts \
  --build-manifest "$MATH_BUILD_MANIFEST" \
  --workspace "$MATH_RUN_ROOT/workspace" \
  --task-file "$MATH_RUN_ROOT/task.md" \
  --output "$MATH_RUN_ROOT/goals-first-result.json" \
  --workers 4 \
  --startup-only
```

预检不调用模型。随后用相同入口和参数，移除 `--startup-only` 并添加 `--resume`，
开始真实求解。使用已有的 Codex profile 时，按快速开始设置 `CODEX_HOME`。
该入口已注入组件组合，请保留默认 `--scheduler plan`，不要再叠加其他调度策略。

自定义实现放入 `src/`，入口放入 `scripts/` 或 `bin/`，使源码纳入构建清单。
修改组件行为后更新相应 `version` 并重新构建；版本参与运行身份，已有运行会拒绝不同组件版本。
恢复原实验应保留原构建与组件；测量新组件应使用全新题目工作区和输出目录。

比较方法时固定题目、模型、环境、预算和评测器，记录所替换组件及其版本。
网页同格式方案的批量对照入口、首轮配置和证据边界见[模块实验](EXPERIMENTS.md)。
单智能体、独立并行和协作的运行与汇总方式见[对照实验](../imo2026/COMPARISON.md)。
这个示例展示组件替换，不代表排序策略已经带来性能提升。
