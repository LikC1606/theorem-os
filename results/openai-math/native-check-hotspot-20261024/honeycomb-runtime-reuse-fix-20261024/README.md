# Honeycomb latest runtime — sealed reuse fix

已将已验证的 sealed override 摘要修复移植到 Honeycomb 真正最新 runtime 的全新隔离副本，并完成聚焦验证和 headless build。最新基线为 `validation/honeycomb-new-build-continuation-20261024/runtime`；没有使用旧 Character runtime 覆盖新版源码。

产品差异仅为 `src/solver/proofReuse.ts` 的两行：在 `resolveMathProofEnvironment` 成功后，将 `.lake/package-overrides.json` 的摘要统一为 `null`，与 sealed consumer 已有的实际配置边界一致。精确差异见 [runtime.patch](runtime.patch)。语义配置、sealed 包身份、工具和运行环境仍按原规则绑定；无效 sealed descriptor 和 mutable unsealed 输入仍拒绝复用。

Honeycomb 最新的 verifier 并发配置、lease 所有权检查、raw/JSON Lean 错误识别、条件声明排序及调度/集成源码均来自最新基线。除这两行产品修复外，其余产品源码逐文件保持一致；对比依据见 [isolation-verification.json](isolation-verification.json)。没有把旧版错误分类逻辑或调度实现带回新版。

## 本次实际验证

| 检查 | 实际通过 |
| --- | ---: |
| sealed/unsealed 环境回归（含 9 项真实 FUSE sealed 检查） | 15 |
| delivery/integration 覆盖文件缺失或路径不同的缓存命中 | 2 |
| 新版调用方：中断关键词、失败边界和 sealed 包身份 | 10 |
| 合计 | 27 |

0 项失败。后两组按测试名过滤，67 项未选中的测试没有执行。原 171 项结果属于之前 Character 隔离修复的历史证据，本次没有重跑或声称 Honeycomb 全套 171 项通过。

实际报告：[environment-tests.json](environment-tests.json)、[caller-tests.json](caller-tests.json)。完整执行命令及次数见 [test-runs.json](test-runs.json)，汇总见 [verification-summary.json](verification-summary.json)。测试使用 Node 24.20.0 / Vitest 4.1.0；构建使用指定 Bun 1.4.0。真实模型与 Lean 编译均未调用。

复用历史证据仅基于已核对的相同实现：`proofReuseEnvironment` 函数体、sealed resolver、configuration 文件表、TaskProofCache、依赖版本和构建器与上一修复相同。新版环境增加 verifier concurrency 配置，lease 实现也有更新，因此本次重新运行实际 sealed/unsealed 测试；新版错误分类通过选定调用方测试。核对记录见 [evidence-reuse.json](evidence-reuse.json)。之前真实 Character delivery/clean projection 的只读摘要记录没有在 Honeycomb 活动项目上重跑。

## 冻结构建与入口

构建 ID：`554d6726-fa7b-4b1c-b84b-f846f20b609d`。Manifest 为只读 `0400`，绑定 210 个最新源码输入和三个 bundle；已通过 `readMathBuildManifest` 对最终源码与产物的校验。完整路径、大小及 SHA256 见 [build-verification.json](build-verification.json)。

Manifest：[build-state/builds/554d6726-fa7b-4b1c-b84b-f846f20b609d/manifest.json](build-state/builds/554d6726-fa7b-4b1c-b84b-f846f20b609d/manifest.json)。

可执行 solver：[runtime/out/main/math-solver.js](runtime/out/main/math-solver.js)。SHA256：`4f3b1b0feb48fe24001719d49eec473d6b77c0f2171b5ffe7d039f5dd049c7f7`。

CLI 入口：[runtime/bin/math.ts](/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/honeycomb-runtime-reuse-fix-20261024/runtime/bin/math.ts)。

以下启动和重新构建命令均须从 `delivery-files.json` 的 `root` 所示完整本地目录执行：`/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/honeycomb-runtime-reuse-fix-20261024`。`results` 中仅保存无依赖的归档摘录，不含完整 runtime 和 `node_modules`，不能作为这些命令的工作目录。

未来新运行可在上述完整本地目录使用以下模板，另行提供新 workspace、task 和 output：

```bash
/home/lzh/.venvs/deepscientist-finance/.bun/bin/bun runtime/bin/math.ts run \
  --build-manifest "$PWD/build-state/builds/554d6726-fa7b-4b1c-b84b-f846f20b609d/manifest.json" \
  --workspace '<new-workspace>' --task-file '<new-task-file>' --output '<new-output>'
```

本次只交付构建，没有执行这个启动模板，也没有启动求解、恢复、迁移或切换当前 run。收益是在未来使用此构建的新 run 中，完整投影、任务、验证工具及其他缓存输入相同时，delivery 与 clean integration 可以共享原有 run-local proof cache。此修复不提供跨 run、all-target 或 publisher 复用，也不会给现有活动链补造 cache 或 verifier receipt。

如需重新构建，仍从上述完整本地目录执行：

```bash
/home/lzh/.venvs/deepscientist-finance/.bun/bin/bun runtime/scripts/build.ts --state-root "$PWD/build-state"
```

## 隔离和审阅材料

源码与依赖均为独立副本，内部没有符号链接。依赖取自上一份已验证的隔离副本，其 `package.json` 和 `bun.lock` 与 Honeycomb 最新源完全一致；没有通过最新源指向 `/home/lzh/theorem-os/node_modules` 的链接执行测试或构建。构建 state 仅位于本目录 `build-state`，测试仅新建并清理自己的临时 fixture/cache。

最新源的 1307 个受检查条目在任务前后内容、大小和模式一致。活动 runtime、bundle、manifest、state、cache 和主区均未由本任务修改；没有提交、推送或读取 ProducedSolution/隐藏推理。

交付差异为 3 个源码/测试文件和 3 个构建产物：两行产品修复、15 项环境回归测试文件、2 项 task cache 回归；未迁移旧版测试夹具的无关修改。审阅入口：[runtime.patch](runtime.patch)、[source-runtime-before.json](source-runtime-before.json)、[isolation-verification.json](isolation-verification.json)。

可归档的精确文件清单见 [delivery-files.json](delivery-files.json)，校验和见 [SHA256SUMS](SHA256SUMS)。文件清单包含报告、patch、三个变更文件、三个 bundle 和 build manifest；不要求归档整个 runtime 或依赖。
