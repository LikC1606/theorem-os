# Future sealed proof reuse fix — 2026-10-24

已在独立副本完成最小修复：`resolveMathProofEnvironment` 成功验证 sealed 环境后，`proofReuseEnvironment` 将生成的 `.lake/package-overrides.json` 摘要统一为 `null`。这与已有 `consumerConfiguration` 的边界一致。产品代码仅增加注释和一个条件返回；精确差异见 [runtime.patch](runtime.patch)。

语义配置、实际 sealed 包身份、环境与工具身份仍受原有检查约束。无效 descriptor 仍拒绝复用；unsealed 环境继续绑定覆盖文件字节，并拒绝 mutable packages、`LEAN_PATH`、`LEAN_SYSROOT` 和 trusted cache roots。

## 验证

| 文件 | 通过 | 跳过 |
| --- | ---: | ---: |
| proofReuseEnvironment.test.ts | 15 | 0 |
| taskProofCache.test.ts | 55 | 0 |
| solverProjectionReuse.test.ts | 6 | 0 |
| taskTypePreflight.test.ts | 64 | 0 |
| mathProofEnvironment.test.ts | 8 | 1 |
| solverEvidenceReuse.test.ts（单独补跑） | 23 | 0 |
| 合计 | 171 | 1 |

0 项失败。前五文件 148 项通过；随后只补跑另一个调用方 `solverEvidenceReuse.test.ts`，23 项通过。唯一跳过项是需要真实 Codex sandbox 的编译测试。新回归包括 9 项实际 FUSE sealed 测试、6 项 unsealed 测试及 2 项带模拟 verifier 的集成缓存命中测试；未调用实际模型或 Lean 编译。

实际回执：[focused-tests.json](focused-tests.json)、[solverEvidenceReuse-tests.json](solverEvidenceReuse-tests.json)；命令与逐文件统计见 [verification-summary.json](verification-summary.json)。测试通过 Node 24.20.0 执行 Vitest 4.1.0；build 使用 Bun 1.4.0。

首次 Node 测试中，已有 `solverProjectionReuse` 夹具只指定 PATH，读取宿主默认 `math.env` 的 mutable trusted cache roots，导致 6 项缓存预期失败。在隔离目录内恢复冻结版 `proofReuse.ts` 与原测试夹具，单文件仍复现同样 6 项失败，随后恢复最终文件。夹具仅增加临时 `DEEPSCIENTIST_MATH_ENV_FILE`，与现有 task cache 测试约定一致。记录：[首轮失败](focused-tests.initial-node.log)、[冻结基线复现](baseline-reproduction.json)、[基线原始报告](baseline-solverProjectionReuse.json)、[环境原因](fixture-environment-cause.json)。

## 真实项目的只读对照

2026-10-24 09:07:34 UTC，对实际交付源与当时存在的两个干净投影调用实际 sealed resolver、冻结版与修复版函数。完整路径和结果见 [reuse-environments.fixed.json](reuse-environments.fixed.json)，查询脚本见 [read-real-reuse-environments.ts](read-real-reuse-environments.ts)。

三者 sealed identity 均为 `900fd1e9244b72b3131a752636e67f20341702d3490776cfe4b267bf2f9b2460`；Submission SHA256 均为 `5c0cbc35bd6335ab7c6d8d57bdece22a3065c6fdc7dee871d2577826b50396d3`。交付源的冻结版摘要为 `3336373af58fcc70d25216b2fb4741c243d67b34213bdd7b826af12593ac1139`；修复后三者摘要均为 `e7d8bb593a02d613eed3ff293ca14dfcd6a69ca47958579069843cdb19f67056`。查询前后项目配置和 Submission 字节一致。

这使未来使用新构建、同一 run 内共享缓存且完整投影及其余输入相同的 delivery/integration 可以命中缓存。此处仅验证摘要一致；没有执行实际缓存查询、生成 verifier receipt 或切换当前运行。未声称当前链已免编译，也不扩大到 all-target 或 publisher 复用。

## 构建与后续入口

headless build 成功生成 3 个 bundle，200 个源码输入已绑定到 manifest；随后通过 `readMathBuildManifest` 校验最终源码与三个产物。详情与完整 SHA256 见 [build-verification.json](build-verification.json)。

构建 ID：`74fd563c-1e68-4d0d-83d0-14ebbd9f79f8`。

Manifest：[build-state/builds/74fd563c-1e68-4d0d-83d0-14ebbd9f79f8/manifest.json](build-state/builds/74fd563c-1e68-4d0d-83d0-14ebbd9f79f8/manifest.json)。

Solver bundle：[runtime/out/main/math-solver.js](runtime/out/main/math-solver.js)，SHA256 `0b464edfbcf9765e208cf667f1445a8bee1a6a2366f5eb914328c35b92cb72c2`。

后续重新构建入口（从本目录执行）：

```bash
/home/lzh/.venvs/deepscientist-finance/.bun/bin/bun runtime/scripts/build.ts --state-root "$PWD/build-state"
```

未来新运行使用本副本 `runtime/bin/math.ts run` 或上述 solver bundle，并显式传入本次 manifest 的 `--build-manifest`。新的 workspace、task-file、output 与启动策略由新运行确定；本交付没有启动新运行或恢复旧运行。

## 隔离与交付边界

副本基于 `character-environment-adapter-20261023/unlimited-preparation-v2/runtime`。源码、资源和依赖均独立复制；副本内没有符号链接，也未使用指向冻结 runtime 或主区的可写依赖。构建 state 仅位于本目录的 `build-state`，测试使用独立临时目录及新建的小型依赖镜像/cache。

冻结 runtime 的 386 个受检查条目在任务前后内容、大小、模式一致。主区 `/home/lzh/theorem-os`、活动 frozen runtime、现有 cache/state 和 results 未由本任务写入；当前 run 未切换，没有 commit 或发布。隔离证据与逐文件 SHA256：[isolation-verification.json](isolation-verification.json)、[frozen-runtime-before.json](frozen-runtime-before.json)。

源码/测试边界为 4 个文件：两行产品修复、一个新回归测试文件、task cache 中的两项回归，以及原 projection 测试夹具的一项环境隔离修正。另有三个预期 bundle 变化；[runtime.patch](runtime.patch) 不含构建产物。修复保留在本副本，供父任务最终 review 与归档。
