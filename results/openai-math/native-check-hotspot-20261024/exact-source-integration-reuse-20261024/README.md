# Exact-source single-task integration reuse

已在 Honeycomb 最新 runtime 的全新独立副本中完成最小修复，保留已检查 delivery 的完整 owned 源码字节，消除 unchanged-seed 单任务集成中由声明拼接引起的空行丢失。缓存仍使用完整投影及原有全部输入；没有修改 TaskProofCache、缓存键或空白处理规则。

快路径仅在以下条件同时满足时生效：没有待消解的条件、每个当前 owned 文件与 delivery seed 完全相同、从 immutable delivery 重算的完整 declaration changes 和新增 imports 与授权补丁一致。随后只复制 delivery 的 owned 源码，再执行原有 assertSolverSources。存在 peer 改动、条件消解或补丁不一致时继续原声明合并。批集成没有改动。

产品差异位于 [cooperativeProof.ts](runtime/src/solver/cooperativeProof.ts)、[cooperationIntegration.ts](runtime/src/solver/cooperationIntegration.ts)；另包含已验证的 [proofReuse.ts](runtime/src/solver/proofReuse.ts) 两行 sealed override 修复。完整差异见 [runtime.patch](runtime.patch)。基础源码来自 `validation/honeycomb-new-build-continuation-20261024/runtime`，保留该新版的错误分类、并发、条件与调度实现。

真实 Snaky 历史源码已在本次独立 clone 中复现，记录见 [snaky-reproduction.json](snaky-reproduction.json)。canonical 和 assignment seed 的 owned 源码原本完全相同；2908 项 changes 经旧合并后精确复现历史 integration，新路径完整保留 delivery。

| 真实源码样本 | 字节 | 换行 | SHA256 前缀 |
| --- | ---: | ---: | --- |
| 已检查 delivery | 968784 | 16371 | 712ecd4ee1a6cf29 |
| 旧合并及历史 integration | 967683 | 15270 | dc40df160330f905 |
| 新合并 | 968784 | 16371 | 712ecd4ee1a6cf29 |

同一次机制复现实际调用 checkTaskProofs、createTaskSourceProjector 和 TaskProofCache：delivery 与新合并的完整投影 tree 均为 `9981650602a4bfb3ef3578c26d5f6df3711a6098`，旧合并为 `d8f3b11f7d2558918a8f1225992df2053427533a`。真实缓存调用 key 的 delivery/new 均为 `f461a750969ed9436935eea6efa3381afcb84f5d3f5330f227725bd3d66697bd`，old 为 `1157b9d177d79a3acfaca2d94448cd4c65cb03cf323e190f4cb8043a82e6ee02`。verifier 调用计数为 1 → 2 → 2，新合并复用原 receipt 对象内容；delivery 的 generated override 与 clean integration 的缺失配置也包含在此检查中。

上述 verifier、工具身份和 sealed 身份明确使用测试 stub；测试验证真实源码、完整投影与缓存机制，没有执行 Lean 或模型，也不构成新的数学验收或生产 receipt。单次本机测量中，旧声明合并为 28.36 秒，新路径为 0.271 秒；这不是 Lean 时间或其他题目的速度保证。

| 最终检查 | 通过 |
| --- | ---: |
| 精确源码、peer、所有 owned、授权补丁、imports、条件、源码保护及实际单任务调用方 | 10 |
| 缓存、条件集成、并发集成、批集成及投影归属回归 | 115 |
| 真实 Snaky 字节、完整投影和实际缓存 key/hit 机制复现 | 1 |
| 合计 | 126 |

0 项失败，TypeScript typecheck 及三 bundle headless build 通过。首次测试的两项夹具/断言失败及修正记录保存在 initial 报告中；没有为这些失败修改产品逻辑。执行记录见 [test-runs.json](test-runs.json)、[verification-summary.json](verification-summary.json)。没有将历史的 27/171 项检查计入本次 126 项。

构建 ID 为 `1537a457-5694-4896-99fe-f2e9248cb6fc`，manifest 为只读 `0400`，绑定 210 个源码输入及三个 bundle，已通过真实 readMathBuildManifest 校验。见 [build-verification.json](build-verification.json)、[manifest](build-state/builds/1537a457-5694-4896-99fe-f2e9248cb6fc/manifest.json)。solver SHA256 为 `b6fb606bb2c2c4f34be905b1ad3fdb60050e23bbbc80fa06adc293821f477a97`。

完整本地目录为 `/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/exact-source-integration-reuse-20261024`，也是 delivery-files.json 的 root。以下命令须在该完整目录执行；results 归档仅保存无依赖的摘录，不含完整 runtime、node_modules 或 Snaky clone，不能用作执行目录。

```bash
/home/lzh/.venvs/deepscientist-finance/.bun/bin/bun runtime/scripts/build.ts --state-root "$PWD/build-state"
```

CLI 入口为 [runtime/bin/math.ts](/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/exact-source-integration-reuse-20261024/runtime/bin/math.ts)。未来新运行可从上述完整目录使用以下模板：

```bash
/home/lzh/.venvs/deepscientist-finance/.bun/bin/bun runtime/bin/math.ts run \
  --build-manifest "$PWD/build-state/builds/1537a457-5694-4896-99fe-f2e9248cb6fc/manifest.json" \
  --workspace '<new-workspace>' --task-file '<new-task-file>' --output '<new-output>'
```

本次没有执行启动模板或切换活动构建。收益限于未来使用本构建、完整投影及全部缓存输入相同的 run-local 单任务集成；不提供跨 run、all-target 或 publisher 复用。当前活动任务、旧缓存与旧 receipt 均未改写。

源码及依赖均为独立副本，无符号链接、无与基线共享的 inode。最新基线的 1307 个受检查条目前后内容、大小与模式均保持一致，见 [source-runtime-before.json](source-runtime-before.json)、[isolation-verification.json](isolation-verification.json)。所有 Git 写入限于本次新 clone 和临时测试仓库；没有修改主 checkout、提交或推送工作成果，也没有读取 ProducedSolution 或隐藏推理。

可归档文件精确列于 [delivery-files.json](delivery-files.json)，校验和见 [SHA256SUMS](SHA256SUMS)。仅包含报告、patch、5 个变更源码/测试文件、3 个 bundle 和只读 manifest；排除其余 runtime、全部依赖、Snaky clone 及历史运行 state/receipt。
