本次加速审查只新增本目录的诊断脚本、隔离 fixture 和报告，没有修改活动冻结 runtime、题目源码、checkpoint 或原 comparator。

可用的最小加速是：首次交付就使用冻结 `taskChanges → applyTaskChanges → createTaskSourceProjector` 的精确固定点源码。现有 `TaskProofCache` 可以把同一 run 内候选检查的可信 artifact 用于合并检查；无需修改缓存键、伪造 receipt、转移 worker 的 `.olean`，也无需工程补丁。

真实 Lean 验证见 [real-lean-cache-smoke.json](cache-real-lean-smoke.json)。未使用 mock、工具 wrapper 或真实模型。使用已安装的标准库 pinned Lean 4.33.0，无包下载。goal 648 ms、integration 34 ms；两步合计只调用一次可信 verifier，原 receipt 完整保留。修改源码、任务 objective/revision、环境 LANG 后分别再次调用可信 verifier；总计四次，2,547 ms。32 GiB 限制和无限 timeout 来自未修改的原 verifier。该烟测只验证缓存机制，不构成 Lean 4.34.1 大题的数学验收。

现有缓存与 host rebind 安全测试在 `/home/lzh/theorem-os-validation-fixes-20261023` 使用 Node 运行：

```text
node node_modules/vitest/vitest.mjs run tests/taskProofCache.test.ts tests/solverProjectionReuse.test.ts
Test Files 2 passed (2)
Tests 59 passed (59)
Duration 9.34s
```

最初以 Bun 启动 Vitest 时出现 `z.object` 导入错误、未执行测试；改用 Node 后上列 59 项通过。第一次真实烟测的候选仍带声明末尾空行，冻结 merger 删除了一行，固定点断言失败；保留的 `goal-proof.json` 是该次已经通过的小题真 Lean receipt，不能用作固定点烟测通过证据。正式通过结果位于 `real-smoke-fixed-point/`，修正的是独立 fixture 的候选源码，无 runtime 修改。

完整键相同的必要条件：

- 同一 `CooperativeResearch` 实例持有同一内存 cache；重启不保留，32 entries / 32 MiB 超限会驱逐。
- 同一 repository common directory、完整 projection Git tree 和完整 problem。
- ordered targets、任务 digest、retainedGoals、依赖、conditions 和 connection check 相同。
- 同一可复用 sealed 环境、实际 Lean/Lake 工具身份、环境 digest、trusted roots、执行选项和 timeout。
- 原 artifact 有可归因的成功 kernel receipt；命中时仍检查旧 projection tree 和 receipt attribution。

`sourceCommit`、`seedCommit`、worker ID 不直接进入键。`RESEARCH.md` 在 `commitSolverProjection` 中删除。`COOPERATION.json` 等 journals 被 `commitSolverSources` 的根路径 exclude 排除，且不会被其 staging；如果异常地已进入 tracked tree，它们仍会影响完整 tree。不要因此把所有 metadata 排除出 key。

新 commit 的归因来自原有 `projectionReuse`，由同进程 WeakMap 授权；原 receipt 的 targetCommit/session/checkedAt 不改写。序列化映射无效，host 再验两棵树、精确源码投影、声明与任务请求，并 pin 两个 commit。

V8 的当前 968,784-byte raw candidate 与 merge/project 后 967,683-byte 版本相差 1,101 个空行字节，tree 不同。当前正在运行的 raw candidate receipt 不能直接给固定点 integration 命中；修改 objective/revision 也会改变任务 digest。本次没有中断它。以后首次交付使用 `dc40df160330f9058ff0af4e85adac6ed1be8be0b2d54c7fba5f10f71450eaae` 才能利用本方法。CV 的既有 source preflight 同理：796,560-byte `80955…` 应在首次正式交付前使用 796,309-byte `0ec8…` 的冻结 merge 固定点，随后保持任务版本和环境不变。

底层 formal cache 的 30 分钟 TTL 不是上述 run-local cache 的 TTL。底层还绑定 canonical projectRoot hash 和精确 targetCommit，临时 worktree/新 projection commit 会 miss；把 TTL 延长也不能解决这些 miss。任务投影和全部原目标的 statementHash 不同，也不能跨这两种请求直接复用 receipt。assembly→S3 的 root 改变仍要求独立校验，最终原 comparator 必须真实运行。

正式 verifier 每次创建独立 checkout，排除 worker `.lake/build` 并显式编译本地模块。advisory diagnostics cache 不能替代正式 receipt。增加跨验收阶段的 host-private `.olean` 复用，需要另一项有模块闭包、工具链、编译选项和 artifact provenance 的设计；本次没有扩大这层信任边界。
