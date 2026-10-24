固定 trusted Lean 支持模块产物复用已在独立 runtime 完成，当前状态为 **已验证、未激活**。基线是 `../exact-source-integration-reuse-20261024/runtime`；本目录的 `runtime` 是独立文件副本。可审阅修改见 `changes.patch`，精确交付文件见 `delivery-files.json`，校验和见 `SHA256SUMS`。

`src/math/fixedLeanDependencies.ts` 只接收宿主冻结的支持源码哈希。`evidence.ts` 的两个正式检查入口排除全部 solver-owned 文件；`verifier.ts` 另排除本次请求中的所有 proof 文件。支持模块必须形成完整、顺序一致的本地依赖闭包，闭包中出现非 trusted 源即回退原完整编译。仅支持冻结 TOML Lake 配置、已验证 sealed 包和已识别的实际 Lean/Lake；可变 `LEAN_PATH`/`LEAN_SYSROOT` 与自定义 verifier 不使用本优化。

冷缓存先在独立依赖沙箱中仅编译固定支持源，沙箱没有 Submission。宿主在目标运行前复核 builder 和原检查项目的源码、配置、实际工具与 sealed 包身份，再保存 `.olean`、`.olean.private`、`.olean.server`、`.ir`、`.ir.sig` 的字节与完整存在性。热缓存逐文件校验后恢复独立副本，目标不能回写缓存。配置、工具、包、支持源或有效环境变化会 miss 或回退；恢复后身份变化会清除已恢复产物。缓存仅本进程存活，最多保留512 MiB产物，退出清理，不加载任何跨进程缓存元数据。

每次仍重新编译当前目标、运行原声明/公理查询，并产生新的 Lean receipt；TaskProofCache 与 receipt 复用规则未改。支持编译的成功输出通过现有 diagnostic 事件独立记录，目标 ProcessResult 的全流 hash 和输出保持一致。真实支持编译失败沿用原失败结果；可选缓存异常回退完整编译。独立 publisher comparator 继续原来的构建与比较路径，本优化不加速它。

同时包含根代理完成的 `src/solver/modules/context.ts`：固定 reviewer 先看同 commit、同 sourceDigest 且完整匹配原目标的现成 host receipt，再审源码和题意；有具体疑点时仍可定向检查。紧凑证据为 mandatory advisory context，标明 recorded-not-replayed，不赋予验收权限。与之对应的7个实际上下文行为案例在最终测试内。

最终验证为11个聚焦测试文件 **261 passed、0 failed**，真实 sealed Lean fixture另 **1 passed**，typecheck成功，headless三 bundle 构建成功。`build-verification.json` 来自实际调用 `readMathBuildManifest`，包含211个源输入和三份产物校验；manifest权限0400。历史提示版97项、最终上下文104项均保留原记录，104项已包含在261项内，不重复累计。测试入口统一使用 Node；历史 runner/fixture 失败与修正见 `resolved-attempts.json`。

真实 fixture 使用 leanprover/lean4:v4.34.1、一个真正编译的外部toy包和两个不同project根。每次proof源和commit变化，目标日志标记与新receipt确认 **7次目标真实重编**。前3次共编支持1次；第3次坏目标仍失败。之后固定支持、配置原字节、sealed包分别变化并重新冷编，最后包含未知 Owned 依赖时回退原路径。总计4次专用支持编译，不含最后一次回退路径中的完整依赖编译。

| 场景 | 总耗时(秒) | 专用支持编译累计 | 本次目标编译 | 结果 |
| --- | ---: | ---: | ---: | --- |
| COLD | 2.405 | 1 | 1 | kernel_verified |
| OTHER_PROJECT | 1.592 | 1 | 1 | kernel_verified |
| BAD_TARGET | 0.839 | 1 | 1 | failed |
| NEW_SUPPORT | 2.271 | 2 | 1 | kernel_verified |
| NEW_CONFIG | 2.346 | 3 | 1 | kernel_verified |
| NEW_PACKAGES | 2.302 | 4 | 1 | kernel_verified |
| OWNED_DEPENDENCY | 1.877 | 4 | 1 | kernel_verified |

小型fixture证明机制与边界，不代表57模块实题的提速比例。没有模型调用或大型实题重编，也未改活动runtime、旧缓存、状态、历史receipt、publisher comparator或全局依赖。

构建ID为 `46551899-4922-4905-b81e-0ff4503842e6`；solver SHA256为 `35d2651ecdec66902d30ff979f936e4cc37b1ac351771d05e9eeefd1ffadbebf`。最终context源码SHA256为 `bdf6be3d90edd7a63ef1e36cbb38ab03adb849f5476e714e1414845e82ed44c5`。

`source-isolation.json` 核对冻结基线1309文件，0变化；新源码/测试/依赖6226普通文件，0共享inode、0符号链接、0多链接。四产品文件之外，仅指定四个测试文件和构建产物变化（`search-lean.js`重建后字节相同）。没有额外新增、删除或未声明差异。

交付只列出四产品源码、四测试、patch、报告、三bundle及其唯一构建manifest；不将完整runtime、node_modules、fixture缓存或其他build目录打包。

根代理独立静态复审未发现具体回归：[复审记录](../fixed-support-reuse-independent-review-20261024.json)。该报告由根代理单独归档，不复制进本交付。
