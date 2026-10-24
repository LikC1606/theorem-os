# CharacterVarieties 全部 seam 方程

完整原题 `CharacterVarietiesAllSeamsSupport` 已通过固定 Lean 内核的模块化验证。对应手稿 `027-01`，本项目评为 C 档；OpenAI 未提供 S–D 标签。

精确目标是 `OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.producedMarkedValues_allSeams`。证明覆盖原题的全部八种 seam 分支，最终定理没有增加前提，公理仅有 `propext`、`Classical.choice` 和 `Quot.sound`。

最新[加速版完整单文件](../native-check-hotspot-20261024/character-sync-def-v2-candidate/Submission.lean)在 635.03 秒内整份编译成功，原目标公理审计通过；复用真实编译产物的独立原比较器在 41.15 秒内通过，包含完整 Lean 内核回放。166 个新增辅助声明改用 `def`，其名称、显式类型、证明体与原题保持不变；另外两项保留 `theorem`。冻结源码守卫和合并固定点检查通过，见[全部证据](../native-check-hotspot-20261024/README.md)。加速版已完成原生环境准备、正常队列递送与源码提交，独立宿主正在编译同 SHA 候选的依赖模块；见[递送核查](../native-check-hotspot-20261024/native-sync-def-attempt/delivery-observation.md)。TheoremOS 原生最终验收尚待回执，没有 OpenAI 托管验收记录。

早期 [V12 单文件候选](candidates/v12/GuardCompatibleAllSeamsV12.lean)保留原题上下文，已通过[原源码保护](candidates/v12/source-guard.json)；180 个辅助声明的默认 CLI 检查自然 exit 0、零报错，耗时约 6 小时 37 分钟，见[回执](candidates/v12/remaining180-receipt.json)与[终态摘要](candidates/v12/remaining180-summary.json)。该完整单文件长检查仍保留。

早期合并版本曾因新增模块作用域被源码保护以 math_original_context_changed 拒绝；该历史状态保留在 [verification.json](verification.json)及下述拒绝回执中，不代表当前 V12 的源码保护结果。

## 文件与证据

- [原题](Challenge.lean) 保留官方完整声明及原始 `sorry`，仅作身份对照，不参与证明依赖。
- [完整证明入口](AllSeamsAssemblyInferredV2.lean) 依赖 66 个已验证的本地证明模块；[编译回执](evidence/AllSeamsAssemblyInferredV2.build-receipt.json) 记录 exit 0、源码 SHA 和 17.736 秒耗时。
- [原定理签名与公理输出](evidence/AllSeamsAssemblyInferredV2.build.log) 记录完整原题内核结果。
- `OAI/` 收录原 import 的 57 个固定公开依赖，来源与 SHA 见 [公开依赖清单](public-support-manifest.json)。未包含发布方解答模块 `ProducedSolution`。
- [证明模块清单](evidence/local-proof-manifest.json) 记录每个源码、成功回执和导出对象的 SHA；[文件清单](manifest.json) 覆盖本包实际归档文件。
- [源码保护拒绝回执](evidence/source-guard-b112a1db4a01-receipt.json) 对应 [待重排的合并源码](rejected-single-file/AllSeamsArchiveFinalInferredV2.lean)。该版本未进入原生交付队列，不是可验收的提交文件。

## 复现

需要 Lean `v4.34.1` 与 Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`。准备固定 Lake 依赖及缓存后运行：

```sh
lake exe cache get
python3 verify-kernel.py
```

脚本先核对归档 SHA，再依次重建 57 个公开依赖和 66 个证明模块，最后检查原题公理清单。它不设时间上限；完整重建可能耗时较长。生成的日志和回执位于 `.build/`。

本证明包含外部辅助构造和协作验证，不能计为配置模型独立从零解出。完整归因、固定版本及五项零预算设置见 [provenance.json](provenance.json)。
