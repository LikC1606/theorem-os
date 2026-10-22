# 规范化闭图场收缩的紧性

原题 OAI.CartierSections.isCompact_closedChartFieldRetraction_cone 已通过 Lean 内核和原版发布方 comparator 的只读依赖、bwrap 禁网独立验收，exit 0，stderr 为空。原目标、公理白名单和原声明保持。

证明将闭图场收缩展开为忠实形式坐标展开对应的分式域赋值，再应用正式 imports 中的通用紧性引理 isCompact_expandedFractionValuation_cone。Submission 只替换原 sorry；没有 sorry/admit，公理只有 propext、Classical.choice、Quot.sound。

- [Submission.lean](Submission.lean)：精确验收源码；[Challenge.lean](Challenge.lean) 保留原题占位 sorry。
- [support](support)：固定上游 commit 的全部 12 个支撑源码；[support-manifest.json](support-manifest.json) 给出来源、SHA、递归 imports 与审查结果。
- [verification.json](verification.json)、[provenance.json](provenance.json) 和 [manifest.json](manifest.json)：范围、归因和全文件 SHA。
- [内核回执](evidence/kernel-axiom-receipt.json)、[源码守卫回执](evidence/source-guard-receipt.json)、[隔离比较器回执](evidence/sealed-comparator-receipt.json)。

这是外部独立辅助证明，campaignAcceptance=false，不计模型从零解题成绩，也不是 OpenAI 托管验收。C 档为本项目判断；该结果只覆盖手稿 066-02 的支撑结论，不表示完整证明该手稿的全部主张。未读取发布的 ChartCompactness 目标解答。

真实契约边界：原版 runtime-v2 源码守卫接受候选声明和上下文，但在 lakefile/manifest 注册必要的 OAI 支撑 path package 后拒绝 math_trusted_source_changed。没有绕过此检查。本归档的 Lake 配置属于 standalone，不能表述为原生 guard accepted；活动队列需另行授权的环境契约修订。

固定 Lean leanprover/lean4:v4.34.1、Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612、OpenAI math 1581d4cbdd69a0faf34b2089614fe2a814316a6a。普通独立复验在本目录执行：

    export LEAN_NUM_THREADS=1
    lake exe cache get
    lake build Challenge Submission
    lake env lean AxiomAudit.lean

根 Lake 配置以 support 相对路径注册 cartier_support，并由该包导出 OAI 库；未携带 Mathlib 大依赖或任何 olean。隔离历史验收使用相同源码，在 .lake/packages/cartier_support 注册支撑包；本归档只将本地包位置改为可移植 support 路径。该可移植布局已在独立副本中重新构建 12 个支撑模块、Challenge/Submission，并通过 AxiomAudit；见 evidence/portable-lake-recheck-receipt.json。

原比较器的配置仅将 challenge_module/solution_module 改为 Challenge/Submission，目标和许可公理均不改，Nanoda 未启用。[run-sealed-comparator.sh](run-sealed-comparator.sh) 是验收时未改的 publisher_evaluator.py 输出，需预备固定 comparator、可信依赖与 TheoremOS sealed sandbox。离线沙箱的包缓存中需含 cartier_support；在全新独立副本中可先运行 /usr/bin/python3 stage-sealed-support.py，再让宿主封存完整 .lake/packages 后执行该脚本。宿主需将依赖只读挂载并禁网；单独在普通 shell 执行该脚本不构成 sealed 验收。

原题、配置及支撑源保留 [Apache-2.0](LICENSE.openai-math) 许可与 [NOTICE](NOTICE)。归档不含环境配置、provider/lease、7.6G 依赖、编译产物，也未改原生 runtime 或 campaign。
