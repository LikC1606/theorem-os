# 本地验证后获官方验收的四道证明

这里归档 4 道通过本地官方比较器的证明。[LeanEval 提交 #2144](https://github.com/leanprover/lean-eval-submissions/issues/2144) 于 2026 年 10 月 16 日收到官方托管评测结果：4/4 通过。目录名沿用提交时的归档路径，不表示目前仍待验收。

| 题目 | 证明包 | 状态 |
| --- | --- | --- |
| 向日葵引理改进界 | [annals_improved_bounds_sunflower_lemma](annals_improved_bounds_sunflower_lemma/) | [#2144 · pass](https://github.com/leanprover/lean-eval-submissions/issues/2144) |
| Lorentzian 多项式 | [annals_lorentzian_polynomials](annals_lorentzian_polynomials/) | [#2144 · pass](https://github.com/leanprover/lean-eval-submissions/issues/2144) |
| 最优纸带 Möbius 环 | [annals_optimal_moebius](annals_optimal_moebius/) | [#2144 · pass](https://github.com/leanprover/lean-eval-submissions/issues/2144) |
| 代数整数 | [annals_algebraic_integers](annals_algebraic_integers/) | [#2144 · pass](https://github.com/leanprover/lean-eval-submissions/issues/2144) |

所有证明包均逐字节保留自公开提交 [`43cffcc2851efebefd9609abee0c537c64bd9dbf`](https://github.com/LikC1606/deepscientist-math-proofs/tree/43cffcc2851efebefd9609abee0c537c64bd9dbf)，包括 `Submission.lean`、辅助证明、Lean 工具链、依赖锁定文件及原始 `verification.json`。[submitted.json](submitted.json) 记录各题来源、提交链接、全部归档文件的 SHA-256 和原有本地验证摘要。

原始记录中的 `official_verified` 表示本地运行官方比较器所得的验证回执，不能替代独立的官方托管验收。`submitted.json` 的 `local_verified_pending_official` 是提交准备时的状态快照，当前验收结果以 #2144 的官方回复为准。证明来自既有求解任务的继续运行，不能据此推算当前版本从零求解的成功率。
