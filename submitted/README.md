# 已通过本地验证、等待官方复验的证明

这里归档 4 道已经通过本地官方比较器的证明。它们已通过 [LeanEval 提交 #2144](https://github.com/leanprover/lean-eval-submissions/issues/2144) 送交官方复验；归档时尚未确认官方验收结果，不计入 [官方已通过题目](../accepted/)。最新进度见 [官方验证工作流](https://github.com/leanprover/lean-eval-submissions/actions/runs/38944065438)。

| 题目 | 证明包 | 状态 |
| --- | --- | --- |
| 向日葵引理改进界 | [annals_improved_bounds_sunflower_lemma](annals_improved_bounds_sunflower_lemma/) | 本地通过，官方待确认 |
| Lorentzian 多项式 | [annals_lorentzian_polynomials](annals_lorentzian_polynomials/) | 本地通过，官方待确认 |
| 最优 Möbius | [annals_optimal_moebius](annals_optimal_moebius/) | 本地通过，官方待确认 |
| 代数整数 | [annals_algebraic_integers](annals_algebraic_integers/) | 本地通过，官方待确认 |

所有证明包均逐字节保留自公开提交 [`43cffcc2851efebefd9609abee0c537c64bd9dbf`](https://github.com/LikC1606/deepscientist-math-proofs/tree/43cffcc2851efebefd9609abee0c537c64bd9dbf)，包括 `Submission.lean`、辅助证明、Lean 工具链、依赖锁定文件及原始 `verification.json`。[submitted.json](submitted.json) 记录各题来源、提交链接、全部归档文件的 SHA-256 和原有本地验证摘要。

原始记录中的 `official_verified` 表示本地运行官方比较器所得的验证回执，不能替代独立的官方托管验收。证据摘要保留的是提交准备时的检查结果；本目录状态为 `local_verified_pending_official`。证明来自既有求解任务的继续运行，不能据此推算当前版本从零求解的成功率。
