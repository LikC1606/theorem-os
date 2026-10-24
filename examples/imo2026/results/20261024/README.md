# IMO2026 六题证明与验收摘要

TheoremOS 使用 `gpt-5.6-sol`、`xhigh`、每题 4 个 worker，完成 Q1–Q6 的 **6/6 道题、15/15 个原始目标**。与其他公开方法的逐题比较见 [结果对比](../../RESULTS.md)。

| 题目 | 原始目标 | 确认成功 API 区间并集 | 证明 | 验收摘要 |
| --- | ---: | ---: | --- | --- |
| Q1 | 5/5 | 17分41秒 | [Submission.lean](Q1/Submission.lean) | [verification.json](Q1/verification.json) |
| Q2 | 1/1 | 1小时12分15秒 | [Submission.lean](Q2/Submission.lean) | [verification.json](Q2/verification.json) |
| Q3 | 6/6 | 1小时54分00秒 | [Submission.lean](Q3/Submission.lean) | [verification.json](Q3/verification.json) |
| Q4 | 1/1 | 13分01秒 | [Submission.lean](Q4/Submission.lean) | [verification.json](Q4/verification.json) |
| Q5 | 1/1 | 19分15秒 | [Submission.lean](Q5/Submission.lean) | [verification.json](Q5/verification.json) |
| Q6 | 1/1 | 49分21秒 | [Submission.lean](Q6/Submission.lean) | [verification.json](Q6/verification.json) |

所选成功链的计时合计 **4小时45分33秒**，共 2680 次客户端确认成功的响应。每题对这些请求的时间区间取并集，合并并发重叠，再将六题相加；包含正常首 token 等待，排除工具、Lean、环境准备、修复等待、重试退避及失败或未确认响应。它不是全部请求时长之和，也不是运行墙钟时间。

Q2 计入 fresh 运行及保留成果的续跑，Q3 计入同一运行升级前后；另行放弃的历史尝试未计入。部分运行经过系统修复，因此这份成功合集不能用于估计一次运行成功率，也不能作为与其他方法等预算的速度实验。

每个目录保留冻结的 `Submission.lean`、源题面 `problem.lean`、Lean/Mathlib 依赖配置，以及 `verification.json` 和 `timing.json`。后两者是已有本地验收及计时记录的精简摘录，保留原记录 SHA-256；本次发布没有重新调用模型或重跑 Lean。未发布会话、认证配置和逐请求标识。

所有证明文件 SHA-256 均与相应最终回执中的 `proofHash` 一致；15 个目标的 `sorryCount`、`admitCount`、`goalsRemaining` 均为 0，依赖公理仅有 `propext`、`Classical.choice`、`Quot.sound`。验收方法为 `host-lean-kernel-all-targets`，`official: false`，属于本地独立验收。

题面来自 [humanfia/imo2026 的固定提交](https://github.com/humanfia/imo2026/tree/834c01f2ecac89b648759b1c95bc6180b0ede149/base/IMO2026)，上游形式化来自 [AxiomMath/IMO2026](https://github.com/AxiomMath/IMO2026)。`problem.lean` 中的 `sorry` 是原题占位；完整证明位于 `Submission.lean`。题面、声明与来源归属保留，TheoremOS 的运行结果及新增证明在此归档。

六题均使用 `leanprover/lean4:v4.31.0`，Mathlib 固定到 `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`。安装 elan 并取得依赖后，可以在各题目录独立复验，例如：

```bash
cd Q1
lake exe cache get
lake env lean Submission.lean
```

[manifest.json](manifest.json) 记录题面与证明哈希、最终运行及提交、全部目标名和精确微秒计时。[SHA256SUMS](SHA256SUMS) 覆盖本目录发布文件，可在本目录执行 `sha256sum -c SHA256SUMS` 检查完整性。
