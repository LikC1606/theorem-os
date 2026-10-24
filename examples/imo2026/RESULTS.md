# IMO2026 逐题公开结果对比

截至 2026-10-24，TheoremOS 已完成 Q1–Q6 的 6/6 道题、15/15 个原始目标。下表逐题整理本方记录与可查到的第一方公开结果；其它方的通过均为作者报告，本次未重新编译其证明。

所有用时单位均为分钟，按原始记录分别换算并保留两位小数。✓ 表示本方最终验收或外部作者报告通过；单位统一后，各方计时口径仍有差异，不是统一预算下的速度排名。

总用时优先采用原报告总计；本方使用原始精确记录，AxiomProver按逐题记录相加。各项独立取整，总计可能与显示值之和略有差异；≈ 表示作者给出的近似总计。MIDAS 1.1 仅计已解的 3 题。

## 相同形式化题面

本方题面固定在 humanfia/imo2026@834c01f2ecac89b648759b1c95bc6180b0ede149。Humanfia、AxiomProver、Hardy Appendix、Dirac 的六份题面均与其逐字节一致；EonMath 仅多一行来源注释。以下主表对齐同一形式化题面。

| 方法 | Q1 | Q2 | Q3 | Q4 | Q5 | Q6 | 总用时（分钟） | 通过题数 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| [TheoremOS + GPT-5.6](https://github.com/LikC1606/theorem-os/tree/main/examples/imo2026/results/20261024) | ✓ 17.68 | ✓ 72.26 | ✓ 114.00 | ✓ 13.01 | ✓ 19.25 | ✓ 49.36 | 285.55 | 6/6 |
| [Humanfia + GPT-5.6](https://github.com/humanfia/hoa-qed/blob/1c918ec9a96c7751ce9c283304e1aebd7ffb19a3/imo2026/README.md) | ✓ 38.10 | ✓ 100.40 | ✓ 187.10 | ✓ 58.70 | ✓ 46.50 | ✓ 66.90 | 497.70 | 6/6 |
| [Humanfia + Kimi-K3 / Codex](https://github.com/humanfia/hoa-qed/blob/1c918ec9a96c7751ce9c283304e1aebd7ffb19a3/imo2026/README.md) | ✓ 87.10 | ✓ 224.30 | ✓ 343.70 | ✓ 75.60 | ✓ 91.90 | ✓ 212.40 | 1034.90 | 6/6 |
| [AxiomProver](https://github.com/AxiomMath/IMO2026/blob/c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2/README.md) | ✓ 24.00 | ✓ 360.00 | ✓ 869.00 | ✓ 39.00 | ✓ 65.00 | ✓ 139.00 | 1496.00 | 6/6 |
| [Hardy（AxiomMath Appendix轨）](https://github.com/pramaana-labs/imo2026-lean/blob/788fddc53c463d5d40d4680fb9bfd7b0f96f1063/README.md) | ✓ 20.43 | ✓ 173.00 | ✓ 184.00 | ✓ 16.33 | ✓ 31.15 | ✓ 112.00 | ≈537.00 | 6/6 |
| [Dirac](https://github.com/Boundless-Intuition/IMO2026/blob/37259237016275044e3905e8d537efd0eead74d2/README.md) | ✓ 29.08 | ✓ 80.30 | ✓ 130.47 | ✓ 15.98 | ✓ 18.18 | ✓ 164.08 | 438.10 | 6/6 |
| [EonMath（文本+形式证明）](https://github.com/MechMath/IMO2026/blob/47ff510110dd400c98aee2ead3be0f53f7b8ba04/README.md) | ✓ 74.13 | ✓ 244.58 | ✓ 305.80 | ✓ 60.58 | ✓ 141.65 | ✓ 351.68 | 1178.43 | 6/6 |

## 如何理解结果与用时

- **TheoremOS**：gpt-5.6-sol、xhigh、每题4 workers。本地独立 Lean 内核验收为 official: false；所有15个目标均无 sorry/admit/剩余目标。表内是所选成功链的确认成功API区间并集，合计285.55分钟；Q2含fresh与续跑，Q3含同一run升级前后。系统修复、工具/Lean等待、失败/未确认响应及另行放弃的历史尝试未计入，不能据此估计一次运行成功率。

- **Humanfia**：GPT-5.6与Kimi-K3两行均为作者称的API time consumption；未说明并发区间取并集还是各会话求和。Kimi采用K3 worker与Codex reviewer的混合方案；reviewer默认gpt-5.5/xhigh，但成功运行的实际配置未单独公开。GPT脚本为gpt-5.6-sol/max，与本方xhigh也不同。两组均公开六份Lean证明和验证脚本。

- **AxiomProver**：作者公开六份Lean证明，README列出六题AXLE okay=True并称已通过本地Comparator验证；所报分钟未定义为API、墙钟或并行累计时间。

- **Hardy**：使用Pramaana Labs报告附录中的AxiomMath题面轨；作者称所有证明经Lean和Comparator检查。不要混入其另一条Panini自形式化端到端轨的时间或成本。表内为附录runtime，作者总计约537.00分钟。

- **Dirac**：Boundless Intuition作者报告同一AxiomMath题面上的六份machine-checked Lean证明，并提供Comparator复验说明；所报runtime合计438.10分钟。

- **EonMath**：仓库名为MechMath。主表采用作者的自然语言证明与形式证明总时间；若只取形式证明部分，Q1–Q6为28.30、147.25、160.33、18.85、24.47、24.07分钟。作者公开源码，声明无sorry/admit且只依赖三种标准公理；这两种时间都不能直接等同本方API区间并集。

这些报告没有统一模型、并行度、预算、重试及历史尝试范围；表中不计算加速倍数，不声称协作策略优于其它方法。其它方的源码公开与作者验收声明，不等于本次进行了独立复验。

## 其它形式化与历史报告

下表涉及不同或尚未核验等价的形式化，不能视作本项目原始15目标的验收结果。MIDAS 1.1是1.2报告中的历史对照，未解出的三题没有披露失败预算；math-ai-org逐题仅标记Proved，具体模型、时间与预算未披露。未披露不记作失败。

| 方法 | Q1 | Q2 | Q3 | Q4 | Q5 | Q6 | 总用时（分钟） | 通过题数 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| [MIDAS 1.2（不同形式化）](https://github.com/midas-intelligence/IMO2026/blob/b476065a0a88a56ef8bb98e7ae5a9b33d6d12fd9/README.md) | ✓ 35.00 | ✓ 141.00 | ✓ 238.00 | ✓ 35.00 | ✓ 53.00 | ✓ 88.00 | 590.00 | 6/6 |
| [MIDAS 1.1（历史对照）](https://github.com/midas-intelligence/IMO2026/blob/b476065a0a88a56ef8bb98e7ae5a9b33d6d12fd9/README.md) | ✓ 154.00 | 未解出 | 未解出 | ✓ 84.00 | ✓ 431.00 | 未解出 | 669.00（仅3题） | 3/6 |
| [math-ai-org（方法未注明）](https://github.com/math-ai-org/IMO2026/blob/a8912f36ed4f0a658bf5cc640daf8b1f88a50f48/README.md) | Proved / 未披露用时 | Proved / 未披露用时 | Proved / 未披露用时 | Proved / 未披露用时 | Proved / 未披露用时 | Proved / 未披露用时 | 未披露 | 6/6 |

另外发现 dots-IMO2026 和 claude-opus-5-imo2026 的公开解答文件；定点读取的内容为自然语言证明，未取得逐题形式化验收或独立判分证据，因此未填成Lean通过成绩。本次为有界公开检索，未收录不代表没有结果。

## 证明与来源

本方完整证明、冻结题面、依赖、验收与计时摘要见[六题归档](results/20261024/README.md)。验收摘要从已有回执精简提取；证明哈希与原回执一致，本次整理没有重跑模型或Lean。机器可读数据见[comparison.json](results/comparison.json)。

所有外部方法名称均链接到已读取的固定提交README，避免后续更新改变引用。题面对齐仅检查公开题面文件；通过状态按各自证据类型记录。以下保留自然语言材料入口，便于后续补充独立评分：

- [studio-dots-ai/dots-IMO2026](https://github.com/studio-dots-ai/dots-IMO2026/blob/710efb9fb6b33c350e1be37ac2d3a3509a4fe7b7/Problem1.pdf)：尚缺可比较的逐题形式化验收。
- [changjonathanc/claude-opus-5-imo2026](https://github.com/changjonathanc/claude-opus-5-imo2026/blob/fbd6061c248eb62698246cb4d89b7ee3ce8709c7/p1.txt)：尚缺可比较的逐题形式化验收。
