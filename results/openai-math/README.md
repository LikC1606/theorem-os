# OpenAI math 求解成果

按 D → C → B → A → S 推进；分档是本项目判断，不是 OpenAI 官方标签。

| 题目 | 档位 | 手稿 | 本地验证 | 官方托管验收 |
| --- | --- | --- | --- | --- |
| [Truffet 有限反例](truffet_counterexample/README.md) | D | 104-03 | Lean、原比较器、TheoremOS 原生 evaluated_passed | 尚无确认 |
| [三维完备局部复代数](surface_cone_candidate_support/README.md) | D | 195-01 | 完整原题；Lean、隔离原比较器、TheoremOS 原生 evaluated_passed | 尚无确认 |
| [Hadamard 三次纤维消去](hadamard_cube_fiber/README.md) | C | 266-02 | Lean、源码保护、隔离原比较器、TheoremOS 原生 evaluated_passed | 尚无确认 |
| [Cartier 图域回缩的紧致性](cartier_chart_compactness_support/README.md) | C | 066-02 | Lean、隔离原比较器、新受保护环境原生 evaluated_passed | 尚无确认 |

归档 6 个完整原题证明：4 个原生最终通过，2 个新 Snaky 证明通过模块化 Lean 内核、仍待隔离原比较器与原生验收（Cartier 为独立新环境补跑；主 campaign 保留历史阻断）。保留源码、固定依赖、身份、SHA 和归因；不计入根目录 6 个 LeanEval 官方记录。新增证明含外部辅助，归因见各成果包。

## 新增完整内核证明

| 题目 | 档位 | 手稿 | 已完成 | 待完成 |
| --- | --- | --- | --- | --- |
| [Snaky 616 行证书](snaky_certificate/README.md) | C | 187-01 | 完整七合取；616 行与标准公理内核核查 | 单文件提交、隔离原比较器、原生验收 |
| [Snaky 普通 35 步必胜策略](snaky_conditional/README.md) | C | 187-01 | 完整合法策略与棋子数；无 sorry 依赖链，标准公理 | 单文件提交、隔离原比较器、原生验收 |

新增两项为外部辅助完成的本地内核证明，尚无 OpenAI 托管验收确认。
