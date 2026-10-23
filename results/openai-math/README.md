# OpenAI math 求解成果

按 D → C → B → A → S 推进；分档是本项目判断，不是 OpenAI 官方标签。

| 题目 | 档位 | 手稿 | 本地验证 | 官方托管验收 |
| --- | --- | --- | --- | --- |
| [Truffet 有限反例](truffet_counterexample/README.md) | D | 104-03 | Lean、原比较器、TheoremOS 原生 evaluated_passed | 尚无确认 |
| [三维完备局部复代数](surface_cone_candidate_support/README.md) | D | 195-01 | 完整原题；Lean、隔离原比较器、TheoremOS 原生 evaluated_passed | 尚无确认 |
| [Hadamard 三次纤维消去](hadamard_cube_fiber/README.md) | C | 266-02 | Lean、源码保护、隔离原比较器、TheoremOS 原生 evaluated_passed | 尚无确认 |
| [Cartier 图域回缩的紧致性](cartier_chart_compactness_support/README.md) | C | 066-02 | Lean、隔离原比较器、新受保护环境原生 evaluated_passed | 尚无确认 |

归档 7 个完整原题证明：4 个原生最终通过。SnakyCertificate 的 V5 已通过完整单文件、原比较器、正常原生目标、集成和全部原目标检查，正在固定版本复审；SnakyConditional 的 V6 已通过完整单文件构建和原比较器，正在同源宿主检查；CharacterVarieties V12 已通过源码保护，正在复验 180 个辅助声明。这三题仍待原生最终验收（Cartier 为独立新环境补跑；主 campaign 保留历史阻断）。保留源码、固定依赖、身份、SHA 和归因；不计入根目录 6 个 LeanEval 官方记录。新增证明含外部辅助，归因见各成果包。

## 新增完整内核证明

| 题目 | 档位 | 手稿 | 已完成 | 待完成 |
| --- | --- | --- | --- | --- |
| [Snaky 616 行证书](snaky_certificate/README.md) | C | 187-01 | 完整七合取；单文件、源码保护、原比较器、正常原生目标、集成和全部原目标检查通过 | 固定版本复审、原生最终验收 |
| [Snaky 普通 35 步必胜策略](snaky_conditional/README.md) | C | 187-01 | 完整合法策略与棋子数；V6 单文件构建和原比较器通过 | 同源宿主公理检查、原生验收 |
| [CharacterVarieties 全部 seam 方程](character_varieties_all_seams_support/README.md) | C | 027-01 | 完整原题与全部八分支；固定内核通过，仅标准三公理 | 单文件重检、隔离原比较器、原生验收 |

这三项为外部辅助完成的本地内核证明，尚无 OpenAI 托管验收确认。

[2026-10-24 阶段进度与回执](verification-progress-20261024/README.md)：原生最终通过总数仍为 4；阶段通过不计入最终通过数。

[验收可靠性修复与验证回执](validation-reliability-20261023/README.md)：长载荷递送、首错摘要和宿主检查修复已通过 344 项测试；补丁归档，数学通过数不变。
