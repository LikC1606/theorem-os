# OpenAI math 求解成果

按 D → C → B → A → S 推进；分档是本项目判断，不是 OpenAI 官方标签。

| 题目 | 档位 | 手稿 | 本地验证 | 官方托管验收 |
| --- | --- | --- | --- | --- |
| [Truffet 有限反例](truffet_counterexample/README.md) | D | 104-03 | Lean、原比较器、TheoremOS 原生 evaluated_passed | 尚无确认 |
| [三维完备局部复代数](surface_cone_candidate_support/README.md) | D | 195-01 | 完整原题；Lean 与隔离原比较器通过；原生最终审查进行中 | 尚无确认 |
| [Hadamard 三次纤维消去](hadamard_cube_fiber/README.md) | C | 266-02 | Lean、源码保护、隔离原比较器通过；原生队列待运行 | 尚无确认 |

归档 3 个证明，其中 1 个原生最终通过。保留源码、固定依赖、身份、SHA 和归因；不计入根目录 6 个 LeanEval 官方记录。第二题与 Hadamard 题含外部证明辅助。
