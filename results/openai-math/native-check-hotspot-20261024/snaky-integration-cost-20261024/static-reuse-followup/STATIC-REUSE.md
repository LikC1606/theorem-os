Snaky V8：一个有限证书复用候选（静态归档）

已识别一个具体重复核验：`qescapestep_11` 可通过坐标替换直接引用已有的 `qsmall_step11`。已生成仅替换这一个声明的 [candidate.patch](candidate.patch) 和 [完整替换片段](qescapestep_11.replacement.lean.txt)。补丁未应用、未运行 Lean、未测得提速，不能替代整题检查。

证据固定在集成源码 SHA-256 `dc40df160330f9058ff0af4e85adac6ed1be8be0b2d54c7fba5f10f71450eaae`，967683 字节。已知临时工作目录在收尾时被清理，遂改用原身份回执指定的 [持久归档](/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/snaky-ordinary-bridge-20261023/SnakyConditionalCanonicalV8IntegrationMerged.lean:14746)，重新确认其字节哈希完全相同。与本候选相关的原文及行号另存于 [source-excerpts.txt](source-excerpts.txt)。

718 处 `decide +kernel` 是源码位置数。静态归属如下；带 `<;>` 的一处调用可作用于多个子目标，不能将该计数当成运行调用次数或时间占比。

| 源码位置 | 数量 | 有限证书依赖 |
|---|---:|---|
| `qtable_valid_probe` | 2 | `qtable` 的长度及全部条目的索引、非空和子节点界限 |
| `qmeq_0` 至 `qmeq_614` | 615 | 单行输出与显式 `qm` 的等式，引用已证明的子行等式 |
| `qn...` | 12 | 显式坐标清单的 `Nodup` |
| 几何界限、集合规范化及开局衔接 | 89 | 有限坐标清单、局部成员关系和已有行数据 |

`qtable` 包含 `qv6` 至 `qv615` 共 610 个条目。`qTableValid` 在 3015–3020 行定义，`qtable_valid_probe` 在 3091–3104 行证明一次；15214–15256 行的 15 个根行引用该引理。此次未识别到重复执行整张表合法性核验的源码位置。全部 718 处的声明归属和词法引用见 [site-inventory.json](site-inventory.json)；它不是经过展开器或内核确认的动态依赖图。

本轮只评估下述一个候选：

- 已有 `lemma qsmall_step11` 在 14206–14209 行证明：对 `a ∈ qsmall10`，若 `a` 位于 `qplaceRow ⟨614,1,4,3⟩ qm614` 的包络中，则 `a ∈ qsmall11`。
- `qescapestep_11` 在 14746–14749 行重新用 `decide +kernel` 证明另一个坐标系中的同一有限条件。`qo614` 在 14567–14570 行直接定义为 `qm614`，两者引用同一个包络数据。
- 令 `a = (b.y + 1, -b.x)`，即 `b = T(a) = (-a.y, a.x - 1)`。`T` 把 `qsmall10` 精确映为 `qescapeI_10`，把 `qsmall11` 精确映为 `qescapeI_11`。

两个成员关系的逆变换为：

```text
旧： (qplacementEquiv 1 (0,-1)).symm a = (a.y + 1, a.x)
新： (qplacementEquiv 4 (1,-1)).symm b = (1 - b.x, b.y + 1)
```

代入 `a` 后，两者相等。三个候选输入的身份可逐项核对：

| 新域中的 b | 旧域中的 a | 两者对应的 qm614.H 输入 | 结论中的有限集合是否包含该点 |
|---|---|---|---|
| `(0,-2)` | `(-1,0)` | `(1,-1)` | 两者均不包含 |
| `(0,-1)` | `(0,0)` | `(1,0)` | 两者均包含 |
| `(0,0)` | `(1,0)` | `(1,1)` | 两者均包含 |

这里仅说明候选成员关系输入相同，没有断言三个查询都会在实际可判定程序中执行。Python 仅核对了这些整数坐标和有限域映射，没有计算 `qm614.H`；见 [finite-input-identity.json](finite-input-identity.json)。

补丁保留 `qescapestep_11` 的声明名、命题、局部 heartbeat 与递归深度选项。新证明用线性整数运算转换有限域，使用已有的 `qmem_moveRow_H_iff` 转换成员关系，再调用不透明的 `qsmall_step11`；不再请求 `decide +kernel` 重新证明此项。源码位置数由 718 减至 717。原文件的其他字节和最终主定理整个块均保持原样；这只是静态 diff 的性质，尚无新候选内核通过回执。

后续独立正式验证仍需确认：固定 Lean/Mathlib 环境能展开此证明中的等价逆映射；内核接受替换后的同一命题且无新增假设或公理；完整合并目标、声明查询、review 和 publisher 各项检查通过。提速须单独测量。当前热线程所处的具体声明仍未知，不能将这个候选归为当前采样成本的已证实原因。

本轮只写入本独立目录，未附加或采样进程、未启动 Lean、未改活动候选或运行时/cache，未更改既有诊断回执，未提交 Git。机器可读结论见 [candidate-assessment.json](candidate-assessment.json)。
