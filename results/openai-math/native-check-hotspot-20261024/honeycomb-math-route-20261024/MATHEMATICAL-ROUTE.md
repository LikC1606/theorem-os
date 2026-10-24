一个可缩小证明接口的路线是：先证明每个固定宽度的临界桥**总质量**在所有有限矩形中有统一的有限上界，再用条带的精确有限状态模型，把零阶总质量提升为一阶长度矩。这能利用现有已验收归约，省去为每个宽度显式构造计数底数 β_h 的要求。它仍有两个实质待证项：有限矩形质量上界，以及完整、精确的有限状态编码；本次没有得到新的 Lean 证明或原题验收。

本次只读了原题定义、父任务指定为已验收的归约源码，以及获准读取的 RESEARCH.md。未读发布方 ProducedSolution、模型隐藏推理，也没有运行 Lean、修改活动源码、runtime、checkpoint 或队列。研究采用 local_only 范围；下面的数学推导标为 I，源码直接支持的事实标为 E，尚未建立的接口标为 ?。

E：当前已验收归约实际已经足够直接使用一阶矩。源码的 [bridgeFiniteBridgeSums_of_firstLengthWeight](/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/honeycomb-scheduling-observation/followup-20261024T0747Z/sums-reduction-proof-21c88246de18.lean:171) 接受

```lean
(∀ h : ℕ, 1 ≤ h → Summable (firstLengthWeight (h := h))) → FiniteBridgeSums
```

归约用 `weight ≤ firstLengthWeight`、`Summable.subtype` 与 `Summable.div_const` 得到其余五项，不需要分析 log corridor 或证明分母非零。严格增长率只是该源码另一个充分条件，见 [finite_bridge_sums_of_stripGrowthBelowMu](/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/honeycomb-scheduling-observation/followup-20261024T0747Z/sums-reduction-proof-21c88246de18.lean:183)。因此新路线可直接对接已存在的一阶矩 helper。原目标在该归档源码中仍是待证的 `sorry`，见 [原目标](/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/honeycomb-scheduling-observation/followup-20261024T0747Z/sums-reduction-proof-21c88246de18.lean:194)。父任务负责现有集成 commit 的状态，本报告不重新审计验收。

I：原图可精确改写成周期为二的砖墙条带。令

\[
c(\operatorname{up}(i,j))=2i+j,\qquad
c(\operatorname{down}(i,j))=2i+j+1.
\]

对于每个整数 c 和层号 0≤j<h，恰有一个顶点：c−j 偶数时为 up，奇数时为 down。原 [adjacent 与 BridgePath 定义](/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/tasks/HoneycombBridgeFiniteness/workspace/generated/problem/Challenge.lean:18) 逐项代入给出：

- 水平边连接 (c,j) 与 (c±1,j)。
- 向上的竖边连接 (c,j) 与 (c,j+1)，恰在 c−j 为奇数时存在。
- 每个切口 c+1/2 只有 h 条可能的水平边。
- 两列切片 c=2k、2k+1 恰有 2h 个顶点，图在 k 上平移不变。

这些坐标结论可直接从三个邻接分支验证。已有 [RESEARCH 的坐标与邻接声明](/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/tasks/HoneycombBridgeFiniteness/attempts/workflow-20261024/result.json.runtime/worktree-3/RESEARCH.md:263) 提供相同结构的线索；其早先“已编译”陈述在本任务中仅按 advisory 看待，未重验。

I：若一条桥的非空占用切片共有 k 个，那么它们是一个连续整数区间，且

\[
1\le |p.\mathrm{vertices}|\le 2hk.
\]

连续性来自每一步 c 的变化只可能是 0、±1；上界来自 Nodup 和每片仅 2h 个顶点。这是**顶点数**，与原题 `criticalActivity ^ p.vertices.length` 的幂次完全一致。原题不是以边数作为幂次，也不是仅以横向跨度作为幂次。

?：需要构造精确的有限转移模型，不能只记录经过切口的次数。建议一片处理两列，状态保留切口上活动端口的连通分划、组件上的 source/terminal 标志、是否已出现唯一 source，以及拒绝闭环或提前消失的独立组件所需的状态。普通占用顶点度为 2，source 和 terminal 度为 1；最终必须是一条连通路径。source 只能标在某片第一列的第 0 层；将这片平移至 k=0 就锚定原 `.up 0 0`。terminal 只能标在第 h−1 层的 down 顶点，即 c≡h mod 2 的槽位。终点可以在扫描顺序中先于 source，状态不能错误地禁止这种合法情形。

?：每次转移必须处理一个实际占用的切片，按本次新处理顶点数 m 赋权 x^m，其中 1≤m≤2h。初末边界不额外计算顶点；禁止任意空片填充。局部选边和标记的选择作为转移标签，因而矩阵条目为非负系数多项式。必须证明接受的带标签字与原 BridgePath 的双射（或另一个足以双向控制质量的严格对应），并证明每个顶点恰计一次。

记 α=criticalActivity、A=A_h(α)，以及初始、终止向量 u,v。所需的精确身份是

\[
c_k=u^\top A^k v
 =\sum_{p:\,\text{占用恰 }k\text{ 片}}\alpha^{|p.\mathrm{vertices}|}.
\]

只有把真实路径注入一个更大的接受语言是不够的：即使真实桥总质量有限，伪接受字也可能具有无限质量。忘记连通分划、允许提前闭合组件或允许空片填充，都可能产生此问题。完整编码尚未构造，本报告不把它当作可用定理。

I：下面的**有限矩阵引理**有完整的纸面证明，适合先提炼为独立条件引理；尚未在 Lean 实现。设 S 是有限状态集，A≥0，u,v≥0。先将状态限制到既能从 u 以正权到达、又能以正权到达 v 的 trim 部分。删去其他状态不改变任何正权接受字。空 trim 集单独处理。

假定

\[
M=\sum_{n\ge0}c_n=\sum_{n\ge0}u^\top A^n v<\infty.
\]

对每个保留的 i,j，选取 a_i,b_j，使

\[
r_i=(u^\top A^{a_i})_i>0,\qquad
 t_j=(A^{b_j}v)_j>0.
\]

非负性给出

\[
r_i(A^n)_{ij}t_j\le c_{a_i+n+b_j}.
\]

右边的移位索引随 n 单射，所以

\[
\sum_{n\ge0}(A^n)_{ij}\le M/(r_it_j)<\infty.
\]

定义 s_i=∑_n∑_j(A^n)_{ij}。有限维与非负级数换序给出

\[
1\le s_i<\infty,\qquad As=s-\mathbf1.
\]

取 q=max_i(1−1/s_i)，则 0≤q<1，且 As≤qs。取 C=max_i(v_i/s_i)，便有

\[
c_n\le C(u^\top s)q^n,
\qquad
\sum_{n\ge0}nc_n<\infty.
\]

若 q=0，n≥1 项直接为零；其余情形用普通几何级数的一阶矩。整个论证不需要 Perron–Frobenius、谱半径或不可约性。**trim 是必要条件**：例如 A=diag(1/2,2)、u=v=(1,0)，单个接受 Green 级数有限，而第二行 Green 级数发散；不能从单一桥总质量直接推未 trim 的全部状态可和。

I：结合精确编码与顶点数上界，得到

\[
\sum_p |p.\mathrm{vertices}|\alpha^{|p.\mathrm{vertices}|}
\le 2h\sum_k k c_k<\infty.
\]

因此缺少的几何输入可缩小为下面的**未知有限 K_h** 接口。令 V_{h,R} 为 0≤j<h 且 −2R≤c≤2R+1 的顶点集，则希望证明

\[
\forall h\ge1\;\exists K_h\in\mathbb R_{\ge0}\;
\forall R\in\mathbb N\;\forall\mathcal F\subset\mathrm{BridgePath}(h)\text{ 有限},
\quad
(\forall p\in\mathcal F,\ p.\mathrm{vertices}\subset V_{h,R})
\Rightarrow
\sum_{p\in\mathcal F}\alpha^{|p.\mathrm{vertices}|}\le K_h.
\]

每个有限桥集合都包含于某个共同 V_{h,R}，所以这个接口直接给临界总质量有限；无需先证明固定长度计数界。K_h 可随 h 变化。假设 Kh、精确编码和矩阵引理都获得真证明后，才可得到一阶矩并调用现有 helper。这是一条新的条件证明路线，当前仍未闭合。

I/?：有限域的 parafermionic 抵消是得到 K_h 的具体候选。把普通桥在底端和顶端各延长半条缺失边，得到 boundary-mid-edge 路径。对当前 regular honeycomb 嵌入，可考虑

\[
F(z)=\sum_{\gamma:a\to z}\alpha^{N(\gamma)}e^{-i\sigma W(\gamma)},\qquad\sigma=5/8,
\]

其中 N 是经过的原图顶点数。每个内部三价顶点的局部候选守恒式为 ∑_{z\sim v}(z−v)F(z)=0。将路径按未访问该顶点的三种终止/延伸选择以及已访问情况下的成对反向片段分组，对应的两个代数抵消为

\[
1+2\alpha\cos(7\pi/8)=1-2\alpha\cos(\pi/8)=0,
\qquad
2\cos(2\pi/3+4\sigma\pi/3)=2\cos(3\pi/2)=0.
\]

这些代数式与当前 α 的定义吻合；它们本身没有证明路径分组和有限域守恒式。

?：若能将局部式对有限砖墙矩形求和，正确分类从底端 a 到各边界出口的总转角，并证明所有其他边界项为非负，则可能获得顶端桥总质量的有限上界。为使此建议可核查：原 [position](/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/tasks/HoneycombBridgeFiniteness/workspace/generated/problem/Challenge.lean:12) 满足物理横坐标 x=c/2；a 位于 y=0，top 缺失边的中点位于 y=h√3/2。预期 top 交叉路径总转角为 0，bottom 为 ±π，左右边为 ±π/3 或 ±2π/3；相应取实部的候选系数为 1、cos(3π/8)、cos(π/8)、cos(π/4)，全为正。证明这些转角值需要真正的平面简单路径/边界闭合论证，不能仅由局部邻接和终点切向相同推出。

?：**K_h=1 尚未建立。** 上述边界-mid-edge 模型的空路径、边界长度归一化、半边端点，以及 `N(γ)=p.vertices.length` 的精确对应都需要逐项证明。纸面候选中 N 取顶点数，因而可能与原权重一致，但本报告未完成完整的局部配对与边界 winding 证明。正常任务交接应只使用“存在未知有限 K_h”作为待证目标，不能把 1 或任何数值上界加入已知前提。

交付给现有 researcher-2 的顺序建议为：先核对缺口并选择一个能完成的具体引理；可先证明 trim 有限矩阵的 Green→一阶矩条件引理，再用精确状态接口组织原图编码，或独立检查有限域局部抵消及顶端边界质量界。每一步必须报告实际证明覆盖范围。单独完成矩阵引理不会解决原题，也不保证几何输入容易。

一般非负序列的一阶矩可和并不蕴含严格指数计数差距，例如 a_n=μ^n/(n+1)^3 在 α=1/μ 时一阶矩可和而增长指数仍为 μ。因此本报告只声称新接口加编码足以使用已验收 helper，不把原 `strip_growth_below_mu` 记为已解或改写成“已等价解决”。

本次可交付状态如下。

| 内容 | 证据状态 |
|---|---|
| 一阶矩可和足以推出全部六个原题结论 | E：父任务指定的已验收归约源码，171 行 |
| 周期二砖墙坐标、每片 2h 顶点、长度 ≤2hk | I：从原邻接和 Nodup 直接导出；本次未写 Lean |
| trim 有限非负矩阵：总 Green 质量有限 ⇒ 一阶矩有限 | I：以上给出完整条件证明；本次未写 Lean |
| 原 BridgePath 与接受字精确对应 | ?：待构造并证明，不能只用单向过估计 |
| 存在统一有限矩形质量上界 K_h | ?：仍是实质数学缺口 |
| parafermionic 局部配对、边界 winding 与当前归一化 | ?：具体候选，尚未证明；K_h=1 未确认 |
| 原题无条件证明 / 原生最终验收 | 未获得，活动目标与队列未由本任务改变 |

可供正常计划队列递送的简明说明已另存 [native-advisory-handoff.md](/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/honeycomb-math-route-20261024/native-advisory-handoff.md)。父任务将其中证据定位调整为模型可访问的集成 commit 与精确 helper 签名；本报告保留主机归档路径以便审阅。研究在给出一个具体、非循环的条件引理及明确剩余数学输入后结束，没有重做先前 Mathlib 的泛关键词搜索或小宽度枚举。
