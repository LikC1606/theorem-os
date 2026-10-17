# 官网设计执行记录

本轮按 [taste-skill](https://github.com/Leonxlnx/taste-skill) 的 `design-taste-frontend` 流程执行，安装版本固定为 `f624f37a8c650b9cc550253104925efe4c8de246`。这是官网的设计与自查记录，不代表外部评审或产品性能测评。

## 目标与真实材料

面向数学 Agent 研究者与 Lean 开发者，让访客看清实际工作台、理解独立验收，再进入本地部署。

材料清单：TheoremOS 名称；自备模型 Key；固定 Lean / Mathlib 环境；冻结原题身份；隔离研究工作区；M1–M5 源码接口；单 Agent 与协作研究；候选与诊断；`evaluated_passed` 独立回执；带原始归属的官方证明包；可下载档案；静态 Pages 与 Linux 运行环境的边界。

概念句：在这张页面上，TheoremOS 保存的“候选源码 → 检查反馈 → 修复 → 独立回执”成为从品牌声明延续到成果索引与部署命令的排版主线。可操作的核心是现有四步证明回放，使用仓库真实预设源码与本机归档回执。

## 方向与适配

三选一选择 `type-only-statement`，seed **6632587**。大字、整章色场和不同位置的正文，适合以名称及研究输出组织页面；没有采用卡片密铺方向。

采用 Hanken Grotesk，自托管字体与 OFL 许可证，中文使用系统字体；Fira Code 仅用于字面代码。字体来自 Google Fonts 的版本化字体 URL，随仓库保留各自许可证。所有字距为 0，字号使用固定值与断点，优先遵守项目约束。

保留抽取的章节色场比例，将糖果色映射到现有品牌的白、墨色、蓝与验收绿，并使用浅青与薄荷区分章节。首屏保留大字主导，同时放入真实工作台并露出下一章，适配产品必须第一屏可见的要求。没有采用天空气氛图、虚构客户或虚构指标。

三次章节替换，保留同一 seed：

- `how-it-works-pinned-fragment-changing-state`：没有可用于同比例时间条的通用运行时长，已有四状态回放能够真实解释过程。
- `features-capabilities-at-poster-scale`：M1–M5 是可替换源码接口，不能画成可直接开关的设置。
- `showcase-band-of-unequal-panels`：可编辑宣传标题会暗示静态官网能在线证明，改用真实源码、设置和档案图像。

成果章采用记录式索引保留所有官方结果，部署章保留完整 Docker / CLI 命令。后者适配了整章单词按钮的随机蓝图，避免损失必要的部署信息。FAQ 用宽标题与缩进问题，页脚以完整名称收尾，不人为撑满一屏。

## 页面论点与文案

| 章节 | 主张 | 证据 / 内容 |
| --- | --- | --- |
| 首屏 | TheoremOS，数学 Agent 的开源研究运行时 | 真实工作台双栏截图；连接自己的模型；独立验证 Lean 证明；主操作“部署本地工作台” |
| 回放 | 从候选，到独立验收。 | 四步预设源码回放、最终回执、原始 JSON 与完整档案；明确不调用模型 |
| 成果 | 研究成果，有据可查。 | 从真实 catalog 生成的全部官方通过记录；来源、模型与官方结果链接；前身成果归属 |
| 组件 | 五种决策，组合研究。 | 五个完整可选组件，真实输入输出、源码接口与 M3 示例 |
| 产品图 | 让研究过程，看得见。 | 未提交 Mathlib 源码、模型与空 Key 配置、可检索的真实证明档案 |
| 部署 | 开始你的下一次研究。 | Linux / Docker、CLI 与预设回放三种完整命令；资源要求与部署边界 |
| FAQ | 开始之前。 | 用途、运行位置、支持的 Key、记录生命周期四个实际问题 |
| 页脚 | 让数学探索，有据可循。 | 档案、文档、源码、研究预览版本与 AGPL 许可证 |

辅助正文保留完整事实，不用宣传语代替验收方式或运行限制。网页截图中的 `sorry` 与“未提交”始终保留，不把草稿描述为成功证明。

## 素材来源

所有产品图来自此仓库可复现的本地 UI，未调用真实模型：

- `workbench-desktop.png` / `workbench-mobile.png`：未提交 Mathlib 草稿，首屏展示。
- `workbench-source-detail.png`：真实右侧 Lean 源码区，953×444 自然尺寸，2x 导出。
- `workbench-settings-detail.png`：真实配置弹窗正常内滚动，600×800 自然尺寸，2x 导出；API Key 为空。
- `archive-preview.png` / `archive-preview-mobile.png`：本仓库实际证明档案。

截图脚本阻止工作台所有 API POST，并验证 Key 为空。交互回放比不相关的外部视频更直接解释研究流程，因此不额外加入背景视频。

## 审查记录

以下均为按技能量表进行的内部截图自评，不是外部网站或评委给分。

```text
ROUND 0
Seen in one second: TheoremOS 品牌字与浅色工作台截图。
Idea (one sentence): 保存候选源码与独立验收供研究者复盘，但首屏与后半页仍是通用软件站语法。
Live thing: 真实预设归档的四步证明回放。
Layout words by section: hero=centered-stack / replay=dark-tool / results=equal-grid / components=split / records=split / start=split / faq=split / footer=wordmark。
Scores: design 5.8 · usability 7.2 · creativity 5.5 · content 8.0 → overall 6.0
Caps applied: inspector 多项 FAIL，overall≤6.0；重复占位图、较小灰字与装饰细线限制了设计评分。
Top three problems (most visible first), each with the screenshot it shows in and the fix:
1. taste-baseline/desktop-page-01.jpg：成果前三项反复使用同一 ⊢ 占位图。改为完整真实成果索引，逐项保留来源、模型与官方结果。
2. taste-baseline/desktop-page-02.jpg：灰色小字、多层细线与相同两栏骨架。扩大正文，采用章节色场、索引与图像构图。
3. taste-baseline/mobile-page-01.jpg：手机组件标签被横向裁切。改为五项完整网格，保留键盘选择。
```

```text
ROUND 1
Seen in one second: 大幅 TheoremOS 名称和真实双栏工作台。
Idea (one sentence): 用真实研究输出构成品牌声明、验收工具和成果索引。
Live thing: 保留并放大真实四步回放与最终回执。
Layout words by section: hero=statement-and-product / replay=full-field-tool / results=table-index / components=large-type-selector / records=asymmetric-gallery / start=dark-command / faq=questions / footer=brand-statement。
Scores: design 7.0 · usability 7.6 · creativity 7.0 · content 8.4 → overall 6.0
Caps applied: inspector 仍有 FAIL，overall≤6.0；需要处理关闭 details 内容的测量与图注识别，以及手机表格被误判为图标卡片的问题。
Top three problems (most visible first), each with the screenshot it shows in and the fix:
1. taste-round-1/desktop-fold.jpg：首屏较长，下一章完全未出现。收紧首屏间距，保留完整产品画面。
2. taste-round-1/tablet-fold.jpg：桌面工作台缩成很小的字。平板改用手机视口图片，配合独立的并排说明。
3. taste-round-1/desktop-page-02.jpg：档案图片仍显示旧的三个验收统计。重拍当前实际档案，断言与 catalog 一致，显示六个官方通过和一份研究快照。
```

中间复检修复了真实图注被误认作眉题的问题：桌面图注归到画面右下角，手机图注与下一章明确拉开；关闭的源码详情使用显式 `display: none`；手机记录行不再画表格细线。代码字体改为自托管，避免系统字体回退。最终没有对 inspector 使用 `--allow`，也没有修改技能检查器。

```text
ROUND 3
Seen in one second: 大幅 TheoremOS 字标与真实 Lean 双栏工作台。
Idea (one sentence): 让 TheoremOS 的候选源码、五类研究决策与独立验收回执成为页面主体，用可查证的研究记录组织产品说明。
Live thing: 真实预设归档的四步证明回放；访问者可播放、暂停、切步并打开原始回执，不调用模型。
Layout words by section: hero=statement-and-product / replay=full-field-tool / results=table-index / components=large-type-selector / records=asymmetric-gallery / start=dark-command / faq=questions / footer=brand-statement。
Scores: design 7.4 · usability 8.0 · creativity 6.5 · content 8.5 → overall 7.5
Caps applied: inspector 无 FAIL；四张不同真实产品画面达标，正文16–18px，无低对比文本、横向溢出或缺图。候选到验收的主题仍可被相邻 Lean 产品沿用，creativity≤7。保留 no-footage WARN，因为交互回放直接展示实际过程，没有加入装饰视频。
Top three problems (most visible first), each with the screenshot it shows in and the fix:
1. taste-final/desktop-page-01.jpg 与 mobile-page-01.jpg：成果索引完整可信，但等行距略长，后续可以减少行间留白，继续保留全部出处与链接。
2. taste-final/desktop-fold.jpg 与 mobile-fold.jpg：下一章色场已露出，标题只出现在底缘；后续可以略减章节顶部间距。平板已同时看到下一章标题与工具开头。
3. taste-final/desktop-page-02.jpg 与 tablet-page-01.jpg：源码与设置细字需要点开原图阅读；后续可以进一步聚焦裁图。当前有完整原图入口，不影响正文理解。
```

按十四项审查逐一核对焦点、体量、独特性、边缘、留白、字体、色彩、图像、章节变化、手机构图、内容密度、事实、遮挡与实际交互。未发现遮挡、空白入场区或关键内容缺失。达到本轮三次检查上限后保留上述非功能性的取舍。

## 最终验证

- `bun run typecheck`、`bun run typecheck:site`、`bun run build:site` 通过。
- `bun test tests/siteCatalog.test.ts`：8 项通过，覆盖归属、来源绑定与验收记录。
- `bun run test:site` 通过：首页与档案交互、五种宽度、9 组回放与动画偏好场景；包含无 JavaScript、文件预览和 Pages 子路径，未调用模型。
- taste-skill 源码扫描：**0 FAIL、0 WARN**；实际浏览器检查：**0 FAIL、1 WARN**（无视频，取舍见上文），检测到 55 个元素发生动画。
- 1920、1440、768、390、320 像素下，标题均不超过两行；首屏分别露出下一章 83、62、317、103、88 像素。
- 新截图脚本成功执行；档案截图统计与当前 catalog 一致；`git diff --check` 通过。

构建预览：`out/site/index.html`。最终桌面、平板、手机截图与测量报告：`out/taste-final/`。安装技能位于 `~/.codex/skills/taste-skill`；它是开发工具，网站构建与部署不依赖本地技能目录。本轮未提交、推送或发布。

## GSAP 与 React Bits 实际应用

后续按用户要求使用新安装的技能，针对组件交互继续优化，沿用 `type-only-statement` 方向与 seed **6632587**。这是已有页面的局部打磨，按 taste-skill 的组件流程保留方向，没有重新抽取或新增素材。

- **GSAP 官方技能**：`greensock/gsap-skills`，固定安装提交 `aed9cfd3277740755f6bfc1155c7aa645403b760`。执行核心、时间线与性能指导，保留品牌遮罩入场和四步回放，新增选中背景的可中断过渡。仅动画 transform；尺寸变化、字体加载完成和减少动画偏好切换时立即校准。离页清理与浏览器返回缓存分别处理。
- **React Bits 社区技能**：`Marco9442/reactbits-skill`，固定安装提交 `afd9684ffb2136fc93cc711907edb18eac5efe91`。实际从[官方 registry](https://reactbits.dev/r/GooeyNav-TS-CSS.json) 获取并阅读 GooeyNav 的 TypeScript/CSS 源码，参考其目标测量、ResizeObserver 与字体就绪后的校准方式。官网为原生 TypeScript，因此在 `docs/web/selectionIndicator.ts` 实现适配现有 DOM 的 GSAP 选中背景；这是交互思路适配，未直接挂载 React 组件。
- **Taste-skill**：复查桌面、平板和手机截图，将组件选中表面改为白色，文字始终保持深色，避免背景移动时出现白字落在浅底上的低对比。手机首屏收紧 20px，回放章节顶部缩短 8px，同时保留图注与下一章的层次。成果行上下留白由 26px 收紧到 20px，保留全部来源与证据。

滑动选中应用于 M1–M5 组件、四个回放步骤和三种部署命令。键盘焦点与面板内容同步更新；无脚本时沿用静态选中背景。组件下载位于 `out/design-sources/react-bits/`，仅供开发参考；构建无需 React 或技能目录。

```text
ROUND 1
Seen in one second: TheoremOS 大字与真实双栏工作台。
Idea (one sentence): 继续以候选、研究决策与独立回执组织页面，让选中项的移动连接操作与当前内容。
Live thing: 四步证明回放，以及五个研究组件的真实输入输出切换。
Layout words by section: hero=statement-and-product / replay=full-field-tool / results=table-index / components=large-type-selector / records=asymmetric-gallery / start=dark-command / faq=questions / footer=brand-statement。
Scores: design 7.5 · usability 8.1 · creativity 6.5 · content 8.5 → overall 7.6
Caps applied: 内部截图自评；最终 inspector 无 FAIL。与相邻 Lean 产品共用的叙事主题仍限制独创性。保留 no-footage WARN，真实交互回放能够展示候选与回执，没有合适的产品实录视频。
Top three problems (most visible first), each with the screenshot it shows in and the fix:
1. skills-baseline/mobile-fold.jpg：首屏到下一章的空隙偏长。收紧手机首屏，同时保留截图图注与章节标题的距离；见 skills-final/mobile-fold.jpg。
2. skills-baseline/desktop-page-01.jpg：成果索引行间留白偏长。压缩行距，保留全部六项证据；见 skills-final/desktop-page-01.jpg。
3. skills-baseline/desktop-page-02.jpg：组件选中项瞬间跳换。加入可中断的移动选中背景，使用白色表面与深色文本维持过渡时对比；见 skills-final/desktop-page-02.jpg 和交互测试。
```

最终检查记录：`out/skills-final/`。源码扫描 **0 FAIL / 0 WARN**；真实浏览器排版检查 **0 FAIL / 1 WARN**（无视频，理由见上）。类型检查、官网构建、首页与档案浏览器检查均通过。动效测试通过 **9 组**视口与偏好场景，新增快速连续切换、减少动画切换中断、同一页面在 1440 / 768 / 390px 间重排的选中对齐检查；全过程 **0 次 API 请求**。测试会显式等待浏览器原生媒体查询事件，避免把受控动画时钟推进误当作偏好事件已经送达。
