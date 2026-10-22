# 产品宣传网站与证明档案

线上地址：<https://likc1606.github.io/theorem-os/>。网站由本仓库的 GitHub Actions 构建并发布到 GitHub Pages。

静态网站包含三个入口：

- `index.html`：中文产品宣传首页，包括可缩放的真实工作台截图、可播放和暂停的四步预设回放、官方证明成果、M1–M5 组件介绍与可展开的源码示例、Docker 部署和 CLI 体验命令。
- `archive.html`：证明档案，支持搜索、筛选、源码查看、验收证据、JSON 下载和本地回放记录。
- `feedback.html`：问题反馈、功能建议和使用咨询，预览后前往 GitHub Issues 确认发布。

网站独立于 CLI，不启动 Agent 或 Lean，不需要服务端或模型认证。

## 本地预览

```bash
bun install --frozen-lockfile
bun run build:site
```

打开 `out/site/index.html`。使用相对资源路径，档案数据打包进脚本，支持直接打开本地文件，也支持 GitHub Pages 的 `/theorem-os/` 子路径。

首页的成果数量、归属和官方结果链接由档案生成，构建时写入 HTML；浏览器不支持 JavaScript 时也能查看真实工作台截图、首页正文、默认部署命令和成果入口。组件切换、手机导航及命令复制使用独立的小型脚本，档案源码在进入 `archive.html` 时加载。静态站点构建不依赖工作台服务。

## 数据来源

- `accepted/accepted.json`：官方结果链接、原始项目和模型归属、题目版本、原始提交、文件校验值。
- `accepted/*/verification.json`：已有的本地检查与来源记录。检查投影和最终归档文件的哈希可能不同，档案界面会标明差异；官方验收状态以官方响应为准。
- `in-progress/snapshot.json` 与各题 `manifest.json`：研究快照的时间、轮数、worker 数量和任务状态。它们不构成整题验收，也不计入首页的官方通过数量。

当前静态站点和已验收清单仍只收录早期 6 道证明；2026 年 10 月 16 日获官方 4/4 通过的 [#2144 四题](../submitted/README.md) 保留在原提交归档中，未计入站点统计。

成果来自前身 DeepScientist / DeepScientist Math 及后续工作，包含继续运行与环境迁移。页面保留原始归属，不将这些案例表述为当前运行时从零求解的成功率评测。

构建时校验已验收提交包全部登记文件，以及页面收录的研究源码的 SHA-256。页面仅提取这些记录的明确字段，以及 solver 的 `Challenge.lean`、`Submission.lean`、`Submission/Helpers.lean`；不复制 `state.json`、会话、环境文件或完整实验目录。档案的源码行数仅统计页面收录的文件。

生成的 `out/site/data/catalog.json` 与档案使用同一份数据。源码链接固定到构建时的仓库提交，避免后续 `main` 变化使证据链接漂移。

## 修改页面

- `docs/index.html`、`docs/landing.css`：宣传首页内容和响应式样式。
- `docs/web/landing.ts`：回放步骤与组件切换、三种开始方式、命令复制和手机导航。
- `docs/web/presentation.ts`：预设回放展示和从真实档案生成的成果表格。
- `docs/archive.html`、`docs/site.css`、`docs/web/app.ts`：证明档案界面。
- `docs/feedback.html`、`docs/feedback.css`、`docs/web/feedback.ts`：反馈表单、全文预览和 GitHub Issues 跳转。
- `scripts/build-site.ts`：构建三个页面、浏览器脚本和公开数据，并复制素材与许可证。

首页按 taste-skill 的大字排版方向组织内容，以白色品牌声明、浅青色回放与薄荷色组件区形成章节变化。首屏使用本地工作台真实的 Mathlib 草稿截图，明确标为未提交；手机和平板通过 `picture` 加载独立视口，平板采用画面与说明并排的构图。截图可打开完整界面预览，支持缩放、鼠标拖动和触屏滚动，关闭后恢复焦点；无 JavaScript 时仍可打开原图。开始区默认展示完整 Docker 部署命令，也可切换 CLI 安装和免模型回放。GitHub Pages 仅提供静态展示；用户需在 Linux 本地或服务器部署工作台，再输入自己的 API Key。

四步回放的候选源码读取自 `src/math/localExample.ts`，回执读取自 `docs/assets/replay.json`；切换演示不会启动模型或 Lean。默认停在最终验收，点击播放后从候选开始，可暂停续播、手动选步和重新播放；离屏或页面隐藏会暂停，返回后由用户继续播放。反馈步骤是对预设示例的检查说明，并非原始诊断日志。手机端先展示已归档的最终回执，再展示选中步骤的源码。源码与回放记录改动后需要重新构建。

首屏名称使用 GSAP 遮罩入场，成果按行出现，组件选项依次进入，产品图轻微缩放落定；组件和命令切换采用短过渡。系统启用减少动态效果时，内容即时切换，回放仍可按步骤阅读。GSAP 固定版本与锁文件一起管理，版权和许可链接随静态产物保留在 `assets/licenses/gsap-NOTICE.txt`。

完整原题验收独立于五类研究决策。组件用大字号索引展示，手机端五个标签完整排列为网格，支持键盘选择；源码示例默认收起，可在没有 JavaScript 的情况下展开。产品区补充实际 Lean 源码与模型配置截图，API Key 保持为空。档案区展示完整的真实界面，手机端使用单独的题目详情截图，避免放大裁切桌面图。网页工作台的临时历史与 CLI 的持久运行和恢复分开说明。参考官网与应用取舍记录在 [design-references.md](design-references.md)，本轮方向、素材来源与审查记录见 [design-taste.md](design-taste.md)。

## 用户反馈

首页桌面导航、手机导航、页脚以及证明档案都链接到 `feedback.html`。反馈分为问题反馈、功能建议、使用咨询，可填写相关位置、标题、描述及可选环境。表单在本地整理 Markdown，预览确认后由用户进入固定仓库的 GitHub Issue 编辑页；最终发布需要用户登录 GitHub 并确认，静态网站不持有 GitHub Token，也不显示虚假的提交成功状态。

反馈将公开，页面提示不要填写 API Key 或个人敏感信息。不会自动读取工作台、浏览器查询参数、源码或认证信息，也不把表单写入浏览器存储。完整编码 URL 超过 7500 字符时不附带正文，页面明确提示先复制或下载全文，再到 GitHub 粘贴；全文始终保留在预览里，复制失败时会选中正文供手动复制。无 JavaScript 或脚本不可用时保留直接提交到 GitHub 的入口。此方案可直接部署到 GitHub Pages，不需要额外服务器；若后续需要匿名或私密反馈，应另接支持这些能力的接收服务。

## 验证

```bash
bun run typecheck:site
bun run test -- tests/siteCatalog.test.ts
bun run build:site
bunx playwright install chromium --only-shell
bun run test:site
```

浏览器检查覆盖响应式截图、首屏可见、原图预览的缩放与拖动、弹窗关闭和焦点恢复、档案图片无裁切、源码示例展开、手机组件标签的键盘可见性、三种开始方式与部署命令复制、预设回放与记录的一致性、移动端回执顺序、首页成果的真实归属、复制失败反馈、手机导航、本地文件预览、无 JavaScript 内容与 GitHub Pages 子路径，以及证明档案的搜索、筛选、源码、来源、下载和链接恢复。检查 320、390、768、1440、1920 像素宽度，截图输出到 `out/site-checks/`。这些检查不调用模型。

`test:site` 还运行 `test-landing-motion.mjs`，检查首屏入场、回放的暂停续播与结束、手动选步、键盘焦点，以及离屏、页面隐藏和减少动态效果设置；报告与截图输出到 `out/site-motion-checks/`。

`test-feedback.mjs` 检查表单校验、分类切换、Markdown 编码、超长内容的复制与下载、弹窗焦点、桌面与手机排版、本地文件、Pages 子路径和无 JavaScript 入口。测试不会创建真实 Issue。

## GitHub Pages 部署

工作流位于 `.github/workflows/pages.yml`。在 GitHub 仓库的 **Settings → Pages → Build and deployment** 中选择 **GitHub Actions**，再在 **Settings → Secrets and variables → Actions → Variables** 中添加仓库变量 `PAGES_ENABLED`，值为 `true`。配置好 Pages 后，推送页面或档案变化到 `main` 会运行检查并部署 `out/site`；也可以手动触发。未开启该变量时仍会执行构建与浏览器检查，并跳过发布，适用于尚未配置 Pages 或当前套餐不支持私有仓库 Pages 的情况。

预期地址为 `https://likc1606.github.io/theorem-os/`。私有源仓库需要账号支持该仓库的 Pages 功能；源仓库是否私有与站点是否公开是两个设置。工作流不改变仓库可见性，也不自动创建 Pages 配置。

## 视觉素材

`docs/assets/mark.svg` 是首页与档案共用的蓝色项目标记，`mark.png` 保留为位图版本。首页使用本地 Hanken Grotesk 字体，字面代码使用 Fira Code，中文使用系统无衬线字体。字体及各自的 SIL Open Font License 保存在 `docs/assets/fonts/`。构建时将字体嵌入样式，确保直接打开本地文件时也能加载，页面不依赖外部字体服务。

`workbench-desktop.png` 和 `workbench-mobile.png` 来自真实本地工作台的新会话，分别是 1440×500 的桌面视口和 390×440 的手机视口。`workbench-full-desktop.png` 与 `workbench-full-mobile.png` 为弹窗使用的完整截图，视口分别是 1440×900 和 390×844，以 2 倍像素密度生成。桌面展示左侧对话与右侧源码，手机切到工作区，展示经过正常编辑器载入的紧凑 Mathlib 草稿；图注均标明未提交。截图脚本核对源码在手机上完整可见并阻止创建任务，不需要模型或 Key：

```bash
node scripts/capture-workbench.mjs http://127.0.0.1:8787
```

`workbench-source-detail.png` 是右侧 Lean 工作区的完整片段，保留未提交状态与 `sorry`；`workbench-settings-detail.png` 是原生研究配置弹窗正常滚动后的可见区域，展示服务商、模型、空 Key 与预算。二者均以 2 倍像素密度导出，同一截图脚本生成并验证零 API POST。

`social-preview.png` 是分享卡片，由上述工作台截图和首页排版生成。修改设计后运行：

```bash
bun run build:site
node scripts/capture-promo.mjs
bun run build:site
```

`replay.png` 来自一次真实的预设回放，其公开记录字段保存在 `replay.json`，明确注明没有调用模型、不是官方评测。`archive-preview.png` 是完整桌面档案界面，`archive-preview-mobile.png` 是手机端题目详情，两者都使用 2 倍像素密度。只更新档案截图时运行：

```bash
bun run build:site
node scripts/capture-archive.mjs
bun run build:site
```

重新生成回放素材时，先完成一次预设回放，再运行：

```bash
node scripts/capture-site-assets.mjs /path/to/preset-replay/result.json
bun run build:site
```

该脚本只读取已有回放结果，不调用模型。界面图标使用 Lucide，许可证随静态产物保留。
