# 产品宣传网站与证明档案

线上地址：<https://likc1606.github.io/theorem-os/>。网站由本仓库的 GitHub Actions 构建并发布到 GitHub Pages。

静态网站包含两个入口：

- `index.html`：中文产品宣传首页，包括数学结构动效、官方证明成果、M1–M5 组件介绍、本地体验命令和常见问题。
- `archive.html`：证明档案，支持搜索、筛选、源码查看、验收证据、JSON 下载和本地回放记录。

网站独立于 CLI，不启动 Agent 或 Lean，不需要服务端或模型认证。

## 本地预览

```bash
bun install --frozen-lockfile
bun run build:site
```

打开 `out/site/index.html`。使用相对资源路径，档案数据打包进脚本，支持直接打开本地文件，也支持 GitHub Pages 的 `/theorem-os/` 子路径。

首页的成果数量、归属和官方结果链接由档案生成，构建时写入 HTML；首屏数学图形为 SVG，浏览器不支持 JavaScript 时也能查看首页正文和成果入口。组件切换、动效控制、手机导航及命令复制使用独立的小型脚本，档案源码在进入 `archive.html` 时加载。

## 数据来源

- `accepted/accepted.json`：官方结果链接、原始项目和模型归属、题目版本、原始提交、文件校验值。
- `accepted/*/verification.json`：已有的本地检查与来源记录。检查投影和最终归档文件的哈希可能不同，档案界面会标明差异；官方验收状态以官方响应为准。
- `in-progress/snapshot.json` 与各题 `manifest.json`：研究快照的时间、轮数、worker 数量和任务状态。它们不构成整题验收，也不计入首页的官方通过数量。

成果来自前身 DeepScientist / DeepScientist Math 及后续工作，包含继续运行与环境迁移。页面保留原始归属，不将这些案例表述为当前运行时从零求解的成功率评测。

构建时校验已验收提交包全部登记文件，以及页面收录的研究源码的 SHA-256。页面仅提取这些记录的明确字段，以及 solver 的 `Challenge.lean`、`Submission.lean`、`Submission/Helpers.lean`；不复制 `state.json`、会话、环境文件或完整实验目录。档案的源码行数仅统计页面收录的文件。

生成的 `out/site/data/catalog.json` 与档案使用同一份数据。源码链接固定到构建时的仓库提交，避免后续 `main` 变化使证据链接漂移。

## 修改页面

- `docs/index.html`、`docs/landing.css`：宣传首页内容和响应式样式。
- `docs/web/landing.ts`：组件切换、命令复制、手机导航和动效控制。
- `docs/web/presentation.ts`：数学结构图和从真实档案生成的成果卡片。
- `docs/archive.html`、`docs/site.css`、`docs/web/app.ts`：证明档案界面。
- `scripts/build-site.ts`：构建两个页面、浏览器脚本和公开数据，并复制素材与许可证。

首页采用深蓝首屏、亮蓝研究图形和浅色内容区，桌面与手机分别布局。三维结形 SVG 是研究空间的概念示意，曲面在构建时生成；浏览器只对轨道上的单条线条应用动效。组件图中的五个节点表示五类研究决策，最终完整原题验收单独展示。页面支持键盘操作，并尊重系统的减少动态效果设置。

## 验证

```bash
bun run typecheck:site
bun run test -- tests/siteCatalog.test.ts
bun run build:site
bunx playwright install chromium --only-shell
bun run test:site
```

浏览器检查覆盖首页成果与真实档案的一致性、组件切换和键盘控制、命令复制与失败反馈、手机导航、减少动态效果、本地文件预览、GitHub Pages 子路径，以及证明档案的搜索、筛选、源码、来源、下载和链接恢复。检查 320、390、768、1440、1920 像素宽度，截图输出到 `out/site-checks/`。这些检查不调用模型。

## GitHub Pages 部署

工作流位于 `.github/workflows/pages.yml`。在 GitHub 仓库的 **Settings → Pages → Build and deployment** 中选择 **GitHub Actions**，再在 **Settings → Secrets and variables → Actions → Variables** 中添加仓库变量 `PAGES_ENABLED`，值为 `true`。配置好 Pages 后，推送页面或档案变化到 `main` 会运行检查并部署 `out/site`；也可以手动触发。未开启该变量时仍会执行构建与浏览器检查，并跳过发布，适用于尚未配置 Pages 或当前套餐不支持私有仓库 Pages 的情况。

预期地址为 `https://likc1606.github.io/theorem-os/`。私有源仓库需要账号支持该仓库的 Pages 功能；源仓库是否私有与站点是否公开是两个设置。工作流不改变仓库可见性，也不自动创建 Pages 配置。

## 视觉素材

`docs/assets/mark.svg` 是首页与档案共用的蓝色项目标记，`mark.png` 保留为位图版本。首页使用本地 Inter 可变字体，中文使用系统无衬线字体；字体及 SIL Open Font License 保存在 `docs/assets/fonts/`。构建时将字体嵌入样式，确保直接打开本地文件时也能加载，页面不依赖外部字体服务。

`social-preview.png` 是分享卡片，由首页数学图形和排版生成。修改设计后运行：

```bash
bun run build:site
node scripts/capture-promo.mjs
bun run build:site
```

`replay.png` 来自一次真实的预设回放，其公开记录字段保存在 `replay.json`，明确注明没有调用模型、不是官方评测。`archive-preview.png` 是证明档案的界面截图。

重新生成回放素材时，先完成一次预设回放，再运行：

```bash
node scripts/capture-site-assets.mjs /path/to/preset-replay/result.json
bun run build:site
```

该脚本只读取已有回放结果，不调用模型。界面图标使用 Lucide，许可证随静态产物保留。
