import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import http from 'node:http';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { chromium } from 'playwright';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const site = path.join(root, 'out/site');
const url = pathToFileURL(path.join(site, 'index.html')).href;
const output = path.join(root, 'out/site-checks');
fs.mkdirSync(output, { recursive: true });
const catalog = JSON.parse(fs.readFileSync(path.join(site, 'data/catalog.json'), 'utf8'));
const accepted = catalog.records.filter(record => record.status === 'official_accepted');
const replayEvidence = JSON.parse(fs.readFileSync(path.join(site, 'assets/replay.json'), 'utf8'));
const errors = [];
const browser = await chromium.launch();
let server;
const trackErrors = page => {
  page.on('pageerror', error => errors.push(error.message));
  page.on('console', message => { if (['warning', 'error'].includes(message.type())) errors.push(message.text()); });
  page.on('requestfailed', request => errors.push(`${request.url()}: ${request.failure()?.errorText}`));
};
const checkWidth = async (page, label) => assert.ok(
  await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), `Horizontal overflow: ${label}`,
);
const checkWorkbench = async (page, label) => {
  const figure = page.locator('#workbench-preview');
  assert.equal(await figure.evaluate(node => node.tagName), 'FIGURE');
  assert.equal(await figure.locator('picture.workbench-picture').count(), 1);
  const caption = await figure.locator('figcaption').innerText();
  for (const wording of [/本地/, /工作台/, /截图/]) assert.match(caption, wording);
  assert.match(caption, /未提交/);
  assert.equal(await figure.locator('source[srcset*="assets/workbench-mobile.png"]').count(), 1);
  const screenshot = figure.locator('.workbench-picture img');
  assert.equal(await screenshot.getAttribute('src'), 'assets/workbench-desktop.png');
  assert.ok(await screenshot.getAttribute('alt'), 'The workbench screenshot must have descriptive alternative text');
  await page.evaluate(() => window.scrollTo(0, 0));
  const image = await screenshot.evaluate(async image => {
    await image.decode();
    const bounds = image.getBoundingClientRect();
    return { complete: image.complete, width: image.naturalWidth, height: image.naturalHeight,
      src: image.currentSrc, viewport: innerWidth,
      visibleWidth: Math.max(0, Math.min(bounds.right, innerWidth) - Math.max(0, bounds.left)),
      visibleHeight: Math.max(0, Math.min(bounds.bottom, innerHeight) - Math.max(0, bounds.top)) };
  });
  assert.ok(image.complete && image.width > 0 && image.height > 0, `The screenshot must load: ${label}`);
  const asset = path.basename(new URL(image.src).pathname);
  assert.ok(['workbench-desktop.png', 'workbench-mobile.png'].includes(asset), `Unexpected screenshot: ${image.src}`);
  if (image.viewport <= 390) assert.equal(asset, 'workbench-mobile.png', `Mobile srcset must load at ${label}`);
  if (image.viewport >= 1024) assert.equal(asset, 'workbench-desktop.png', `Desktop screenshot must load at ${label}`);
  const png = fs.readFileSync(path.join(site, 'assets', asset));
  assert.equal(png.subarray(0, 8).toString('hex'), '89504e470d0a1a0a');
  assert.deepEqual({ width: image.width, height: image.height },
    { width: png.readUInt32BE(16), height: png.readUInt32BE(20) }, `Screenshot natural dimensions: ${label}`);
  assert.ok(image.visibleWidth >= 200 && image.visibleHeight >= 100, `The actual workbench must be visible in the first viewport: ${label}`);
};
const checkCommand = async (page, id) => {
  assert.equal(await page.locator(`#command-${id}`).getAttribute('aria-selected'), 'true');
  assert.equal(await page.locator(`#${id}-panel`).isVisible(), true);
  assert.equal(await page.locator(`#${id}-panel`).getAttribute('aria-labelledby'), `command-${id}`);
  assert.equal(await page.locator('.command-panel:visible').count(), 1);
};
const checkScreenshotPreview = async (page, width) => {
  const link = page.locator('.workbench-image-link');
  const dialog = page.locator('#workbench-dialog');
  const originalUrl = page.url();
  await link.click();
  assert.equal(page.url(), originalUrl, 'Opening the preview must keep the visitor on the homepage');
  assert.equal(await dialog.isVisible(), true);
  const preview = await dialog.locator('img').evaluate(async image => {
    await image.decode();
    return { source: image.currentSrc, width: image.naturalWidth };
  });
  assert.match(preview.source, width <= 600 ? /workbench-full-mobile\.png/ : /workbench-full-desktop\.png/);
  assert.equal(await dialog.locator('.preview-original').getAttribute('href'), new URL(preview.source).pathname.split('/').slice(-2).join('/'));
  assert.match(await dialog.locator('#preview-description').innerText(), /草稿 · 未提交/);
  assert.equal(await page.evaluate(() => document.documentElement.classList.contains('preview-open')), true);
  const media = dialog.locator('.preview-dialog-media');
  await dialog.getByRole('button', { name: '放大截图' }).click();
  assert.equal(await dialog.getByRole('button', { name: '适应窗口' }).getAttribute('aria-pressed'), 'true');
  assert.ok(await media.evaluate(node => node.scrollWidth >= node.clientWidth * 1.9), 'Zoom must expose a larger, scrollable image');
  await checkWidth(page, `${width}px screenshot preview`);
  const close = dialog.locator('.preview-close');
  const closeBounds = await close.boundingBox();
  assert.ok(closeBounds && closeBounds.x >= 0 && closeBounds.x + closeBounds.width <= width && closeBounds.y >= 0);
  if (width === 1440) {
    const bounds = await media.boundingBox();
    const before = await media.evaluate(node => node.scrollLeft);
    await page.mouse.move(bounds.x + bounds.width / 2, bounds.y + 100);
    await page.mouse.down();
    await page.mouse.move(bounds.x + bounds.width / 2 - 100, bounds.y + 80, { steps: 5 });
    await page.mouse.up();
    assert.ok(await media.evaluate(node => node.scrollLeft) > before + 70, 'A zoomed image must support mouse panning');
  }
  await close.focus();
  await page.keyboard.press('Tab');
  assert.equal(await dialog.evaluate(node => node.contains(document.activeElement)), true, 'The modal must contain keyboard focus');
  await page.keyboard.press('Escape');
  await page.waitForFunction(() => !document.documentElement.classList.contains('preview-open'));
  assert.equal(await dialog.isVisible(), false);
  assert.equal(await link.evaluate(node => node === document.activeElement), true, 'Closing must return focus to the screenshot');
  await link.click();
  assert.equal(await dialog.getByRole('button', { name: '放大截图' }).getAttribute('aria-pressed'), 'false');
  assert.deepEqual(await media.evaluate(node => ({ left: node.scrollLeft, top: node.scrollTop })), { left: 0, top: 0 }, `The ${width}px preview must reopen at its origin`);
  await dialog.locator('.preview-close').click();
  await page.waitForFunction(() => !document.documentElement.classList.contains('preview-open'));
  if (width === 1440) {
    await link.click();
    await page.mouse.click(2, 2);
    await page.waitForFunction(() => !document.querySelector('#workbench-dialog').open);
  }
};
const checkArchivePreview = async (page, width) => {
  const image = page.locator('.archive-image-link img');
  await image.scrollIntoViewIfNeeded();
  const result = await image.evaluate(async node => {
    await node.decode();
    const bounds = node.getBoundingClientRect(), parent = node.closest('a').getBoundingClientRect();
    return { source: node.currentSrc, ratio: node.naturalWidth / node.naturalHeight,
      renderedRatio: bounds.width / bounds.height, fits: bounds.width <= parent.width + 1 };
  });
  assert.match(result.source, width <= 600 ? /archive-preview-mobile\.png/ : /archive-preview\.png/);
  assert.ok(result.fits && Math.abs(result.ratio - result.renderedRatio) < .01, 'The archive screenshot must remain complete without cropping');
};
const checkProductImages = async (page, label) => {
  const images = page.locator('.workbench-picture img, .product-fragment img, .archive-image-link img');
  assert.ok(await images.count() >= 4, `At least four real product pictures must be present: ${label}`);
  const sources = new Set();
  for (const image of await images.all()) {
    // Bring lazy-loaded fragments into view before waiting for their pixels.
    await image.scrollIntoViewIfNeeded();
    const picture = await image.evaluate(async node => {
      await node.decode();
      const bounds = node.getBoundingClientRect(), container = node.closest('a').getBoundingClientRect();
      return {
        source: node.currentSrc, alt: node.alt, complete: node.complete,
        width: node.naturalWidth, height: node.naturalHeight,
        ratio: node.naturalWidth / node.naturalHeight, renderedRatio: bounds.width / bounds.height,
        fits: bounds.left >= container.left - 1 && bounds.right <= container.right + 1 &&
          bounds.top >= container.top - 1 && bounds.bottom <= container.bottom + 1,
      };
    });
    sources.add(picture.source);
    assert.ok(picture.complete && picture.width > 0 && picture.height > 0, `Product picture must load: ${picture.source}, ${label}`);
    assert.ok(picture.alt.trim(), `Product picture must have descriptive alternative text: ${picture.source}`);
    assert.ok(picture.fits && Math.abs(picture.ratio - picture.renderedRatio) < .01,
      `Product picture must fit its container without stretching or cropping: ${picture.source}, ${label}`);
  }
  assert.ok(sources.size >= 4, `Product pictures must show distinct real views: ${label}`);
};
const componentContent = {
  m1: { title: /候选证明/, description: /隔离工作区.*构造和修复 Lean 候选/, input: /题目.*模型会话/, output: /候选记录.*证明/ },
  m2: { title: /诊断/, description: /Lean 诊断.*独立验收/, input: /候选源码.*检查环境/, output: /源码摘要.*检查与诊断/ },
  m3: { title: /下一步/, description: /就绪任务.*预算约束/, input: /研究状态.*共享预算/, output: /下一步操作.*有序就绪任务/ },
  m4: { title: /证据/, description: /失败记录.*检索策略/, input: /题目.*可见证据/, output: /来源身份.*上下文包/ },
  m5: { title: /分工与交接/, description: /任务分配.*独立审阅/, input: /就绪任务.*路线约束/, output: /工作区配置.*审阅分配/ },
};
const checkMobileComponentGrid = async (page, label) => {
  const result = await page.locator('.component-tabs').evaluate(list => {
    const bounds = list.getBoundingClientRect();
    const tabs = [...list.querySelectorAll('[data-component]')];
    return { display: getComputedStyle(list).display, count: tabs.length,
      fits: list.scrollWidth <= list.clientWidth + 1 && tabs.every(tab => {
        const box = tab.getBoundingClientRect(), title = tab.querySelector('strong').getBoundingClientRect();
        return box.width > 0 && box.height > 0 && box.left >= bounds.left - 1 && box.right <= bounds.right + 1 &&
          box.top >= bounds.top - 1 && box.bottom <= bounds.bottom + 1 &&
          title.left >= box.left - 1 && title.right <= box.right + 1;
      }) };
  });
  assert.equal(result.display, 'grid', `Mobile components must use a complete grid: ${label}`);
  assert.equal(result.count, 5);
  assert.ok(result.fits, `All five mobile component tabs and labels must fit without sideways scrolling: ${label}`);
};
try {
  const page = await browser.newPage({ viewport: { width: 1440, height: 1000 }, reducedMotion: 'reduce' });
  trackErrors(page);
  await page.addInitScript(() => {
    Object.defineProperty(navigator, 'clipboard', { configurable: true, value: {
      writeText: async text => { if (window.testClipboardFailure) throw new Error('denied'); window.testClipboard = text; },
    } });
  });
  await page.goto(url);
  await page.waitForFunction(() => document.documentElement.dataset.landingReady === 'true');
  await page.evaluate(() => document.fonts.ready);
  assert.ok(await page.evaluate(() => [...document.fonts].some(font => font.family.replace(/["']/g, '') === 'Hanken Grotesk' && font.status === 'loaded')), 'The local preview must load the bundled Hanken Grotesk font');
  assert.match(await page.title(), /TheoremOS/);
  assert.equal(await page.locator('h1').count(), 1);
  await checkWorkbench(page, '1440px local preview');
  await checkScreenshotPreview(page, 1440);
  await checkArchivePreview(page, 1440);
  await checkProductImages(page, '1440px local preview');
  assert.equal(await page.locator('#motion-toggle, .manifold').count(), 0);
  assert.equal(await page.locator('#demo').evaluate(demo => demo.closest('.hero-shell') === null), true,
    'The archived replay must be a separate section from the workbench hero');
  const hostingFaq = page.locator('.faq-list details').filter({ hasText: 'GitHub Pages' });
  assert.equal(await hostingFaq.count(), 1);
  await hostingFaq.locator('summary').click();
  const boundary = await hostingFaq.innerText();
  assert.match(boundary, /GitHub Pages/);
  assert.match(boundary, /静态/);
  assert.match(boundary, /Linux|本地/);
  await hostingFaq.locator('summary').click();
  assert.equal(await page.locator('.proof-table tbody .proof-row[data-accepted-proof]').count(), accepted.length);
  assert.equal(await page.locator('.proof-count').innerText(), String(accepted.length));
  for (const record of accepted) {
    const card = page.locator(`[data-accepted-proof="${record.id}"]`);
    assert.equal(await card.locator('.proof-credit').innerText(), record.model);
    assert.equal(await card.locator('.official-link').getAttribute('href'), record.official.resultUrl);
    assert.equal(await card.locator('a[data-proof-source]').getAttribute('href'), `archive.html#proof=${record.id}&tab=source`);
  }
  assert.match(await page.locator('.proof-provenance').innerText(), /前身 DeepScientist/);
  assert.match(await page.locator('.receipt-status').innerText(), new RegExp(replayEvidence.status));
  for (const target of replayEvidence.targets) assert.ok((await page.locator('.receipt-targets').innerText()).includes(target.theorem));
  assert.match(await page.locator('.replay-badge').innerText(), /预设回放 · 不调用模型/);
  for (const id of ['candidate', 'feedback', 'repair', 'verified']) {
    await page.locator(`#demo-${id}`).click();
    assert.equal(await page.locator(`#demo-${id}`).getAttribute('aria-selected'), 'true');
    assert.equal(await page.locator(`#stage-${id}`).isVisible(), true);
    assert.equal(await page.locator('.replay-panel:visible').count(), 1);
    assert.match(await page.locator('.receipt-status').innerText(), /evaluated_passed/);
  }
  assert.match(await page.locator('#stage-candidate').textContent(), /0 \+ n = n := by rfl/);
  assert.match(await page.locator('#stage-repair').textContent(), /by exact Nat.zero_add n/);
  await page.locator('#demo-verified').focus();
  await page.keyboard.press('ArrowRight');
  assert.equal(await page.locator('#demo-candidate').getAttribute('aria-selected'), 'true');
  await page.keyboard.press('End');
  assert.equal(await page.locator('#demo-verified').getAttribute('aria-selected'), 'true');
  // Verify local navigation and packaged resources, including file:// previews.
  const localPaths = await page.locator('a[href], img[src], script[src], link[href]').evaluateAll(nodes => nodes.map(node => node.getAttribute('href') ?? node.getAttribute('src')).filter(Boolean));
  for (const relative of localPaths) {
    if (relative.startsWith('#') || /^[a-z]+:/i.test(relative)) continue;
    assert.ok(fs.existsSync(path.join(site, relative.split('#')[0])), `Missing local resource: ${relative}`);
  }
  assert.ok(fs.existsSync(path.join(site, 'assets/social-preview.png')));

  for (const id of ['m1', 'm2', 'm3', 'm4', 'm5']) {
    await page.locator(`#tab-${id}`).click();
    assert.equal(await page.locator(`#tab-${id}`).getAttribute('aria-selected'), 'true');
    assert.equal(await page.locator('#component-panel').getAttribute('aria-labelledby'), `tab-${id}`);
    assert.match(await page.locator('#module-kicker').innerText(), new RegExp(id.toUpperCase()));
    for (const [field, wording] of Object.entries(componentContent[id])) {
      assert.match(await page.locator(`#module-${field}`).innerText(), wording, `Component ${id} must show its own ${field}`);
    }
    assert.match(await page.locator('.independent-check').innerText(), /完整原题.*独立 Lean.*验收/);
    await checkWidth(page, `component ${id}`);
  }
  await page.locator('#tab-m5').focus();
  await page.keyboard.press('ArrowDown');
  assert.equal(await page.locator('#tab-m1').getAttribute('aria-selected'), 'true');
  await page.keyboard.press('End');
  assert.equal(await page.locator('#tab-m5').getAttribute('aria-selected'), 'true');
  await page.keyboard.press('Home');
  assert.equal(await page.locator('#tab-m1').getAttribute('aria-selected'), 'true');
  await page.locator('#tab-m3').click();

  assert.deepEqual(await page.locator('[data-command]').evaluateAll(tabs => tabs.map(tab => ({
    id: tab.dataset.command, label: tab.textContent.trim(),
  }))), [
    { id: 'workbench', label: '网页工作台' },
    { id: 'install', label: 'CLI 安装' },
    { id: 'replay', label: '预设回放' },
  ]);
  await checkCommand(page, 'workbench');
  await page.getByRole('button', { name: '复制部署工作台命令' }).click();
  const workbenchCommand = await page.evaluate(() => window.testClipboard);
  assert.deepEqual(workbenchCommand.split(/\r?\n/).map(line => line.trim()).filter(Boolean), [
    'git clone https://github.com/LikC1606/theorem-os.git',
    'cd theorem-os',
    'docker compose -f apps/web/compose.yml build worker web',
    'docker compose -f apps/web/compose.yml up -d web',
    'docker compose -f apps/web/compose.yml ps',
  ]);
  assert.equal(workbenchCommand, await page.locator('#workbench-panel pre code').textContent());
  await page.locator('#command-install').click();
  await checkCommand(page, 'install');
  await page.getByRole('button', { name: '复制获取项目命令' }).click();
  assert.match(await page.evaluate(() => window.testClipboard), /^git clone https:\/\/github.com\/LikC1606\/theorem-os.git\ncd theorem-os\nbun install --frozen-lockfile$/);
  await page.getByRole('button', { name: '下一步', exact: true }).click();
  assert.equal(await page.locator('#replay-panel').isVisible(), true);
  await page.getByRole('button', { name: '复制本地回放命令' }).click();
  assert.match(await page.evaluate(() => window.testClipboard), /elan toolchain install leanprover\/lean4:v4.33.0/);
  assert.match(await page.evaluate(() => window.testClipboard), /export THEOREMOS_CASE="\$PWD\/\.\.\/theorem-os-runs\/first-replay"/);
  assert.match(await page.evaluate(() => window.testClipboard), /math example replay --dir "\$THEOREMOS_CASE"/);
  await page.evaluate(() => { window.testClipboardFailure = true; });
  await page.getByRole('button', { name: '复制本地回放命令' }).click();
  await page.waitForFunction(() => document.querySelector('#toast').textContent.startsWith('未能复制'));
  await page.evaluate(() => { window.testClipboardFailure = false; });
  await page.locator('#command-replay').focus();
  await page.keyboard.press('ArrowRight');
  await checkCommand(page, 'workbench');
  await page.keyboard.press('ArrowRight');
  await checkCommand(page, 'install');
  await page.keyboard.press('End');
  await checkCommand(page, 'replay');
  assert.equal(await page.locator('#command-replay').evaluate(tab => tab === document.activeElement), true);
  await page.keyboard.press('Home');
  await checkCommand(page, 'workbench');

  const summary = page.locator('.faq-list summary').first();
  await summary.click();
  assert.equal(await page.locator('.faq-list details').first().getAttribute('open'), '');
  await summary.click();
  await page.locator('.archive-image-link').scrollIntoViewIfNeeded();
  await page.waitForFunction(() => document.querySelector('.archive-image-link img').complete);
  await page.evaluate(() => { document.querySelector('#toast').hidden = true; window.scrollTo(0, 0); });
  await page.screenshot({ path: path.join(output, 'landing-desktop.png'), fullPage: true });
  await page.screenshot({ path: path.join(output, 'landing-hero.png') });

  for (const viewport of [{ width: 1920, height: 1080 }, { width: 768, height: 1024 }, { width: 390, height: 844 }, { width: 320, height: 740 }]) {
    await page.setViewportSize(viewport);
    await page.goto(url);
    await page.waitForFunction(() => document.documentElement.dataset.landingReady === 'true');
    await page.evaluate(() => document.fonts.ready);
    await checkWorkbench(page, `${viewport.width}px homepage`);
    await checkScreenshotPreview(page, viewport.width);
    await checkArchivePreview(page, viewport.width);
    await checkProductImages(page, `${viewport.width}px homepage`);
    await checkCommand(page, 'workbench');
    await checkWidth(page, `${viewport.width}px homepage`);
    for (const id of ['feedback', 'repair', 'verified']) {
      await page.locator(`#demo-${id}`).click();
      await checkWidth(page, `${viewport.width}px replay ${id}`);
    }
    if (viewport.width <= 390) {
      const receipt = await page.locator('.replay-receipt').boundingBox();
      const editor = await page.locator('.replay-editor').boundingBox();
      assert.ok(receipt && editor && receipt.y + receipt.height <= editor.y + 1,
        `The archived receipt must precede the editor at ${viewport.width}px`);
    }
    assert.ok(await page.locator('.brand img').first().evaluate(image => image.complete && image.naturalWidth > 0));
    await page.locator('#tab-m2').click();
    await checkWidth(page, `${viewport.width}px M2`);
    if (viewport.width <= 390) {
      await page.locator('#tab-m2').focus();
      await page.keyboard.press('End');
      const selected = await page.locator('#tab-m5').evaluate(node => {
        const bounds = node.getBoundingClientRect(), parent = node.parentElement.getBoundingClientRect();
        return { active: node.getAttribute('aria-selected'), visible: bounds.left >= parent.left - 1 && bounds.right <= parent.right + 1 };
      });
      assert.equal(selected.active, 'true');
      assert.ok(selected.visible, 'Keyboard selection must reveal the active mobile component tab');
      await checkMobileComponentGrid(page, `${viewport.width}px homepage`);
    }
    assert.equal(await page.locator('.extension-example').getAttribute('open'), null);
    await page.locator('.extension-example > summary').click();
    assert.equal(await page.locator('.extension-code').isVisible(), true);
    assert.match(await page.locator('.extension-code').innerText(), /ready: goalsFirstResearchTasks/);
    await checkWidth(page, `${viewport.width}px expanded source example`);
    await page.locator('.extension-example > summary').click();
    await page.locator('#command-replay').click();
    await checkWidth(page, `${viewport.width}px commands`);
    await page.locator('#command-workbench').click();
    await checkCommand(page, 'workbench');
    await checkWidth(page, `${viewport.width}px workbench deployment commands`);
    await page.locator('#command-install').click();
    await checkWidth(page, `${viewport.width}px CLI installation commands`);
    await page.locator('#command-workbench').click();
    await page.locator('#tab-m3').click();
    await page.locator('.archive-image-link').scrollIntoViewIfNeeded();
    await page.waitForFunction(() => document.querySelector('.archive-image-link img').complete);
    await page.evaluate(() => window.scrollTo(0, 0));
    await page.screenshot({ path: path.join(output, `landing-${viewport.width}.png`), fullPage: true });
    await page.screenshot({ path: path.join(output, `landing-${viewport.width}-hero.png`) });
  }
  await page.setViewportSize({ width: 390, height: 844 });
  await page.goto(url);
  await page.getByRole('button', { name: '打开导航' }).click();
  assert.equal(await page.locator('#mobile-nav').isVisible(), true);
  await page.keyboard.press('Escape');
  assert.equal(await page.locator('#mobile-nav').isVisible(), false);
  assert.equal(await page.getByRole('button', { name: '打开导航' }).evaluate(button => button === document.activeElement), true);
  await page.getByRole('button', { name: '打开导航' }).click();
  await page.locator('#mobile-nav a[href="#components"]').click();
  assert.equal(await page.locator('#mobile-nav').isVisible(), false);
  assert.equal(new URL(page.url()).hash, '#components');
  assert.equal(await page.locator('.component-tabs').getAttribute('aria-orientation'), 'horizontal');
  await page.getByRole('button', { name: '打开导航' }).click();
  await page.setViewportSize({ width: 1440, height: 1000 });
  await page.waitForFunction(() => document.querySelector('#mobile-nav').hidden);
  assert.equal(await page.locator('#mobile-nav').isVisible(), false);

  // The proof row opens the exact archived source, and the archive returns home.
  await page.locator('[data-accepted-proof="annals_rademacher_enflo_type"] a[data-proof-source]').click();
  await page.waitForSelector('.source-code');
  assert.match(await page.locator('.is-declaration').innerText(), /theorem theorem_1_1/);
  await page.getByRole('link', { name: 'TheoremOS 首页' }).click();
  assert.equal(new URL(page.url()).pathname, new URL(url).pathname);

  const noJS = await browser.newPage({ javaScriptEnabled: false, viewport: { width: 1440, height: 1000 } });
  trackErrors(noJS);
  await noJS.goto(url);
  assert.equal(await noJS.locator('.proof-table tbody .proof-row[data-accepted-proof]').count(), accepted.length);
  await checkWorkbench(noJS, 'JavaScript-disabled homepage');
  await checkProductImages(noJS, 'JavaScript-disabled homepage');
  assert.equal(await noJS.locator('.workbench-image-link').getAttribute('href'), 'assets/workbench-full-desktop.png');
  assert.ok(fs.existsSync(path.join(site, 'assets/workbench-full-desktop.png')));
  await noJS.locator('.extension-example > summary').click();
  assert.equal(await noJS.locator('.extension-code').isVisible(), true);
  await checkCommand(noJS, 'workbench');
  assert.equal(await noJS.locator('[data-accepted-proof] h3 a').first().isVisible(), true);
  await noJS.close();

  // Test the repository subpath used by GitHub Pages, with real HTTP resource loading.
  server = http.createServer((request, response) => {
    const pathname = decodeURIComponent(new URL(request.url, 'http://127.0.0.1').pathname);
    if (!pathname.startsWith('/theorem-os/')) { response.writeHead(404).end(); return; }
    const file = path.resolve(site, pathname.slice('/theorem-os/'.length) || 'index.html');
    if (!file.startsWith(site + path.sep) || !fs.existsSync(file) || !fs.statSync(file).isFile()) { response.writeHead(404).end(); return; }
    const mime = { '.html': 'text/html', '.js': 'text/javascript', '.css': 'text/css', '.json': 'application/json', '.png': 'image/png', '.svg': 'image/svg+xml', '.woff2': 'font/woff2', '.txt': 'text/plain' };
    response.writeHead(200, { 'Content-Type': mime[path.extname(file)] ?? 'application/octet-stream' });
    fs.createReadStream(file).pipe(response);
  });
  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  const hosted = `http://127.0.0.1:${server.address().port}/theorem-os/`;
  await page.goto(hosted);
  await page.waitForFunction(() => document.documentElement.dataset.landingReady === 'true');
  await page.evaluate(() => document.fonts.ready);
  assert.ok(await page.evaluate(() => [...document.fonts].some(font => font.family.replace(/["']/g, '') === 'Hanken Grotesk' && font.status === 'loaded')), 'The Pages subpath must load the bundled Hanken Grotesk font');
  await checkWorkbench(page, 'GitHub Pages repository subpath');
  await checkProductImages(page, 'GitHub Pages repository subpath');
  await checkScreenshotPreview(page, 1440);
  await page.locator('#tab-m4').click();
  assert.match(await page.locator('#module-kicker').innerText(), /M4/);
  assert.match(await page.locator('#module-description').innerText(), componentContent.m4.description);
  await page.locator('.hero-actions a[href="archive.html"]').click();
  await page.waitForSelector('.proof-row');
  assert.equal(await page.locator('.proof-row').count(), catalog.records.length);
  assert.deepEqual(errors, []);
  console.log('Landing checks passed: four real product pictures, responsive workbench and uncropped archive screenshots, modal zoom, panning, focus restoration and closing, archived replay and mobile receipt order, verified proof-table links and attribution, complete mobile component grid and changing interface content, expandable source example, command copying and failure feedback, mobile navigation, JavaScript-disabled content, file preview, bundled Hanken Grotesk, Pages subpath, and 5 viewport sizes.');
} finally {
  if (server) await new Promise(resolve => server.close(resolve));
  await browser.close();
}
