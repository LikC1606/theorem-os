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
try {
  const page = await browser.newPage({ viewport: { width: 1440, height: 1000 }, reducedMotion: 'reduce' });
  trackErrors(page);
  await page.addInitScript(() => {
    Object.defineProperty(navigator, 'clipboard', { configurable: true, value: {
      writeText: async text => { if (window.testClipboardFailure) throw new Error('denied'); window.testClipboard = text; },
    } });
  });
  await page.goto(url);
  await page.waitForSelector('.release-pill svg.lucide');
  await page.evaluate(() => document.fonts.ready);
  assert.ok(await page.evaluate(() => [...document.fonts].some(font => font.family === 'Inter' && font.status === 'loaded')), 'The local preview must load the bundled font');
  assert.match(await page.title(), /TheoremOS/);
  assert.equal(await page.locator('h1').count(), 1);
  await checkWorkbench(page, '1440px local preview');
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
  assert.equal(await page.locator('.proof-card').count(), accepted.length);
  assert.equal(await page.locator('.proof-count').innerText(), String(accepted.length).padStart(2, '0'));
  for (const record of accepted) {
    const card = page.locator(`[data-accepted-proof="${record.id}"]`);
    assert.equal(await card.locator('.proof-credit').innerText(), record.model);
    assert.equal(await card.locator('.official-link').getAttribute('href'), record.official.resultUrl);
    assert.equal(await card.locator('.proof-card-footer a').first().getAttribute('href'), `archive.html#proof=${record.id}&tab=source`);
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
    assert.equal(await page.locator('.diagram-node.is-active').getAttribute('data-diagram'), id);
    assert.match(await page.locator('#module-kicker').innerText(), new RegExp(id.toUpperCase()));
    assert.match(await page.locator('.independent-check').innerText(), /完整原题 · 独立 Lean 验收/);
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
    await page.waitForSelector('.release-pill svg.lucide');
    await page.evaluate(() => document.fonts.ready);
    await checkWorkbench(page, `${viewport.width}px homepage`);
    await checkCommand(page, 'workbench');
    await checkWidth(page, `${viewport.width}px homepage`);
    for (const artwork of await page.locator('.proof-art > svg, .proof-art > .type-formula, .proof-art > .unit-formula').all()) {
      const fits = await artwork.evaluate(node => {
        const bounds = node.getBoundingClientRect(), parent = node.parentElement.getBoundingClientRect();
        return bounds.left >= parent.left - 1 && bounds.right <= parent.right + 1;
      });
      assert.ok(fits, `Proof artwork must remain complete at ${viewport.width}px`);
    }
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

  // The promotional card opens the exact archived source, and the archive returns home.
  await page.locator('[data-accepted-proof="annals_rademacher_enflo_type"] .proof-card-footer a').first().click();
  await page.waitForSelector('.source-code');
  assert.match(await page.locator('.is-declaration').innerText(), /theorem theorem_1_1/);
  await page.getByRole('link', { name: 'TheoremOS 首页' }).click();
  assert.equal(new URL(page.url()).pathname, new URL(url).pathname);

  const noJS = await browser.newPage({ javaScriptEnabled: false, viewport: { width: 1440, height: 1000 } });
  trackErrors(noJS);
  await noJS.goto(url);
  assert.equal(await noJS.locator('.proof-card').count(), accepted.length);
  await checkWorkbench(noJS, 'JavaScript-disabled homepage');
  await checkCommand(noJS, 'workbench');
  assert.equal(await noJS.locator('.proof-card h3 a').first().isVisible(), true);
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
  await page.evaluate(() => document.fonts.ready);
  assert.ok(await page.evaluate(() => [...document.fonts].some(font => font.family === 'Inter' && font.status === 'loaded')), 'The Pages subpath must load the bundled font');
  await checkWorkbench(page, 'GitHub Pages repository subpath');
  await page.locator('#tab-m4').click();
  assert.match(await page.locator('#module-kicker').innerText(), /CONTEXT/);
  await page.locator('.hero-actions a[href="archive.html"]').click();
  await page.waitForSelector('.proof-row');
  assert.equal(await page.locator('.proof-row').count(), catalog.records.length);
  assert.deepEqual(errors, []);
  console.log('Landing checks passed: real workbench screenshots and responsive sources in the first viewport, archived replay and mobile receipt order, verified proof links and attribution, component and command tabs with keyboard controls, deployment command copying and failure feedback, mobile navigation, static hosting boundaries, JavaScript-disabled content, file preview, Pages subpath, and 5 viewport sizes.');
} finally {
  if (server) await new Promise(resolve => server.close(resolve));
  await browser.close();
}
