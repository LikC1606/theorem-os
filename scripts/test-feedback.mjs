import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import http from 'node:http';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { chromium } from 'playwright';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const site = path.join(root, 'out/site');
const url = pathToFileURL(path.join(site, 'feedback.html')).href;
const output = path.join(root, 'out/feedback-checks');
const issueDestination = 'https://github.com/LikC1606/theorem-os/issues/new';
fs.mkdirSync(output, { recursive: true });
const errors = [];
const unexpectedExternalRequests = [];
const interceptedIssueNavigations = [];
let allowIssueNavigation = false;
let server;
const browser = await chromium.launch();

const guardContext = async context => {
  context.on('page', page => {
    page.on('pageerror', error => errors.push(error.message));
    page.on('console', message => {
      if (['warning', 'error'].includes(message.type())) errors.push(message.text());
    });
    page.on('requestfailed', request => errors.push(`${request.url()}: ${request.failure()?.errorText}`));
  });
  await context.route(/^https?:\/\//, async route => {
    const destination = new URL(route.request().url());
    if (destination.hostname === '127.0.0.1') {
      await route.continue();
      return;
    }
    if (allowIssueNavigation && `${destination.origin}${destination.pathname}` === issueDestination) {
      interceptedIssueNavigations.push(destination.href);
      await route.fulfill({ contentType: 'text/html; charset=utf-8', body: '<!doctype html><title>Intercepted feedback destination</title><p>Local test response.</p>' });
      return;
    }
    unexpectedExternalRequests.push(destination.href);
    await route.abort();
  });
};
const ready = async page => {
  await page.waitForFunction(() => document.documentElement.dataset.feedbackReady === 'true');
  await page.evaluate(() => document.fonts.ready);
  assert.equal(await page.locator('#feedback-form').isVisible(), true);
  assert.equal(await page.locator('#feedback-fallback').isVisible(), false);
};
const checkWidth = async (page, label) => assert.ok(
  await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth + 1), `Horizontal overflow: ${label}`,
);
const checkReviewBounds = async (page, label) => {
  await checkWidth(page, label);
  const bounds = await page.locator('#feedback-review').boundingBox();
  const viewport = page.viewportSize();
  assert.ok(bounds && bounds.x >= 0 && bounds.y >= 0 && bounds.x + bounds.width <= viewport.width + 1 &&
    bounds.y + bounds.height <= viewport.height + 1, `Feedback review must fit the viewport: ${label}`);
  assert.ok(await page.locator('#feedback-review').evaluate(dialog => dialog.scrollWidth <= dialog.clientWidth + 1),
    `Feedback review must not overflow horizontally: ${label}`);
};
const submit = async page => {
  await page.locator('#feedback-preview').click();
  assert.equal(await page.locator('#feedback-review').isVisible(), true);
  assert.deepEqual(await page.locator('#feedback-markdown').evaluate(textarea => ({
    start: textarea.selectionStart, end: textarea.selectionEnd, top: textarea.scrollTop, left: textarea.scrollLeft,
  })), { start: 0, end: 0, top: 0, left: 0 }, 'Each review must open at the beginning of the complete feedback');
};
const closeReview = async (page, escape = false) => {
  if (escape) await page.keyboard.press('Escape');
  else await page.locator('#feedback-review-close').click();
  await page.waitForFunction(() => !document.querySelector('#feedback-review').open);
  assert.equal(await page.locator('#feedback-preview').evaluate(button => button === document.activeElement), true,
    'Closing the review must return keyboard focus to the preview button');
};
const readDestination = async page => {
  const destination = new URL(await page.locator('#feedback-github').getAttribute('href'));
  assert.equal(`${destination.origin}${destination.pathname}`, issueDestination);
  assert.equal(destination.hash, '');
  assert.equal(await page.locator('#feedback-github').getAttribute('target'), '_blank');
  assert.match(await page.locator('#feedback-github').getAttribute('rel'), /noreferrer/);
  return destination;
};

try {
  const context = await browser.newContext({ viewport: { width: 1440, height: 1000 }, reducedMotion: 'reduce' });
  await guardContext(context);
  await context.addInitScript(() => {
    Object.defineProperty(navigator, 'clipboard', { configurable: true, value: {
      writeText: async text => {
        if (window.feedbackClipboardFailure) throw new Error('Clipboard denied for test');
        window.feedbackClipboard = text;
      },
    } });
  });
  const page = await context.newPage();
  await page.goto(url);
  await ready(page);
  assert.match(await page.title(), /TheoremOS.*反馈/);
  assert.equal(await page.locator('h1').count(), 1);
  assert.equal(await page.locator('#feedback-export-status').getAttribute('role'), 'status');
  assert.match(await page.locator('.feedback-destination').innerText(), /公开.*GitHub Issues/s);
  assert.match(await page.locator('.feedback-destination').innerText(), /登录 GitHub/);
  assert.equal(await page.locator('#feedback-markdown').getAttribute('readonly'), '');
  assert.ok(await page.locator('.brand img').evaluate(image => image.complete && image.naturalWidth > 0));
  await page.locator('.feedback-product img').evaluate(image => image.decode());
  await checkWidth(page, 'initial desktop');
  await page.screenshot({ path: path.join(output, 'feedback-desktop.png'), fullPage: true });

  // Native constraints must reject both missing values and whitespace-only feedback.
  await page.locator('#feedback-preview').click();
  assert.equal(await page.locator('#feedback-review').isVisible(), false);
  assert.equal(await page.locator('#feedback-area').evaluate(select => select === document.activeElement), true);
  await page.locator('#feedback-area').selectOption('workbench');
  await page.locator('#feedback-subject').fill('   ');
  await page.locator('#feedback-description').fill(' \n  ');
  await page.locator('#feedback-preview').click();
  assert.equal(await page.locator('#feedback-review').isVisible(), false);
  assert.equal(await page.locator('#feedback-subject').evaluate(input => input === document.activeElement && !input.validity.valid), true);

  const subject = '证明反馈 & emoji 🧪 #1 + 100%';
  const description = '复现步骤：\n1. 输入 A & B + C #tag 100%\n\n```lean\nexample : True := by trivial\n```\n</textarea><script>window.feedbackInjected = true</script>';
  const environment = 'Linux / Chromium & Mathlib #v1 + 100%';
  await page.locator('#feedback-subject').fill(subject);
  await page.locator('#feedback-preview').click();
  assert.equal(await page.locator('#feedback-review').isVisible(), false);
  assert.equal(await page.locator('#feedback-description').evaluate(input => input === document.activeElement && !input.validity.valid), true);
  await page.locator('#feedback-description').fill(description);
  await page.locator('#feedback-environment').fill(environment);
  assert.equal(await page.locator('#feedback-form').evaluate(form => form.checkValidity()), true,
    'Correcting whitespace-only values must clear the custom validation errors');
  await submit(page);
  await checkReviewBounds(page, 'special-character feedback');
  const destination = await readDestination(page);
  assert.deepEqual([...destination.searchParams.keys()].sort(), ['body', 'title']);
  assert.equal(destination.searchParams.get('title'), `[Bug] ${subject}`);
  const body = destination.searchParams.get('body');
  assert.ok(body.includes(description), 'The Issue body must preserve Unicode, Markdown, and URL punctuation');
  assert.ok(body.includes(environment));
  assert.ok(body.includes('网页工作台'));
  assert.equal(await page.locator('#feedback-markdown').inputValue(), `# [Bug] ${subject}\n\n${body}\n`);
  assert.equal(await page.evaluate(() => window.feedbackInjected), undefined, 'Feedback must stay inert text');
  assert.equal(await page.locator('#feedback-review script').count(), 0);
  assert.match(await page.locator('#feedback-review-note').innerText(), /确认后.*公开发布/);
  await page.locator('#feedback-copy').click();
  assert.equal(await page.evaluate(() => window.feedbackClipboard), await page.locator('#feedback-markdown').inputValue());
  assert.match(await page.locator('#feedback-export-status').innerText(), /已复制/);
  await page.locator('#feedback-review-close').focus();
  await page.keyboard.press('Tab');
  assert.equal(await page.locator('#feedback-review').evaluate(dialog => dialog.contains(document.activeElement)), true,
    'The native modal must contain keyboard focus');
  await closeReview(page, true);

  // Radio arrow keys must update both the displayed guidance and generated Issue type.
  await page.locator('input[name="feedback-kind"][value="bug"]').focus();
  await page.keyboard.press('ArrowRight');
  assert.equal(await page.locator('input[value="feature"]').isChecked(), true);
  assert.match(await page.locator('#feedback-description-hint').innerText(), /使用场景/);
  await submit(page);
  assert.equal((await readDestination(page)).searchParams.get('title'), `[Feature] ${subject}`);
  assert.match(await page.locator('#feedback-markdown').inputValue(), /### 反馈类型\n功能建议/);
  await closeReview(page);
  await page.locator('input[name="feedback-kind"][value="feature"]').focus();
  await page.keyboard.press('ArrowRight');
  assert.equal(await page.locator('input[value="question"]').isChecked(), true);
  assert.match(await page.locator('#feedback-description-hint').innerText(), /疑问/);
  await page.locator('#feedback-environment').fill('');
  await submit(page);
  assert.equal((await readDestination(page)).searchParams.get('title'), `[Question] ${subject}`);
  assert.doesNotMatch(await page.locator('#feedback-markdown').inputValue(), /### 环境与版本/);
  await closeReview(page);

  // Encoded Unicode can exceed a URL's practical limit while the form is still valid.
  const longDescription = '完整反馈 🧪 & + # %\n'.repeat(400);
  assert.ok(longDescription.length < 10000);
  await page.locator('#feedback-description').fill(longDescription);
  await submit(page);
  const longDestination = await readDestination(page);
  assert.equal(longDestination.searchParams.has('body'), false);
  assert.equal(longDestination.searchParams.get('title'), `[Question] ${subject}`);
  assert.match(await page.locator('#feedback-review-note').innerText(), /内容较长.*复制或下载.*粘贴/);
  const fullMarkdown = await page.locator('#feedback-markdown').inputValue();
  assert.ok(fullMarkdown.includes(longDescription.trim()), 'The long-feedback fallback must preserve every line');
  await page.evaluate(() => { window.feedbackClipboardFailure = true; });
  await page.locator('#feedback-copy').click();
  await page.waitForFunction(() => document.querySelector('#feedback-export-status').textContent.includes('未能自动复制'));
  assert.deepEqual(await page.locator('#feedback-markdown').evaluate(textarea => ({
    focused: textarea === document.activeElement, start: textarea.selectionStart, end: textarea.selectionEnd,
  })), { focused: true, start: 0, end: fullMarkdown.length });
  const downloadPromise = page.waitForEvent('download');
  await page.locator('#feedback-download').click();
  const download = await downloadPromise;
  assert.equal(download.suggestedFilename(), 'theoremos-feedback.md');
  assert.equal(fs.readFileSync(await download.path(), 'utf8'), fullMarkdown);
  assert.match(await page.locator('#feedback-export-status').innerText(), /下载/);
  await page.evaluate(() => { window.feedbackClipboardFailure = false; });
  await closeReview(page);

  await page.locator('#feedback-description').fill(description);
  for (const viewport of [{ width: 1440, height: 1000 }, { width: 768, height: 1024 }, { width: 390, height: 844 }, { width: 320, height: 740 }]) {
    await page.setViewportSize(viewport);
    await page.evaluate(() => window.scrollTo(0, 0));
    await checkWidth(page, `${viewport.width}px page`);
    const optionsFit = await page.locator('.feedback-kind-options').evaluate(options => {
      const parent = options.getBoundingClientRect();
      return [...options.querySelectorAll('label > span')].every(option => {
        const bounds = option.getBoundingClientRect();
        return bounds.left >= parent.left - 1 && bounds.right <= parent.right + 1 && option.scrollWidth <= option.clientWidth + 1;
      });
    });
    assert.ok(optionsFit, `All feedback categories must fit at ${viewport.width}px`);
    await page.screenshot({ path: path.join(output, `feedback-${viewport.width}.png`), fullPage: true });
    await submit(page);
    await checkReviewBounds(page, `${viewport.width}px review`);
    await page.screenshot({ path: path.join(output, `feedback-review-${viewport.width}.png`) });
    await closeReview(page);
  }
  assert.deepEqual(unexpectedExternalRequests, [], 'Composing, previewing, copying, and downloading must not contact external services');
  assert.deepEqual(interceptedIssueNavigations, []);

  // Exercise the external link through a local response; never create an actual Issue.
  await submit(page);
  const expectedNavigation = (await readDestination(page)).href;
  allowIssueNavigation = true;
  const popupPromise = page.waitForEvent('popup');
  await page.locator('#feedback-github').click();
  const popup = await popupPromise;
  await popup.waitForLoadState('domcontentloaded');
  assert.equal(await popup.title(), 'Intercepted feedback destination');
  assert.equal(popup.url(), expectedNavigation);
  assert.deepEqual(interceptedIssueNavigations, [expectedNavigation]);
  await popup.close();
  allowIssueNavigation = false;
  await closeReview(page);

  // Test resource loading and relative navigation under the GitHub Pages repository path.
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
  await page.setViewportSize({ width: 1440, height: 1000 });
  await page.goto(`${hosted}feedback.html`);
  await ready(page);
  await page.getByRole('link', { name: 'TheoremOS 首页' }).click();
  await page.waitForFunction(() => document.documentElement.dataset.landingReady === 'true');
  assert.equal(page.url(), `${hosted}index.html`);
  assert.ok(await page.locator('.desktop-nav a[href="feedback.html"]').isVisible());
  assert.ok(await page.locator('.site-footer a[href="feedback.html"]').isVisible());
  await page.locator('.desktop-nav a[href="feedback.html"]').click();
  await ready(page);
  await page.locator('.feedback-nav a[href="archive.html"]').click();
  await page.waitForSelector('.proof-row');
  assert.equal(page.url().split('#')[0], `${hosted}archive.html`);
  await page.locator('.header-links a[href="feedback.html"]').click();
  await ready(page);
  assert.equal(page.url(), `${hosted}feedback.html`);
  await page.setViewportSize({ width: 390, height: 844 });
  await page.goto(hosted);
  await page.waitForFunction(() => document.documentElement.dataset.landingReady === 'true');
  await page.getByRole('button', { name: '打开导航' }).click();
  await page.locator('#mobile-nav a[href="feedback.html"]').click();
  await ready(page);
  await checkWidth(page, 'GitHub Pages feedback subpath');

  const noJSContext = await browser.newContext({ javaScriptEnabled: false, viewport: { width: 390, height: 844 } });
  await guardContext(noJSContext);
  const noJS = await noJSContext.newPage();
  for (const fallbackUrl of [url, `${hosted}feedback.html`]) {
    await noJS.goto(fallbackUrl);
    assert.equal(await noJS.locator('#feedback-form').isVisible(), false);
    assert.equal(await noJS.locator('#feedback-fallback').isVisible(), true);
    assert.equal(await noJS.locator('#feedback-fallback a').getAttribute('href'), issueDestination);
    assert.equal(await noJS.locator('#feedback-fallback a').isVisible(), true);
    await checkWidth(noJS, `JavaScript-disabled ${fallbackUrl}`);
  }
  await noJS.screenshot({ path: path.join(output, 'feedback-no-script.png'), fullPage: true });
  assert.deepEqual(unexpectedExternalRequests, []);
  assert.deepEqual(errors, []);
  console.log('Feedback checks passed: form constraints and recovery, Unicode and Markdown preservation, inert preview, radio keyboard controls, modal focus and bounds, copy success and failure, lossless long-feedback fallback and download, locally intercepted GitHub navigation, Pages subpath and entry links, JavaScript-disabled fallback, zero external network access, and 4 viewport sizes.');
  console.log(`Screenshots: ${path.relative(root, output)}`);
} finally {
  if (server) await new Promise(resolve => server.close(resolve));
  await browser.close();
}
