#!/usr/bin/env bun
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import net from 'node:net';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium, type BrowserContext, type Page } from 'playwright';
import { readWebConfig } from '../apps/web/config';
import { createWebService } from '../apps/web/server';
import type { WebRunner } from '../apps/web/runner';
import { draftRecoveryStorageKey } from '../apps/web/client/draftRecovery';
import { closeDialog, closeSettings, discardSourceEditor, openSettings } from './web-ui-controls';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const output = path.join(root, 'out/web-editor-review'), reportFile = path.join(output, 'report.json');
const widths = [1440, 375, 320];
const markup = '<img data-editor-review-injection src=x onerror="window.__reviewInjected=true">';
await fs.access(path.join(root, 'out/web/app.js')).catch(() => { throw new Error('Run bun run build:web before the editor review check.'); });
await fs.mkdir(output, { recursive: true }); await fs.rm(reportFile, { force: true });
const probe = net.createServer();
await new Promise<void>(resolve => probe.listen(0, '127.0.0.1', resolve));
const port = (probe.address() as net.AddressInfo).port;
await new Promise<void>((resolve, reject) => probe.close(error => error ? reject(error) : resolve()));
const origin = `http://127.0.0.1:${port}`;
let workerStarts = 0, cleanedOwners = 0;
const runner: WebRunner = {
  async readiness() { return { ready: true, message: 'Local editor review fixture' }; },
  async run() { workerStarts++; throw new Error('Editor review must never start a worker'); },
};
const service = createWebService(readWebConfig({ THEOREMOS_WEB_PORT: String(port), THEOREMOS_WEB_PUBLIC_URL: origin,
  THEOREMOS_WEB_STATIC_ROOT: path.join(root, 'out/web') }), runner);
type RequestRecord = { method: string; pathname: string };
type Harness = { page: Page; context: BrowserContext; requests: RequestRecord[]; releases: Array<() => Promise<unknown>> };
type EditorSnapshot = { value: string; start: number; end: number; direction: string; top: number; left: number };
type DiffRow = { kind: 'added' | 'removed' | 'context'; before: number | null; after: number | null; text: string; noNewline: boolean };
const checks: Array<{ name: string; width: number; elapsedMs: number; unexpectedWrites: number; requests: RequestRecord[] }> = [];
const screenshots: string[] = [];
const summaries: Array<{ label: string; text: string; added: number; removed: number }> = [];
const notices: Array<{ label: string; text: string }> = [];
const buffers: Array<{ label: string; width: number; start: number; end: number; direction: string; top: number; left: number }> = [];
const navigation: Array<{ label: string; position: string; scrollTop: number }> = [];
const editLocations: Array<{ label: string; width: number; offset: number; line: number; via: 'click' | 'Enter' }> = [];
const targetVisibility: Array<{ label: string; width: number; geometry: unknown }> = [];
let browser: Awaited<ReturnType<typeof chromium.launch>> | undefined;
let activeHarness: Harness | undefined;
let failedScenario = '', failureScreenshot = '';
const normalize = (source: string) => source.replace(/\r\n?/g, '\n');
const lineOffset = (source: string, line: number) => source.split('\n').slice(0, line - 1).reduce((offset, text) => offset + text.length + 1, 0);
const sourceRows = (page: Page) => page.locator('#editor-review-scroll tr.diff-added, #editor-review-scroll tr.diff-removed, #editor-review-scroll tr.diff-context');

async function settled(page: Page) {
  await page.evaluate(() => new Promise<void>(resolve => requestAnimationFrame(() => requestAnimationFrame(() => resolve()))));
}
async function scenario(name: string, run: (h: Harness) => Promise<void>, width = 1440) {
  failedScenario = name; const started = performance.now();
  const context = await browser!.newContext({ viewport: { width, height: width > 850 ? 900 : 812 }, reducedMotion: 'reduce' });
  const page = await context.newPage(); page.setDefaultTimeout(10_000);
  const h: Harness = { page, context, requests: [], releases: [] }; activeHarness = h;
  const errors: string[] = [], external: string[] = [];
  page.on('pageerror', error => errors.push(error.message));
  await context.route(/^https?:\/\//, async route => {
    const url = new URL(route.request().url());
    if (url.origin !== origin) { external.push(url.href); await route.abort(); return; }
    if (url.pathname.startsWith('/api/')) {
      h.requests.push({ method: route.request().method(), pathname: url.pathname });
      if (route.request().method() !== 'GET') { await route.abort(); return; }
    }
    await route.continue();
  });
  let deadline: ReturnType<typeof setTimeout> | undefined;
  try {
    await page.goto(origin); await page.locator('#submit-run:enabled').waitFor();
    await Promise.race([run(h), new Promise<never>((_, reject) => {
      deadline = setTimeout(() => reject(new Error(`Editor review scenario exceeded 50 seconds: ${name}`)), 50_000);
    })]);
    assert.deepEqual(errors, [], 'uncaught browser errors'); assert.deepEqual(external, [], 'review must remain local');
    const writes = h.requests.filter(request => request.method !== 'GET');
    assert.deepEqual(writes, [], 'review and applying a local draft must not create, change, cancel or delete runs');
    assert.equal(workerStarts, 0, 'review checks must not start a solver');
    checks.push({ name, width, elapsedMs: Math.round(performance.now() - started), unexpectedWrites: writes.length, requests: h.requests });
    console.log(`PASS ${name}`);
  } catch (error) {
    failureScreenshot = `failure-${checks.length + 1}.png`;
    await page.screenshot({ path: path.join(output, failureScreenshot) }).catch(() => {}); throw error;
  } finally {
    clearTimeout(deadline);
    try {
      for (const release of h.releases) await release().catch(() => {});
      const owner = (await context.cookies(origin)).find(cookie => cookie.name === 'theoremos_session')?.value;
      if (owner) {
        const remaining = service.jobs.list(owner).length; service.jobs.forget(owner); cleanedOwners++;
        assert.equal(remaining, 0, 'review must not create hidden fixture jobs');
      }
    } finally { await context.close(); }
  }
}
async function rememberBuffer(page: Page) {
  await page.locator('#expanded-source').evaluate(node => { (window as unknown as { __reviewBuffer: Element }).__reviewBuffer = node; });
}
async function sameBuffer(page: Page) {
  assert.equal(await page.locator('#expanded-source').evaluate(node => node === (window as unknown as { __reviewBuffer: Element }).__reviewBuffer), true,
    'review must retain the exact native textarea node and its undo history');
}
async function editSource(page: Page, source: string) {
  await openSettings(page); await page.locator('#environment').selectOption('standard');
  await page.locator('#template').selectOption(''); await page.locator('#source').fill(source);
  await page.locator('#expand-source').click(); await page.locator('#source-editor[open]').waitFor();
  await value(page, normalize(source)); await focused(page, '#expanded-source'); await rememberBuffer(page);
}
async function value(page: Page, expected: string) {
  await page.waitForFunction(expected => (document.querySelector('#expanded-source') as HTMLTextAreaElement).value === expected, expected);
}
async function text(page: Page, selector: string, expected: string) {
  await page.waitForFunction(({ selector, expected }) => document.querySelector(selector)?.textContent?.replace(/\s/g, '') === expected.replace(/\s/g, ''), { selector, expected });
}
async function focused(page: Page, selector: string) {
  assert.equal(await page.locator(selector).evaluate(node => node === document.activeElement), true, `${selector} must have focus`);
}
async function select(page: Page, start: number, end = start, direction: 'forward' | 'backward' | 'none' = 'none') {
  await page.locator('#expanded-source').evaluate((node, selection) => {
    const editor = node as HTMLTextAreaElement; editor.focus({ preventScroll: true });
    editor.setSelectionRange(selection.start, selection.end, selection.direction);
  }, { start, end, direction });
}
async function replaceBuffer(page: Page, source: string) {
  await page.locator('#expanded-source').focus(); await page.keyboard.press('Control+a');
  if (source) await page.keyboard.insertText(source); else await page.keyboard.press('Backspace');
  await value(page, source); await settled(page);
}
async function snapshot(page: Page): Promise<EditorSnapshot> {
  return page.locator('#expanded-source').evaluate(node => {
    const editor = node as HTMLTextAreaElement;
    return { value: editor.value, start: editor.selectionStart, end: editor.selectionEnd, direction: editor.selectionDirection,
      top: editor.scrollTop, left: editor.scrollLeft };
  });
}
async function preserved(page: Page, before: EditorSnapshot, label: string) {
  await settled(page); await sameBuffer(page); const actual = await snapshot(page);
  assert.equal(actual.value, before.value, `${label}: preserve native scratch text`);
  assert.equal(actual.start, before.start); assert.equal(actual.end, before.end); assert.equal(actual.direction, before.direction);
  assert.ok(Math.abs(actual.top - before.top) <= 1 && Math.abs(actual.left - before.left) <= 1,
    `${label}: review must preserve the editor's scroll: ${JSON.stringify({ before: { ...before, value: undefined }, actual: { ...actual, value: undefined } })}`);
  buffers.push({ label, width: page.viewportSize()!.width, start: actual.start, end: actual.end, direction: actual.direction, top: actual.top, left: actual.left });
}
async function openReview(page: Page) {
  assert.equal(await page.locator('#editor-review-toggle').isVisible(), true, 'a dirty buffer offers review');
  await page.locator('#editor-review-toggle').click(); await page.locator('#editor-review').waitFor(); await settled(page);
  assert.equal(await page.locator('#editor-review-toggle').getAttribute('aria-expanded'), 'true');
  assert.equal(await page.locator('#editor-review-toggle').getAttribute('aria-controls'), 'editor-review');
  assert.equal((await page.locator('#editor-review-toggle').innerText()).trim(), '返回编辑');
  assert.equal(await page.locator('.editor-source-surface').isVisible(), false);
  assert.equal(await page.locator('#source-editor .editor-toolbar').isVisible(), false);
  assert.equal(await page.locator('#editor-navigation').isVisible(), false);
  assert.equal(await page.locator('#editor-review textarea, #editor-review [contenteditable="true"]').count(), 0, 'the diff is read-only');
  await sameBuffer(page);
}
async function returnEdit(page: Page, escape = false) {
  if (await page.locator('#editor-review').isVisible()) {
    if (escape) await page.keyboard.press('Escape'); else await page.locator('#editor-review-toggle').click();
  }
  assert.equal(await page.locator('#editor-review').isVisible(), false);
  assert.equal(await page.locator('.editor-source-surface').isVisible(), true);
  assert.equal(await page.locator('#editor-review-toggle').getAttribute('aria-expanded'), 'false');
  await focused(page, '#expanded-source'); await sameBuffer(page); await settled(page);
}
async function rows(page: Page): Promise<DiffRow[]> {
  return sourceRows(page).evaluateAll(nodes => nodes.map(node => ({
    kind: node.classList.contains('diff-added') ? 'added' : node.classList.contains('diff-removed') ? 'removed' : 'context',
    before: node.hasAttribute('data-old-line') ? Number(node.getAttribute('data-old-line')) : null,
    after: node.hasAttribute('data-new-line') ? Number(node.getAttribute('data-new-line')) : null,
    text: node.querySelector('[data-diff-text]')!.textContent!, noNewline: Boolean(node.querySelector('.diff-no-newline')),
  })));
}
async function summary(page: Page, added: number, removed: number, label: string) {
  const actual = await page.locator('#editor-review-summary').evaluate(node => ({ text: node.textContent ?? '',
    labels: Array.from(node.querySelectorAll('[aria-label]')).map(child => child.getAttribute('aria-label')).join(' ') }));
  const clean = `${actual.text} ${actual.labels}`.replaceAll(',', '');
  assert.ok(new RegExp(`新增\\s*${added}\\s*行`).test(clean) || new RegExp(`\\+\\s*${added}(?!\\d)`).test(clean), `added count ${added}: ${clean}`);
  assert.ok(new RegExp(`删除\\s*${removed}\\s*行`).test(clean) || new RegExp(`-\\s*${removed}(?!\\d)`).test(clean), `removed count ${removed}: ${clean}`);
  assert.doesNotMatch(clean, /验收|证明通过|已验证/, 'scratch review must not claim Lean acceptance');
  summaries.push({ label, text: actual.text.trim(), added, removed });
}
async function notice(page: Page, label: string, selector = '#editor-review-notice') {
  await page.locator(selector).waitFor();
  const content = (await page.locator(selector).innerText()).trim();
  assert.ok(content, `${label}: a comparison limit needs an explicit notice`); notices.push({ label, text: content });
  return content;
}
async function currentChange(page: Page, index: number, label: string) {
  await settled(page);
  const evidence = await page.locator('#editor-review-scroll').evaluate((scroll, index) => {
    const change = scroll.querySelectorAll<HTMLElement>('[data-change-start]')[index];
    const rect = change?.getBoundingClientRect(), bounds = scroll.getBoundingClientRect();
    const header = scroll.querySelector('thead')?.getBoundingClientRect().height ?? 0;
    return { found: Boolean(change), top: rect?.top ?? -1, bottom: rect?.bottom ?? -1,
      visibleTop: bounds.top + header, visibleBottom: bounds.bottom, scrollTop: scroll.scrollTop };
  }, index);
  assert.equal(evidence.found, true);
  assert.ok(evidence.top >= evidence.visibleTop - 2 && evidence.bottom <= evidence.visibleBottom + 2,
    `${label}: the current change must be visible: ${JSON.stringify(evidence)}`);
  navigation.push({ label, position: (await page.locator('#editor-review-position').innerText()).trim(), scrollTop: evidence.scrollTop });
}
async function reviewLocation(page: Page, source: string, offset: number) {
  const line = source.slice(0, offset).split('\n').length;
  assert.equal(await page.locator('#editor-review-edit').isVisible(), true, 'a displayed change offers a source edit location');
  assert.equal((await page.locator('#editor-review-edit').innerText()).trim(), '编辑此处');
  assert.match(await page.locator('#editor-review-location').innerText(), new RegExp(`第\\s*${line}\\s*行`),
    'the review location must use the current source logical line');
  return line;
}
async function editChange(page: Page, source: string, offset: number, label: string, via: 'click' | 'Enter' = 'click') {
  const line = await reviewLocation(page, source, offset);
  if (via === 'Enter') { await page.locator('#editor-review-edit').focus(); await page.keyboard.press('Enter'); }
  else await page.locator('#editor-review-edit').click();
  await returnEdit(page); const actual = await snapshot(page);
  assert.equal(actual.value, source, `${label}: editing a review location must not modify source`);
  assert.equal(actual.start, offset, `${label}: the caret must use the exact UTF-16 target offset`);
  assert.equal(actual.end, offset, `${label}: review edit places a caret without selecting source`);
  assert.equal(await page.locator('#editor-navigation').isVisible(), false, 'review edit must leave source navigation tools closed');
  await text(page, '#editor-position', `第 ${line} 行 · 第 ${Array.from(source.slice(source.lastIndexOf('\n', Math.max(0, offset - 1)) + 1, offset)).length + 1} 列`);
  editLocations.push({ label, width: page.viewportSize()!.width, offset, line, via });
}
async function visibleCaret(page: Page, label: string) {
  await settled(page);
  const geometry = await page.locator('#expanded-source').evaluate(node => {
    const editor = node as HTMLTextAreaElement, computed = getComputedStyle(editor), mirror = document.createElement('div');
    for (const property of ['font-family', 'font-size', 'font-style', 'font-weight', 'font-variant', 'line-height', 'letter-spacing',
      'word-spacing', 'text-align', 'text-indent', 'text-transform', 'direction', 'tab-size', 'word-break']) {
      mirror.style.setProperty(property, computed.getPropertyValue(property));
    }
    Object.assign(mirror.style, { position: 'fixed', top: '0', left: '0', visibility: 'hidden', pointerEvents: 'none',
      margin: '0', border: '0', boxSizing: 'border-box', width: `${editor.clientWidth}px`, height: 'auto', minHeight: '0',
      whiteSpace: editor.wrap === 'off' ? 'pre' : 'pre-wrap', overflowWrap: 'break-word',
      paddingTop: computed.paddingTop, paddingRight: computed.paddingRight, paddingBottom: computed.paddingBottom, paddingLeft: computed.paddingLeft });
    const content = document.createTextNode(editor.value + '\u200b'); mirror.append(content); document.body.append(mirror);
    try {
      const range = document.createRange(); range.setStart(content, editor.selectionStart); range.setEnd(content, editor.selectionEnd);
      let rect = range.getClientRects()[0] ?? range.getBoundingClientRect();
      if (!rect.height) {
        content.data = editor.value.slice(0, editor.selectionStart) + '\u200b' + editor.value.slice(editor.selectionStart) + '\u200b';
        range.setStart(content, editor.selectionStart); range.setEnd(content, editor.selectionStart + 1);
        rect = range.getClientRects()[0] ?? range.getBoundingClientRect();
      }
      const origin = mirror.getBoundingClientRect(), bounds = editor.getBoundingClientRect();
      return { height: rect.height, top: rect.top - origin.top - editor.scrollTop, bottom: rect.bottom - origin.top - editor.scrollTop,
        left: rect.left - origin.left - editor.scrollLeft, right: rect.right - origin.left - editor.scrollLeft,
        visibleTop: Math.max(0, -bounds.top - editor.clientTop), visibleBottom: Math.min(editor.clientHeight, innerHeight - bounds.top - editor.clientTop),
        visibleLeft: Math.max(0, -bounds.left - editor.clientLeft), visibleRight: Math.min(editor.clientWidth, innerWidth - bounds.left - editor.clientLeft),
        scrollTop: editor.scrollTop, scrollLeft: editor.scrollLeft };
    } finally { mirror.remove(); }
  });
  targetVisibility.push({ label, width: page.viewportSize()!.width, geometry });
  assert.ok(geometry.height > 0, `${label}: a native Range must occupy a rendered line`);
  assert.ok(geometry.top >= geometry.visibleTop - 2 && geometry.bottom <= geometry.visibleBottom + 2,
    `${label}: the actual wrapped caret must be vertically visible: ${JSON.stringify(geometry)}`);
  assert.ok(geometry.left >= geometry.visibleLeft - 2 && geometry.right <= geometry.visibleRight + 2,
    `${label}: the actual wrapped caret must be horizontally visible: ${JSON.stringify(geometry)}`);
}
async function recovery(page: Page) { return page.evaluate(key => sessionStorage.getItem(key), draftRecoveryStorageKey); }
async function pristine(page: Page, source: string, backup: string | null) {
  assert.equal(await page.locator('#source').inputValue(), source, 'review and scratch edits must not apply the draft automatically');
  assert.equal(await recovery(page), backup, 'review must not replace the recovery backup');
}
async function fit(page: Page, selector: string) {
  const box = await page.locator(selector).boundingBox(), viewport = page.viewportSize()!;
  assert.ok(box && box.width > 0 && box.height > 0 && box.x >= -1 && box.y >= -1
    && box.x + box.width <= viewport.width + 1 && box.y + box.height <= viewport.height + 1,
    `${selector} must fit ${viewport.width}px: ${JSON.stringify(box)}`);
  assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth + 1), true, 'review must not widen the page');
}
async function screenshot(page: Page, name: string) {
  await page.screenshot({ path: path.join(output, name) }); screenshots.push(name);
}
async function delayedLean(h: Harness, source: string) {
  await h.page.evaluate(() => {
    const original = File.prototype.arrayBuffer;
    File.prototype.arrayBuffer = async function() {
      const value = await original.call(this);
      if (this.name === 'late-review.lean') await new Promise<void>(resolve => {
        (window as unknown as { __releaseReviewFile: () => void }).__releaseReviewFile = resolve;
      });
      return value;
    };
  });
  const release = () => h.page.evaluate(() => (window as unknown as { __releaseReviewFile?: () => void }).__releaseReviewFile?.());
  h.releases.push(release);
  await h.page.locator('#source-file').setInputFiles({ name: 'late-review.lean', mimeType: 'text/plain', buffer: Buffer.from(source) });
  await h.page.waitForFunction(() => typeof (window as unknown as { __releaseReviewFile?: unknown }).__releaseReviewFile === 'function');
  return release;
}
async function writeReport(status: 'passed' | 'failed', error?: unknown) {
  await fs.writeFile(reportFile, JSON.stringify({ status, checkedAt: new Date().toISOString(),
    mode: 'Real local HTTP service and Chromium. Read-only scratch review, frozen editor baseline and native textarea history. All API writes are blocked; no models, Docker, Lean or external requests.',
    paidModelCalls: false, workerStarts, cleanedOwners, widths, checks, summaries, notices, buffers, navigation, editLocations, targetVisibility, screenshots,
    unexpectedWrites: checks.reduce((sum, check) => sum + check.unexpectedWrites, 0),
    ...(error ? { failedScenario, error: error instanceof Error ? error.message : String(error), failureScreenshot, failureRequests: activeHarness?.requests } : {}) }, null, 2) + '\n');
}

try {
  await new Promise<void>((resolve, reject) => { service.server.once('error', reject); service.server.listen(port, '127.0.0.1', resolve); });
  browser = await chromium.launch({ headless: true });

  for (const width of widths) await scenario(`Review shows real changed rows and local scrolling without applying the draft at ${width}px`, async ({ page }) => {
    const original = Array.from({ length: 32 }, (_, index) => `-- context ${index + 1}`);
    original[6] = `-- old ${'long_identifier_'.repeat(24)}${markup} 🙂`;
    const edited = [...original]; edited[6] = `-- new ${'long_identifier_'.repeat(24)}${markup} 🙂`; edited[24] = '-- second changed line';
    const source = original.join('\n') + '\n', scratch = edited.join('\n') + '\n'; await editSource(page, source);
    assert.equal(await page.locator('#editor-review-toggle').isVisible(), false, 'an unchanged editor has no review action');
    const backup = await recovery(page); await replaceBuffer(page, scratch);
    assert.equal((await page.locator('#editor-review-toggle').innerText()).trim(), '查看改动');
    await openReview(page); assert.equal(await page.locator('#editor-review-fold').isChecked(), true);
    await summary(page, 2, 2, `responsive real diff ${width}px`);
    const actual = await rows(page);
    assert.deepEqual(actual.filter(row => row.kind === 'removed').map(row => [row.before, row.text]), [[7, original[6]], [25, original[24]]]);
    assert.deepEqual(actual.filter(row => row.kind === 'added').map(row => [row.after, row.text]), [[7, edited[6]], [25, edited[24]]]);
    assert.ok(await page.locator('#editor-review-scroll .diff-gap').count() > 0);
    const headings = (await page.locator('#editor-review-scroll th').allTextContents()).join(' ');
    assert.match(headings, /编辑前/); assert.match(headings, /编辑后/); assert.doesNotMatch(headings, /验收/);
    assert.equal(await page.locator('[data-editor-review-injection]').count(), 0);
    assert.equal(await page.evaluate(() => Boolean((window as unknown as { __reviewInjected?: boolean }).__reviewInjected)), false);
    await text(page, '#editor-review-position', '1/2');
    assert.equal(await page.locator('#editor-review-prev').isDisabled(), true);
    await page.locator('#editor-review-next').click(); await text(page, '#editor-review-position', '2/2'); await currentChange(page, 1, 'responsive next change');
    assert.equal(await page.locator('#editor-review-next').isDisabled(), true);
    await page.locator('#editor-review-prev').click(); await text(page, '#editor-review-position', '1/2');
    for (const selector of ['#source-editor', '#editor-review', '#editor-review-summary', '#editor-review-fold', '#editor-review-prev',
      '#editor-review-next', '#editor-review-position', '#editor-review-edit', '#editor-review-location', '#editor-review-scroll', '#editor-review-toggle', '#apply-editor']) await fit(page, selector);
    const localScroll = await page.locator('#editor-review-scroll').evaluate(node => {
      node.scrollLeft = node.scrollWidth;
      const cell = node.querySelector<HTMLElement>('.diff-code');
      const code = cell?.querySelector<HTMLElement>('code');
      const cellStyle = cell ? getComputedStyle(cell) : undefined;
      const codeStyle = code ? getComputedStyle(code) : undefined;
      return { width: node.clientWidth, total: node.scrollWidth, left: node.scrollLeft,
        cellWidth: cell?.clientWidth, cellScrollWidth: cell?.scrollWidth, cellWhiteSpace: cellStyle?.whiteSpace,
        cellOverflowWrap: cellStyle?.overflowWrap, codeWidth: code?.clientWidth, codeScrollWidth: code?.scrollWidth,
        codeWhiteSpace: codeStyle?.whiteSpace, tableLayout: getComputedStyle(node.querySelector('table')!).tableLayout };
    });
    if (width <= 560) {
      assert.ok(localScroll.total <= localScroll.width + 1,
        `mobile diff should wrap long source lines instead of widening its scroll surface: ${JSON.stringify(localScroll)}`);
      const wrapped = await page.locator('#editor-review-scroll .diff-removed .diff-code').first().evaluate(node => {
        const style = getComputedStyle(node);
        return { height: node.getBoundingClientRect().height, lineHeight: Number.parseFloat(style.lineHeight) };
      });
      assert.ok(wrapped.height > wrapped.lineHeight * 2,
        `mobile diff should visibly wrap a long source line: ${JSON.stringify(wrapped)}`);
    } else {
      assert.ok(localScroll.total > localScroll.width && localScroll.left > 0, 'long source lines scroll inside the diff');
    }
    await page.locator('#editor-review-scroll').evaluate(node => { node.scrollLeft = 0; }); await settled(page);
    await screenshot(page, `editor-review-${width}.png`); await pristine(page, source, backup);
    await returnEdit(page); await value(page, scratch); await discardSourceEditor(page); await closeSettings(page);
    const deepBefore = Array.from({ length: 222 }, (_, index) => `-- deep context ${index + 1}`);
    deepBefore[0] = `-- ${'🙂 lead '.repeat(500)}`;
    deepBefore[174] = `-- ${'wrapped '.repeat(60)}🙂 old_target`;
    deepBefore[203] = '-- later original';
    const deepAfter = [...deepBefore]; deepAfter[174] = deepBefore[174]!.replace('old_target', 'new_target'); deepAfter[203] = '-- later changed';
    const deepSource = deepBefore.join('\n') + '\n', deepScratch = deepAfter.join('\n') + '\n';
    await editSource(page, deepSource); const deepBackup = await recovery(page);
    const laterStart = deepSource.indexOf('-- later original');
    await select(page, laterStart, laterStart + '-- later original'.length); await page.keyboard.insertText('-- later changed');
    const deepPartial = deepSource.replace('-- later original', '-- later changed'), targetStart = deepPartial.indexOf('old_target');
    await select(page, targetStart, targetStart + 'old_target'.length); await page.keyboard.insertText('new_target');
    await value(page, deepScratch); await openReview(page);
    await reviewLocation(page, deepScratch, lineOffset(deepScratch, 175));
    await page.locator('#editor-review-next').click(); await text(page, '#editor-review-position', '2/2');
    await reviewLocation(page, deepScratch, lineOffset(deepScratch, 204));
    await page.locator('#editor-review-prev').click(); await text(page, '#editor-review-position', '1/2');
    await screenshot(page, `editor-review-deep-${width}.png`);
    await editChange(page, deepScratch, lineOffset(deepScratch, 175), `deep Unicode logical line at ${width}px`, 'Enter');
    await visibleCaret(page, `deep Unicode logical line at ${width}px`); await pristine(page, deepSource, deepBackup);
    await screenshot(page, `editor-review-edit-${width}.png`);
    await page.keyboard.press('Control+z'); await value(page, deepPartial);
    await page.keyboard.press('Control+Shift+z'); await value(page, deepScratch); await sameBuffer(page);
    await discardSourceEditor(page); await closeSettings(page);
  }, width);

  await scenario('Full diff reconstructs escaped Unicode source and the exact final-newline change', async ({ page }) => {
    const source = `-- ${markup} 🙂 before\n-- unchanged\n-- old tail\n`;
    const scratch = `-- ${markup} 🙂 after\n-- unchanged\n-- new tail`;
    await editSource(page, source); await replaceBuffer(page, scratch); await openReview(page); await page.locator('#editor-review-fold').uncheck();
    const actual = await rows(page);
    const reconstruct = (side: 'before' | 'after') => actual.filter(row => row.kind !== (side === 'before' ? 'added' : 'removed'))
      .map(row => row.text + (row.noNewline ? '' : '\n')).join('');
    assert.equal(reconstruct('before'), source); assert.equal(reconstruct('after'), scratch);
    await summary(page, 2, 2, 'literal Unicode and EOF');
    assert.equal(await page.locator('#editor-review-scroll .diff-removed .diff-no-newline').count(), 0);
    assert.equal(await page.locator('#editor-review-scroll .diff-added .diff-no-newline[data-eof-side="new"]').count(), 1);
    assert.equal(await page.locator('[data-editor-review-injection]').count(), 0);
    await screenshot(page, 'editor-review-literal-eof.png'); await returnEdit(page, true); await discardSourceEditor(page);
  });

  await scenario('Cached review retains reading scroll and only refreshes changed source when review is entered again', async ({ page }) => {
    const original = Array.from({ length: 250 }, (_, index) => `-- context ${index + 1}`), edited = [...original];
    edited[19] = '-- first changed'; edited[219] = '-- second changed';
    const source = original.join('\n'), scratch = edited.join('\n'); await editSource(page, source); await replaceBuffer(page, scratch);
    await openReview(page); await page.locator('#editor-review-fold').uncheck();
    await page.locator('#editor-review-next').click(); await text(page, '#editor-review-position', '2/2');
    await page.locator('#editor-review-scroll').evaluate(node => { node.scrollTop = 400; }); await settled(page);
    const scrollTop = await page.locator('#editor-review-scroll').evaluate(node => node.scrollTop);
    await returnEdit(page); await openReview(page);
    assert.equal(await page.locator('#editor-review-fold').isChecked(), false);
    assert.ok(Math.abs(await page.locator('#editor-review-scroll').evaluate(node => node.scrollTop) - scrollTop) <= 1,
      'unchanged review reopens at the prior reading position');
    await text(page, '#editor-review-position', '2/2'); await returnEdit(page);
    await page.evaluate(() => {
      const state = window as unknown as { __reviewMutations: number }; state.__reviewMutations = 0;
      new MutationObserver(records => { state.__reviewMutations += records.length; })
        .observe(document.querySelector('#editor-review-scroll')!, { subtree: true, childList: true, characterData: true });
    });
    const oldRows = await rows(page); await select(page, scratch.length); await page.keyboard.insertText('\n-- third changed'); await settled(page);
    assert.equal(await page.evaluate(() => (window as unknown as { __reviewMutations: number }).__reviewMutations), 0,
      'ordinary scratch input must not rerender the hidden comparison');
    assert.deepEqual(await rows(page), oldRows, 'the hidden comparison remains cached until it is opened');
    await openReview(page); await text(page, '#editor-review-position', '1/3'); await summary(page, 4, 3, 'updated review after a third change and a new final newline');
    assert.ok((await rows(page)).some(row => row.kind === 'added' && row.text === '-- third changed'));
    await screenshot(page, 'editor-review-refreshed.png'); await returnEdit(page); await discardSourceEditor(page);
  });

  await scenario('Editing the current hunk survives folding and preserves cached review navigation and reading position', async ({ page }) => {
    const original = Array.from({ length: 100 }, (_, index) => `-- context ${index + 1}`);
    const edited = [...original]; edited.splice(4, 0, '-- inserted 🙂 first', '-- inserted second'); edited[61] = '-- replaced middle'; edited[91] = '-- replaced last';
    const source = original.join('\n') + '\n', scratch = edited.join('\n') + '\n'; await editSource(page, source); await replaceBuffer(page, scratch);
    const backup = await recovery(page); await openReview(page); await text(page, '#editor-review-position', '1/3');
    await reviewLocation(page, scratch, lineOffset(scratch, 5));
    await page.locator('#editor-review-next').click(); await text(page, '#editor-review-position', '2/3');
    await reviewLocation(page, scratch, lineOffset(scratch, 62));
    await page.locator('#editor-review-fold').uncheck(); await text(page, '#editor-review-position', '2/3');
    await reviewLocation(page, scratch, lineOffset(scratch, 62));
    await page.locator('#editor-review-next').click(); await text(page, '#editor-review-position', '3/3');
    await page.locator('#editor-review-fold').check(); await text(page, '#editor-review-position', '3/3');
    await reviewLocation(page, scratch, lineOffset(scratch, 92));
    await page.locator('#editor-review-scroll').evaluate(node => { node.scrollTop = 80; }); await settled(page);
    const reading = await page.locator('#editor-review-scroll').evaluate(node => ({ top: node.scrollTop, left: node.scrollLeft }));
    const markupBefore = await page.locator('#editor-review-body').innerHTML();
    await editChange(page, scratch, lineOffset(scratch, 92), 'last hunk after folding changes'); await visibleCaret(page, 'last hunk source caret');
    await pristine(page, source, backup); await openReview(page); await text(page, '#editor-review-position', '3/3');
    assert.equal(await page.locator('#editor-review-fold').isChecked(), true);
    assert.equal(await page.locator('#editor-review-body').innerHTML(), markupBefore, 'location-only editing must reuse the unchanged cached comparison');
    const reopened = await page.locator('#editor-review-scroll').evaluate(node => ({ top: node.scrollTop, left: node.scrollLeft }));
    assert.ok(Math.abs(reopened.top - reading.top) <= 1 && Math.abs(reopened.left - reading.left) <= 1, 'editing a location retains review reading offsets');
    await page.locator('#editor-review-prev').click(); await editChange(page, scratch, lineOffset(scratch, 62), 'previous hunk source caret');
    await pristine(page, source, backup); await discardSourceEditor(page);
  });

  await scenario('Deletion boundaries, empty buffers, blank lines and final newlines map to exact current-source caret positions', async ({ page }) => {
    const cases = [
      { label: 'pure deletion at the beginning', source: '-- deleted head\n-- kept\n', scratch: '-- kept\n', offset: 0 },
      { label: 'pure deletion in the middle', source: '-- first\n-- deleted middle\n-- last\n', scratch: '-- first\n-- last\n', offset: 9 },
      { label: 'pure deletion at EOF after a final newline', source: '-- first\n-- deleted tail\n', scratch: '-- first\n', offset: 9 },
      { label: 'pure deletion of a tail without a newline', source: '-- first\n-- deleted tail', scratch: '-- first\n', offset: 9 },
      { label: 'deletion of the entire source', source: '-- deleted only line\n', scratch: '', offset: 0 },
      { label: 'deletion of an intermediate empty line', source: '-- first\n\n-- last\n', scratch: '-- first\n-- last\n', offset: 9 },
      { label: 'deletion of a trailing empty line', source: '-- kept\n\n', scratch: '-- kept\n', offset: 8 },
      { label: 'insertion of an empty line', source: '-- first\n-- last\n', scratch: '-- first\n\n-- last\n', offset: 9 },
      { label: 'insertion of the final newline', source: '-- kept', scratch: '-- kept\n', offset: 0 },
      { label: 'removal of the final newline', source: '-- kept\n', scratch: '-- kept', offset: 0 },
    ];
    for (const { label, source, scratch, offset } of cases) {
      await editSource(page, source); const backup = await recovery(page); await replaceBuffer(page, scratch); await openReview(page);
      await text(page, '#editor-review-position', '1/1');
      await editChange(page, scratch, offset, label); await visibleCaret(page, label); await pristine(page, source, backup);
      if (scratch === '') {
        await page.locator('#apply-editor').click();
        assert.equal(await page.locator('#source-editor').evaluate(node => (node as HTMLDialogElement).open), true);
        assert.equal(await page.locator('#editor-error').isVisible(), true, 'editing an empty review location cannot bypass Apply validation');
        await pristine(page, source, backup);
      }
      await page.keyboard.press('Control+z'); await value(page, source); await text(page, '#editor-change-status', '未修改');
      await closeDialog(page, '#source-editor', () => page.locator('#close-editor').click());
      assert.equal(await page.locator('#editor-discard-dialog').isVisible(), false, 'location-only handoff adds no dirty transaction after undo');
      await closeSettings(page);
    }
  });

  await scenario('Review round trips preserve the native textarea, selection direction, scroll and undo history', async ({ page }) => {
    const original = Array.from({ length: 220 }, (_, index) => `-- row ${index + 1}`), source = original.join('\n');
    await editSource(page, source); const backup = await recovery(page), start = source.indexOf('-- row 100\n');
    await select(page, start, start + '-- row 100'.length); await page.keyboard.insertText('-- edited row 100');
    const scratch = source.slice(0, start) + '-- edited row 100' + source.slice(start + '-- row 100'.length);
    await value(page, scratch); const selected = scratch.indexOf('-- row 180\n'); await select(page, selected, selected + 10, 'backward');
    await page.locator('#expanded-source').evaluate(node => { node.scrollTop = 2600; }); const before = await snapshot(page);
    for (const escape of [false, true, false]) {
      await openReview(page); await returnEdit(page, escape); await preserved(page, before, 'native selection and scroll after review');
    }
    await page.keyboard.press('Control+z'); await value(page, source); await text(page, '#editor-change-status', '未修改');
    assert.equal(await page.locator('#editor-review-toggle').isVisible(), false);
    await page.keyboard.press('Control+Shift+z'); await value(page, scratch); await sameBuffer(page); await pristine(page, source, backup);
    await discardSourceEditor(page);
  });

  await scenario('A native multiline replace-all remains one undoable isolated edit after diff review', async ({ page }) => {
    const source = 'theorem review_replace : True := by\n  sorry\n-- sorry'; await editSource(page, source); const backup = await recovery(page);
    await page.keyboard.press('Control+h'); await page.locator('#editor-find-input').fill('sorry');
    await page.locator('#editor-replace-input').fill('trivial'); await page.locator('#editor-replace-all').click();
    const scratch = source.split('sorry').join('trivial'); await value(page, scratch); await openReview(page); await summary(page, 2, 2, 'native replace-all review');
    await pristine(page, source, backup); await returnEdit(page); await page.keyboard.press('Control+z'); await value(page, source);
    await page.keyboard.press('Control+Shift+z'); await value(page, scratch); await openReview(page); await summary(page, 2, 2, 'redo refreshes review');
    await returnEdit(page); await pristine(page, source, backup); await discardSourceEditor(page);
  });

  await scenario('Escape and editor find, line and replace shortcuts return to the same editable buffer', async ({ page }) => {
    const source = '-- needle before\n-- needle after'; await editSource(page, source); await select(page, source.length);
    await page.keyboard.insertText('\n-- scratch note'); const scratch = source + '\n-- scratch note';
    const cases = [
      { key: 'Control+f', focus: '#editor-find-input', controls: '#editor-find-controls' },
      { key: 'Meta+g', focus: '#editor-line-input', controls: '#editor-line-controls' },
      { key: 'Control+h', focus: '#editor-replace-input', controls: '#editor-replace-controls' },
    ];
    for (const { key, focus, controls } of cases) {
      await openReview(page);
      assert.equal(await page.locator('#editor-review-scroll').evaluate(node => node.dispatchEvent(new KeyboardEvent('keydown', {
        key: 'f', ctrlKey: true, isComposing: true, bubbles: true, cancelable: true,
      }))), true, 'IME shortcuts must not leave review');
      assert.equal(await page.locator('#editor-review').isVisible(), true);
      await page.keyboard.press(key); await focused(page, focus); assert.equal(await page.locator(controls).isVisible(), true);
      assert.equal(await page.locator('#editor-review').isVisible(), false); await value(page, scratch); await sameBuffer(page);
      await page.keyboard.press('Escape'); await focused(page, '#expanded-source');
    }
    await openReview(page); await returnEdit(page, true);
    assert.equal(await page.locator('#editor-discard-dialog').isVisible(), false, 'Escape leaves review before asking to discard');
    await discardSourceEditor(page);
  });

  await scenario('Dirty-close confirmation returns to source and Apply validates then creates one recovery and resets review', async ({ page }) => {
    const source = 'theorem review_apply : True := by\n  sorry'; await editSource(page, source); const backup = await recovery(page);
    const scratch = source.replace('sorry', 'trivial'); await replaceBuffer(page, scratch); await openReview(page);
    await editChange(page, scratch, lineOffset(scratch, 2), 'review source location retains dirty-close protection');
    await pristine(page, source, backup); await openReview(page);
    await page.locator('#close-editor').click(); await page.locator('#editor-discard-dialog[open]').waitFor();
    await closeDialog(page, '#editor-discard-dialog', () => page.locator('#keep-editing').click());
    assert.equal(await page.locator('#editor-review').isVisible(), false); await focused(page, '#expanded-source'); await value(page, scratch); await sameBuffer(page);
    await replaceBuffer(page, ' \n'); await openReview(page); await page.locator('#apply-editor').click();
    assert.equal(await page.locator('#source-editor').evaluate(node => (node as HTMLDialogElement).open), true);
    assert.equal(await page.locator('#editor-error').isVisible(), true, 'invalid reviewed source must show the existing validation error');
    await pristine(page, source, backup); await returnEdit(page); await replaceBuffer(page, scratch);
    await page.evaluate(key => {
      const original = Storage.prototype.setItem; const state = window as unknown as { __reviewRecoveryWrites: number }; state.__reviewRecoveryWrites = 0;
      Storage.prototype.setItem = function(name, value) {
        if (this === sessionStorage && name === key) state.__reviewRecoveryWrites++;
        return original.call(this, name, value);
      };
    }, draftRecoveryStorageKey);
    await openReview(page); await page.locator('#editor-review-fold').uncheck();
    await closeDialog(page, '#source-editor', () => page.locator('#apply-editor').click());
    assert.equal(await page.locator('#source').inputValue(), scratch);
    const saved = JSON.parse((await recovery(page))!); assert.equal(saved.reason, 'edit'); assert.equal(saved.task.draft.source, source);
    assert.equal(await page.evaluate(() => (window as unknown as { __reviewRecoveryWrites: number }).__reviewRecoveryWrites), 1);
    await page.locator('#expand-source').click(); await page.locator('#source-editor[open]').waitFor(); await rememberBuffer(page);
    assert.equal(await page.locator('#editor-review').isVisible(), false); assert.equal(await page.locator('#editor-review-toggle').isVisible(), false);
    await select(page, scratch.length); await page.keyboard.insertText('\n-- next session'); await openReview(page);
    assert.equal(await page.locator('#editor-review-fold').isChecked(), true, 'a new editor resets the folding default');
    await summary(page, 2, 1, 'fresh session compares against the applied source');
    await page.locator('#editor-review-fold').uncheck();
    const fresh = await rows(page);
    assert.equal(fresh.some(row => row.kind === 'removed' && row.text.includes('sorry')), false, 'an old baseline cannot leak into the next editor session');
    await returnEdit(page); await discardSourceEditor(page);
  });

  await scenario('A delayed Lean import cannot replace the frozen review baseline or bypass stale-draft validation', async h => {
    const { page } = h, source = '-- original baseline\ntheorem late_review : True := by sorry';
    const imported = '-- imported baseline\ntheorem imported_review : True := by trivial';
    await openSettings(page); await page.locator('#environment').selectOption('standard'); await page.locator('#template').selectOption(''); await page.locator('#source').fill(source);
    const release = await delayedLean(h, imported); await page.locator('#expand-source').click(); await page.locator('#source-editor[open]').waitFor(); await rememberBuffer(page);
    const scratch = source.replace('sorry', 'trivial'); await replaceBuffer(page, scratch); await release();
    await page.waitForFunction(source => (document.querySelector('#source') as HTMLTextAreaElement).value === source, imported);
    const importedBackup = await recovery(page); await openReview(page); await page.locator('#editor-review-fold').uncheck();
    const actual = await rows(page);
    assert.ok(actual.some(row => row.text === '-- original baseline'));
    assert.equal(actual.some(row => row.text === '-- imported baseline'), false, 'the diff must compare the baseline frozen when this editor opened');
    await summary(page, 1, 1, 'frozen baseline after delayed source import'); await value(page, scratch);
    await editChange(page, scratch, lineOffset(scratch, 2), 'a frozen-baseline location uses the independent scratch source');
    await pristine(page, imported, importedBackup); await openReview(page);
    await page.locator('#apply-editor').click();
    assert.equal(await page.locator('#source-editor').evaluate(node => (node as HTMLDialogElement).open), true);
    assert.equal(await page.locator('#editor-error').isVisible(), true); assert.match(await page.locator('#editor-error').innerText(), /变化|重新/);
    await pristine(page, imported, importedBackup); await returnEdit(page); await discardSourceEditor(page);
    await page.locator('#expand-source').click(); await page.locator('#source-editor[open]').waitFor(); await rememberBuffer(page); await value(page, imported);
    await select(page, imported.length); await page.keyboard.insertText('\n-- imported-session note'); await openReview(page); await page.locator('#editor-review-fold').uncheck();
    const next = await rows(page); assert.ok(next.some(row => row.text === '-- imported baseline')); assert.equal(next.some(row => row.text === '-- original baseline'), false);
    await returnEdit(page); await discardSourceEditor(page);
  });

  await scenario('The 2000-row cap warns about omitted rows and navigation only counts displayed changes', async ({ page }) => {
    const original = Array.from({ length: 2500 }, (_, index) => `-- row ${index + 1}`), edited = [...original];
    edited[2499] = '-- changed last line'; edited.splice(5, 0, '-- inserted 🙂 context', '-- second inserted line');
    const source = original.join('\n'), scratch = edited.join('\n'); await editSource(page, source); await replaceBuffer(page, scratch); await openReview(page);
    await summary(page, 3, 1, 'folded diff retains the final change and earlier line shifts');
    assert.ok((await rows(page)).some(row => row.kind === 'added' && row.text === '-- changed last line'));
    await page.locator('#editor-review-fold').uncheck(); assert.equal(await sourceRows(page).count(), 2000);
    const message = await notice(page, '2000-row display cap'); assert.match(message, /503/);
    await text(page, '#editor-review-position', '1/1');
    assert.equal(await page.locator('#editor-review-prev').isDisabled(), true); assert.equal(await page.locator('#editor-review-next').isDisabled(), true);
    await editChange(page, scratch, lineOffset(scratch, 6), 'truncated full diff only exposes the first displayed hunk'); await visibleCaret(page, 'first displayed truncated hunk');
    await openReview(page); await text(page, '#editor-review-position', '1/1');
    await screenshot(page, 'editor-review-row-limit.png'); await page.locator('#editor-review-fold').check();
    assert.ok((await rows(page)).some(row => row.kind === 'added' && row.text === '-- changed last line'));
    await text(page, '#editor-review-position', '1/2'); assert.equal(await page.locator('#editor-review-notice').isVisible(), false);
    await page.locator('#editor-review-next').click(); await text(page, '#editor-review-position', '2/2');
    await editChange(page, scratch, lineOffset(scratch, 2502), 'folded tail hunk uses the real source line after earlier insertions'); await visibleCaret(page, 'folded tail hunk after earlier insertions');
    await openReview(page); await page.locator('#editor-review-fold').uncheck(); await text(page, '#editor-review-position', '1/1');
    await reviewLocation(page, scratch, lineOffset(scratch, 6)); await returnEdit(page); await value(page, scratch); await discardSourceEditor(page); await closeSettings(page);
    const lateOnly = [...original]; lateOnly[2499] = '-- only undisplayed change';
    await editSource(page, source); await replaceBuffer(page, lateOnly.join('\n')); await openReview(page); await page.locator('#editor-review-fold').uncheck();
    await text(page, '#editor-review-position', '0/0');
    assert.equal(await page.locator('#editor-review-edit').isVisible(), false, 'a clipped diff with no displayed change must not offer an edit action');
    assert.equal(await page.locator('#editor-review-location').isVisible(), false);
    await returnEdit(page); await discardSourceEditor(page);
  });

  await scenario('Byte and edit-distance limits show an explicit unavailable comparison without false zero statistics', async ({ page }) => {
    const cases = [
      { label: '256 KiB combined byte limit', source: '-- ' + '🙂'.repeat(34_000), scratch: '-- ' + '🙂'.repeat(34_000) + 'x' },
      { label: '2000-edit algorithm limit', source: Array.from({ length: 1001 }, (_, index) => `old_${index}`).join('\n'),
        scratch: Array.from({ length: 1001 }, (_, index) => `new_${index}`).join('\n') },
    ];
    for (const { label, source, scratch } of cases) {
      await editSource(page, source); const backup = await recovery(page); await replaceBuffer(page, scratch);
      const started = performance.now(); await openReview(page); const message = await notice(page, label, '#editor-review-empty');
      assert.match(message, /无法|过多|过大|不可用|超过/); assert.ok(performance.now() - started < 5000, 'a bounded comparison remains responsive');
      assert.equal(await sourceRows(page).count(), 0);
      assert.equal(await page.locator('#editor-review-summary').isVisible(), false, 'unavailable comparison must not present successful zero-change statistics');
      assert.equal(await page.locator('#editor-review-edit').isVisible(), false, 'an unavailable comparison must not offer a stale edit action');
      assert.equal(await page.locator('#editor-review-location').isVisible(), false);
      await screenshot(page, `editor-review-unavailable-${label.startsWith('256') ? 'bytes' : 'edits'}.png`);
      await returnEdit(page); await value(page, scratch); await pristine(page, source, backup); await discardSourceEditor(page); await closeSettings(page);
    }
  });

  await scenario('Native undo and redo shortcuts leave review before updating the visible scratch buffer', async ({ page }) => {
    const source = '-- before\n-- stable'; await editSource(page, source); const backup = await recovery(page);
    const first = source + '\n-- first edit'; await select(page, source.length); await page.keyboard.insertText('\n-- first edit'); await openReview(page);
    await page.locator('#editor-review-scroll').focus(); await page.keyboard.press('Control+z');
    await value(page, source); assert.equal(await page.locator('#editor-review').isVisible(), false); await focused(page, '#expanded-source');
    assert.equal(await page.locator('#editor-review-toggle').isVisible(), false); await text(page, '#editor-change-status', '未修改');
    await page.keyboard.press('Control+Shift+z'); await value(page, first);
    await select(page, 0, '-- before'.length); await page.keyboard.insertText('-- changed before');
    const second = first.replace('-- before', '-- changed before'); await value(page, second);
    await page.keyboard.press('Control+z'); await value(page, first); await openReview(page); await summary(page, 2, 1, 'review refreshed after native undo and redo');
    await page.locator('#editor-review-fold').focus(); await page.keyboard.press('Control+y');
    await value(page, second); assert.equal(await page.locator('#editor-review').isVisible(), false); await focused(page, '#expanded-source');
    await page.keyboard.press('Control+z'); await value(page, first); await openReview(page);
    await page.evaluate(() => document.querySelector('#source-editor')!.addEventListener('keydown', event => {
      if ((event as KeyboardEvent).metaKey && (event as KeyboardEvent).key.toLowerCase() === 'z') {
        (window as unknown as { __reviewMetaPrevented: boolean }).__reviewMetaPrevented = event.defaultPrevented;
      }
    }));
    await page.locator('#editor-review-fold').focus(); await page.keyboard.press('Meta+z');
    assert.equal(await page.locator('#editor-review').isVisible(), false); await focused(page, '#expanded-source');
    assert.equal(await page.evaluate(() => (window as unknown as { __reviewMetaPrevented: boolean }).__reviewMetaPrevented), false,
      'Meta undo returns to the textarea without intercepting the platform-native default');
    // Linux Chromium does not bind Meta+Z to undo; Control+Z verifies the native edit.
    await page.keyboard.press('Control+z');
    await value(page, source); assert.equal(await page.locator('#editor-review').isVisible(), false); await focused(page, '#expanded-source');
    await pristine(page, source, backup); await sameBuffer(page);
    await closeDialog(page, '#source-editor', () => page.locator('#cancel-editor').click());
    assert.equal(await page.locator('#editor-discard-dialog').isVisible(), false);
  });

  await writeReport('passed');
  console.log(`Editor review checks passed: ${checks.length} scenarios; real diff rows, frozen baselines, native editing history, reading-state preservation, revision and comparison limits.`);
  console.log(`Report: ${path.relative(root, reportFile)}`);
} catch (error) { await writeReport('failed', error); throw error; }
finally { try { await browser?.close(); } finally { await service.close(); } }
