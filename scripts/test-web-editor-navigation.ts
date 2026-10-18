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
const output = path.join(root, 'out/web-editor-navigation'), reportFile = path.join(output, 'report.json');
const widths = [1440, 375, 320];
await fs.access(path.join(root, 'out/web/app.js')).catch(() => { throw new Error('Run bun run build:web before the editor navigation check.'); });
await fs.mkdir(output, { recursive: true });
await fs.rm(reportFile, { force: true });
const probe = net.createServer();
await new Promise<void>(resolve => probe.listen(0, '127.0.0.1', resolve));
const port = (probe.address() as net.AddressInfo).port;
await new Promise<void>((resolve, reject) => probe.close(error => error ? reject(error) : resolve()));
const origin = `http://127.0.0.1:${port}`;
let workerStarts = 0, cleanedOwners = 0;
const runner: WebRunner = {
  async readiness() { return { ready: true, message: 'Local editor navigation fixture' }; },
  async run() { workerStarts++; throw new Error('Editor navigation must never start a worker'); },
};
const service = createWebService(readWebConfig({ THEOREMOS_WEB_PORT: String(port), THEOREMOS_WEB_PUBLIC_URL: origin,
  THEOREMOS_WEB_STATIC_ROOT: path.join(root, 'out/web') }), runner);
type RequestRecord = { method: string; pathname: string };
type Harness = { page: Page; context: BrowserContext; requests: RequestRecord[] };
type EditorSnapshot = { value: string; start: number; end: number; direction: string; top: number; left: number };
type Visibility = { label: string; width: number; geometry: {
  start: number; end: number; selected: string; contentWidth: number; lineHeight: number; scrollTop: number; scrollLeft: number;
  firstRect: { top: number; bottom: number; left: number; right: number }; visibleTop: number; visibleBottom: number;
  visibleLeft: number; visibleRight: number; mirrorHeight: number;
} };
const checks: Array<{ name: string; width: number; elapsedMs: number; unexpectedWrites: number; requests: RequestRecord[] }> = [];
const screenshots: string[] = [], visibility: Visibility[] = [];
const nativeInputChecks: Array<{ operation: string; before: EditorSnapshot; after: EditorSnapshot }> = [];
const overlayChecks: Array<{ label: string; width: number; marks: number; visibleMarks: number }> = [];
let browser: Awaited<ReturnType<typeof chromium.launch>> | undefined;
let activeHarness: Harness | undefined;
let failedScenario = '', failureScreenshot = '';
const normalize = (source: string) => source.replace(/\r\n?/g, '\n');

async function settled(page: Page) {
  await page.evaluate(() => new Promise<void>(resolve => requestAnimationFrame(() => requestAnimationFrame(() => resolve()))));
}
async function scenario(name: string, run: (h: Harness) => Promise<void>, width = 1440) {
  failedScenario = name;
  const started = performance.now();
  const context = await browser!.newContext({ viewport: { width, height: width > 850 ? 900 : 812 }, reducedMotion: 'reduce' });
  const page = await context.newPage(); page.setDefaultTimeout(10_000);
  const h: Harness = { page, context, requests: [] }; activeHarness = h;
  const errors: string[] = [], external: string[] = [];
  page.on('pageerror', error => errors.push(error.message));
  await context.route(/^https?:\/\//, async route => {
    const url = new URL(route.request().url());
    if (url.origin !== origin) { external.push(url.href); await route.abort(); return; }
    if (url.pathname.startsWith('/api/')) h.requests.push({ method: route.request().method(), pathname: url.pathname });
    await route.continue();
  });
  let deadline: ReturnType<typeof setTimeout> | undefined;
  try {
    await page.goto(origin); await page.locator('#submit-run:enabled').waitFor();
    await Promise.race([run(h), new Promise<never>((_, reject) => {
      deadline = setTimeout(() => reject(new Error(`Editor navigation scenario exceeded 45 seconds: ${name}`)), 45_000);
    })]);
    assert.deepEqual(errors, [], 'uncaught browser errors');
    assert.deepEqual(external, [], 'editor navigation must remain local');
    const writes = h.requests.filter(request => request.method !== 'GET');
    assert.deepEqual(writes, [], 'find, line navigation, typing and applying drafts must not POST, cancel or DELETE a run');
    assert.equal(workerStarts, 0, 'editor checks must not start a solver');
    checks.push({ name, width, elapsedMs: Math.round(performance.now() - started), unexpectedWrites: writes.length, requests: h.requests });
    console.log(`PASS ${name}`);
  } catch (error) {
    failureScreenshot = `failure-${checks.length + 1}.png`;
    await page.screenshot({ path: path.join(output, failureScreenshot) }).catch(() => {}); throw error;
  } finally {
    clearTimeout(deadline);
    try {
      const owner = (await context.cookies(origin)).find(cookie => cookie.name === 'theoremos_session')?.value;
      if (owner) {
        const remaining = service.jobs.list(owner).length;
        service.jobs.forget(owner); cleanedOwners++;
        assert.equal(remaining, 0, 'navigation must not create hidden fixture jobs');
      }
    } finally { await context.close(); }
  }
}
async function editSource(page: Page, source: string) {
  await openSettings(page);
  await page.locator('#template').selectOption('');
  await page.locator('#source').fill(source);
  await page.locator('#expand-source').click();
  await page.locator('#source-editor[open]').waitFor();
  await value(page, normalize(source));
  await focused(page, '#expanded-source');
}
async function value(page: Page, expected: string) {
  await page.waitForFunction(expected => (document.querySelector('#expanded-source') as HTMLTextAreaElement).value === expected, expected);
}
async function text(page: Page, selector: string, expected: string) {
  await page.waitForFunction(({ selector, expected }) => document.querySelector(selector)?.textContent === expected, { selector, expected });
}
async function position(page: Page, expected: string) { await text(page, '#editor-find-position', expected); }
async function focused(page: Page, selector: string) {
  assert.equal(await page.locator(selector).evaluate(node => node === document.activeElement), true, `${selector} must have focus`);
}
async function snapshot(page: Page): Promise<EditorSnapshot> {
  return page.locator('#expanded-source').evaluate(node => {
    const editor = node as HTMLTextAreaElement;
    return { value: editor.value, start: editor.selectionStart, end: editor.selectionEnd, direction: editor.selectionDirection,
      top: editor.scrollTop, left: editor.scrollLeft };
  });
}
async function select(page: Page, start: number, end = start, direction: 'forward' | 'backward' | 'none' = 'none') {
  await page.locator('#expanded-source').evaluate((node, selection) => {
    const editor = node as HTMLTextAreaElement; editor.focus({ preventScroll: true });
    editor.setSelectionRange(selection.start, selection.end, selection.direction);
  }, { start, end, direction });
}
async function selection(page: Page, start: number, end = start, selectedText = '') {
  const actual = await snapshot(page);
  assert.equal(actual.start, start, 'navigation must select the expected UTF-16 start offset');
  assert.equal(actual.end, end, 'navigation must select the expected UTF-16 end offset');
  assert.equal(actual.value.slice(actual.start, actual.end), selectedText);
}
async function openFind(page: Page) {
  if (!await page.locator('#editor-find-controls').isVisible()) await page.locator('#editor-find-toggle').click();
  assert.equal(await page.locator('#editor-navigation').isVisible(), true);
  assert.equal(await page.locator('#editor-find-controls').isVisible(), true);
  assert.equal(await page.locator('#editor-line-controls').isVisible(), false);
  await focused(page, '#editor-find-input');
}
async function openLine(page: Page) {
  if (!await page.locator('#editor-line-controls').isVisible()) await page.locator('#editor-line-toggle').click();
  assert.equal(await page.locator('#editor-navigation').isVisible(), true);
  assert.equal(await page.locator('#editor-line-controls').isVisible(), true);
  assert.equal(await page.locator('#editor-find-controls').isVisible(), false);
  await focused(page, '#editor-line-input');
}
async function search(page: Page, query: string, expected: string) {
  await page.locator('#editor-find-input').fill(query); await position(page, expected);
}
async function jump(page: Page, line: number, source: string, click = false) {
  await openLine(page); await page.locator('#editor-line-input').fill(String(line));
  if (click) await page.locator('#editor-line-go').click(); else await page.keyboard.press('Enter');
  assert.equal(await page.locator('#editor-navigation').isVisible(), false);
  assert.equal(await page.locator('#editor-line-controls').isVisible(), false);
  await focused(page, '#expanded-source');
  const start = source.split('\n').slice(0, line - 1).reduce((offset, text) => offset + text.length + 1, 0);
  await selection(page, start);
  await text(page, '#editor-position', `第 ${line} 行 · 第 1 列`);
  await settled(page);
}
async function pristine(page: Page, source: string, recovery: string | null) {
  assert.equal(await page.locator('#source').inputValue(), source, 'navigation and scratch edits must not change the draft');
  assert.equal(await page.evaluate(key => sessionStorage.getItem(key), draftRecoveryStorageKey), recovery,
    'navigation must not replace a recovery backup');
}
async function fit(page: Page, selector: string) {
  const box = await page.locator(selector).boundingBox(), viewport = page.viewportSize()!;
  assert.ok(box && box.x >= -1 && box.y >= -1 && box.x + box.width <= viewport.width + 1 && box.y + box.height <= viewport.height + 1,
    `${selector} must fit ${viewport.width}px: ${JSON.stringify(box)}`);
  assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth + 1), true, 'editor navigation must not widen the page');
}
async function screenshot(page: Page, name: string) {
  await page.screenshot({ path: path.join(output, name) }); screenshots.push(name);
}
async function visibleSelection(page: Page, label: string) {
  await settled(page);
  const geometry = await page.locator('#expanded-source').evaluate(node => {
    const editor = node as HTMLTextAreaElement, computed = getComputedStyle(editor), mirror = document.createElement('div');
    // Independently lay out one plain text node and inspect a native Range. This verifier does not use the application's locator.
    for (const property of ['font-family', 'font-size', 'font-style', 'font-weight', 'font-variant', 'line-height', 'letter-spacing',
      'word-spacing', 'text-align', 'text-indent', 'text-transform', 'direction', 'tab-size', 'word-break', 'overflow-wrap']) {
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
      // Collapsed ranges on an intermediate empty line have no box in Chromium.
      // A zero-width character at that exact offset measures the logical blank line without adding width.
      if (!rect.height && editor.selectionStart === editor.selectionEnd) {
        content.data = editor.value.slice(0, editor.selectionStart) + '\u200b' + editor.value.slice(editor.selectionStart) + '\u200b';
        range.setStart(content, editor.selectionStart); range.setEnd(content, editor.selectionStart + 1);
        rect = range.getClientRects()[0] ?? range.getBoundingClientRect();
      }
      const origin = mirror.getBoundingClientRect();
      const viewport = editor.getBoundingClientRect();
      const top = rect.top - origin.top - editor.scrollTop, bottom = rect.bottom - origin.top - editor.scrollTop;
      const left = rect.left - origin.left - editor.scrollLeft, right = rect.right - origin.left - editor.scrollLeft;
      return { start: editor.selectionStart, end: editor.selectionEnd, selected: editor.value.slice(editor.selectionStart, editor.selectionEnd),
        contentWidth: editor.clientWidth, lineHeight: parseFloat(computed.lineHeight), scrollTop: editor.scrollTop, scrollLeft: editor.scrollLeft,
        firstRect: { top, bottom, left, right }, visibleTop: Math.max(0, -viewport.top - editor.clientTop),
        visibleBottom: Math.min(editor.clientHeight, innerHeight - viewport.top - editor.clientTop),
        visibleLeft: Math.max(0, -viewport.left - editor.clientLeft),
        visibleRight: Math.min(editor.clientWidth, innerWidth - viewport.left - editor.clientLeft), mirrorHeight: origin.height };
    } finally { mirror.remove(); }
  });
  visibility.push({ label, width: page.viewportSize()!.width, geometry });
  assert.ok(geometry.firstRect.bottom > geometry.firstRect.top, `${label}: the independent native Range must occupy a rendered line`);
  assert.ok(geometry.firstRect.top >= geometry.visibleTop - 2 && geometry.firstRect.bottom <= geometry.visibleBottom + 2,
    `${label}: selected text must be vertically visible after actual wrapping: ${JSON.stringify(geometry)}`);
  assert.ok(geometry.firstRect.left >= geometry.visibleLeft - 2 && geometry.firstRect.right <= geometry.visibleRight + 2,
    `${label}: selected text must be horizontally visible: ${JSON.stringify(geometry)}`);
  return geometry;
}
async function visibleOverlay(page: Page, label: string) {
  await page.locator('#editor-match-overlay .editor-match-mark').first().waitFor({ state: 'visible' });
  await settled(page);
  const evidence = await page.evaluate(() => {
    const editor = document.querySelector<HTMLTextAreaElement>('#expanded-source')!;
    const overlay = document.querySelector<HTMLElement>('#editor-match-overlay')!;
    const bounds = editor.getBoundingClientRect();
    const left = bounds.left + editor.clientLeft, top = bounds.top + editor.clientTop;
    const right = left + editor.clientWidth, bottom = top + editor.clientHeight;
    const marks = Array.from(overlay.querySelectorAll<HTMLElement>('.editor-match-mark'));
    return { hiddenFromAssistiveTechnology: overlay.getAttribute('aria-hidden') === 'true', marks: marks.length,
      visibleMarks: marks.filter(mark => {
        const rect = mark.getBoundingClientRect(), style = getComputedStyle(mark);
        return style.display !== 'none' && style.visibility !== 'hidden' && rect.width > 0 && rect.height > 0
          && rect.left >= left - 1 && rect.right <= right + 1 && rect.top >= top - 1 && rect.bottom <= bottom + 1;
      }).length };
  });
  assert.equal(evidence.hiddenFromAssistiveTechnology, true, 'visual match rectangles must not duplicate source text for screen readers');
  assert.ok(evidence.visibleMarks >= 1, `${label}: a current-match rectangle must be visible inside the textarea: ${JSON.stringify(evidence)}`);
  overlayChecks.push({ label, width: page.viewportSize()!.width, marks: evidence.marks, visibleMarks: evidence.visibleMarks });
}
async function noOverlay(page: Page) {
  await settled(page);
  await page.waitForFunction(() => document.querySelectorAll('#editor-match-overlay .editor-match-mark').length === 0);
  assert.equal(await page.locator('#editor-match-overlay .editor-match-mark').count(), 0, 'no stale match rectangle may remain visible');
}
async function installNativeInputProbe(page: Page) {
  await page.evaluate(() => {
    document.addEventListener('input', event => {
      if (!(event.target instanceof HTMLTextAreaElement) || event.target.id !== 'expanded-source') return;
      const editor = event.target;
      (window as unknown as { __editorNativeInput: EditorSnapshot }).__editorNativeInput = { value: editor.value,
        start: editor.selectionStart, end: editor.selectionEnd, direction: editor.selectionDirection, top: editor.scrollTop, left: editor.scrollLeft };
    }, { capture: true });
  });
}
async function preservesNativeEdit(page: Page, operation: string) {
  await settled(page);
  const before = await page.evaluate(() => (window as unknown as { __editorNativeInput: EditorSnapshot }).__editorNativeInput);
  const after = await snapshot(page);
  assert.ok(before, `${operation} must produce a native textarea input event`);
  assert.equal(after.value, before.value); assert.equal(after.start, before.start); assert.equal(after.end, before.end);
  assert.equal(after.direction, before.direction);
  assert.ok(Math.abs(after.top - before.top) <= 1 && Math.abs(after.left - before.left) <= 1,
    `${operation}: recomputing navigation must preserve native caret and scroll: ${JSON.stringify({ before, after })}`);
  nativeInputChecks.push({ operation, before, after });
}
async function writeReport(status: 'passed' | 'failed', error?: unknown) {
  await fs.writeFile(reportFile, JSON.stringify({ status, checkedAt: new Date().toISOString(),
    mode: 'Real local HTTP service and Chromium. Independent plain-text DOM Range mirrors verify wrapped textarea navigation. No POST or DELETE requests, model calls, Docker or Lean.',
    nativeUndoScope: 'Chromium shares native undo transactions across text controls. The test undoes the line-number input transaction before checking that the earlier textarea edit remains undoable.',
    paidModelCalls: false, workerStarts, cleanedOwners, widths, checks, screenshots, visibility, overlayChecks, nativeInputChecks,
    unexpectedWrites: checks.reduce((sum, check) => sum + check.unexpectedWrites, 0),
    ...(error ? { failedScenario, error: error instanceof Error ? error.message : String(error), failureScreenshot, failureRequests: activeHarness?.requests } : {}) }, null, 2) + '\n');
}

try {
  await new Promise<void>((resolve, reject) => { service.server.once('error', reject); service.server.listen(port, '127.0.0.1', resolve); });
  browser = await chromium.launch({ headless: true });

  for (const width of widths) await scenario(`Literal editor find cycles from the caret and handles Unicode and case at ${width}px`, async ({ page }) => {
    const source = '-- Needle alpha\n-- 🙂x needle beta\n-- NEEDLE gamma\n-- literal [a+b]*?; aaab a+b\n';
    const first = source.indexOf('Needle'), second = source.indexOf('needle'), third = source.indexOf('NEEDLE');
    await editSource(page, source);
    const recovery = await page.evaluate(key => sessionStorage.getItem(key), draftRecoveryStorageKey);
    await select(page, second - 1); await openFind(page);
    assert.equal(await page.locator('#editor-find-input').getAttribute('maxlength'), '256');
    await search(page, 'needle', '2/3'); await selection(page, second, second + 6, 'needle');
    await page.locator('#editor-find-next').click(); await position(page, '3/3'); await selection(page, third, third + 6, 'NEEDLE');
    await page.locator('#editor-find-next').click(); await position(page, '1/3'); await selection(page, first, first + 6, 'Needle');
    await page.locator('#editor-find-prev').click(); await position(page, '3/3');
    await page.locator('#editor-find-input').focus();
    await page.keyboard.press('Enter'); await position(page, '1/3');
    await page.keyboard.press('Shift+Enter'); await position(page, '3/3');
    await page.locator('#editor-find-case').click(); await position(page, '1/1');
    assert.equal(await page.locator('#editor-find-case').getAttribute('aria-pressed'), 'true');
    await selection(page, second, second + 6, 'needle');
    await text(page, '#editor-position', '第 2 行 · 第 13 列');
    await visibleSelection(page, 'Unicode match after an astral code point');
    await visibleOverlay(page, 'Unicode match while a search control has focus');
    await search(page, '[a+b]*?', '1/1');
    const literal = source.indexOf('[a+b]*?'); await selection(page, literal, literal + 7, '[a+b]*?');
    const beforeMissing = await snapshot(page);
    await search(page, 'absent_math_lemma', '0/0');
    await noOverlay(page);
    assert.equal(await page.locator('#editor-find-prev').isDisabled(), true);
    assert.equal(await page.locator('#editor-find-next').isDisabled(), true);
    await selection(page, beforeMissing.start, beforeMissing.end, '[a+b]*?');
    await search(page, '', '0/0');
    await search(page, 'needle', '1/1');
    await visibleOverlay(page, 'current match before the responsive search screenshot');
    for (const selector of ['#source-editor', '#editor-navigation', '#editor-find-controls', '#editor-find-input', '#editor-find-position',
      '#editor-find-case', '#editor-find-prev', '#editor-find-next', '#editor-find-close', '#apply-editor']) await fit(page, selector);
    await screenshot(page, `editor-find-${width}.png`);
    await pristine(page, source, recovery);
    await page.locator('#editor-find-close').click(); await focused(page, '#expanded-source');
    await noOverlay(page);
    assert.equal(await page.locator('#editor-navigation').isVisible(), false);
    await closeDialog(page, '#source-editor', () => page.locator('#close-editor').click());
    assert.equal(await page.locator('#editor-discard-dialog').isVisible(), false);
    await closeSettings(page);
  }, width);

  for (const width of widths) await scenario(`Find and logical-line jumps reveal wrapped long Lean text beyond line 160 at ${width}px`, async ({ page }) => {
    const lines = Array.from({ length: 222 }, (_, index) => `-- context ${index + 1}`);
    lines[0] = `-- ${'long_word '.repeat(400)}`;
    lines[7] = '';
    lines[174] = `-- ${'continuation '.repeat(60)}needleAfter175`;
    lines[204] = '-- finalNeedle'; lines[221] = '';
    const source = lines.join('\n'); await editSource(page, source);
    const recovery = await page.evaluate(key => sessionStorage.getItem(key), draftRecoveryStorageKey);
    await jump(page, 175, source);
    const lineGeometry = await visibleSelection(page, 'line 175 after hundreds of soft wraps');
    assert.ok(lineGeometry.scrollTop > lineGeometry.lineHeight * 174 + 250,
      'wrapped lines above the target must contribute to the scroll offset');
    await openFind(page); await search(page, 'needleAfter175', '1/1');
    const match = source.indexOf('needleAfter175'); await selection(page, match, match + 14, 'needleAfter175');
    const wrapped = await visibleSelection(page, 'match deep inside a wrapped logical line');
    await visibleOverlay(page, 'wrapped current match while the query input has focus');
    assert.ok(wrapped.scrollTop > lineGeometry.lineHeight * 174 + 250);
    const cursor = await page.locator('#editor-position').evaluate(node => ({ text: node.textContent, title: (node as HTMLElement).title,
      height: node.getBoundingClientRect().height, lineHeight: parseFloat(getComputedStyle(node).lineHeight) }));
    assert.equal(cursor.title, cursor.text, 'the full cursor location remains available when narrow layouts truncate it');
    assert.ok(cursor.height <= cursor.lineHeight + 1, 'long cursor locations must remain on one toolbar line');
    await screenshot(page, `editor-wrapped-match-${width}.png`);
    await openLine(page);
    await noOverlay(page);
    assert.match(await page.locator('#editor-line-range').innerText(), /222/);
    for (const selector of ['#editor-navigation', '#editor-line-controls', '#editor-line-input', '#editor-line-range', '#editor-line-go', '#editor-line-close']) await fit(page, selector);
    await screenshot(page, `editor-line-${width}.png`);
    await jump(page, 222, source, true); await visibleSelection(page, 'last blank logical line');
    await jump(page, 8, source); await visibleSelection(page, 'middle blank logical line');
    await jump(page, 1, source); await visibleSelection(page, 'first logical line');
    assert.ok((await snapshot(page)).top <= 1, 'jumping to the first line returns to the beginning');
    await pristine(page, source, recovery);
    await closeDialog(page, '#source-editor', () => page.locator('#cancel-editor').click()); await closeSettings(page);
  }, width);

  await scenario('Invalid line requests preserve the caret and scroll while showing a usable local error', async ({ page }) => {
    const source = Array.from({ length: 220 }, (_, index) => `-- line ${index + 1}`).join('\n');
    await editSource(page, source); await jump(page, 175, source);
    const before = await snapshot(page); await openLine(page);
    for (const invalid of ['', '0', '-1', '1.5', '221', '9007199254740992']) {
      await page.locator('#editor-line-input').fill(invalid); await page.keyboard.press('Enter');
      assert.equal(await page.locator('#editor-line-controls').isVisible(), true);
      assert.equal(await page.locator('#editor-line-error').isVisible(), true);
      assert.ok((await page.locator('#editor-line-error').innerText()).trim());
      await focused(page, '#editor-line-input');
      await selection(page, before.start);
      const after = await snapshot(page);
      assert.ok(Math.abs(after.top - before.top) <= 1, `invalid ${invalid} must not navigate the source`);
    }
    await screenshot(page, 'editor-line-invalid.png');
    await page.locator('#editor-line-input').fill('20');
    assert.equal(await page.locator('#editor-line-error').isVisible(), false);
    await page.locator('#editor-line-go').click(); await selection(page, source.indexOf('-- line 20\n'));
    await focused(page, '#expanded-source');
    await closeDialog(page, '#source-editor', () => page.locator('#cancel-editor').click());
  });

  await scenario('Native edits recompute matches without changing the caret or scroll and keep undo and redo intact', async ({ page }) => {
    const lines = Array.from({ length: 180 }, (_, index) => `-- row ${index + 1}`);
    lines[0] += ' needle'; lines[89] += ' needle'; lines[179] += ' needle';
    const source = lines.join('\n'); await editSource(page, source);
    const recovery = await page.evaluate(key => sessionStorage.getItem(key), draftRecoveryStorageKey);
    await openFind(page); await search(page, 'needle', '1/3');
    await installNativeInputProbe(page);
    const insertion = source.indexOf('-- row 20\n');
    await select(page, insertion);
    await page.locator('#expanded-source').evaluate(node => { node.scrollTop = 180; });
    await page.keyboard.insertText('-- needle inserted\n');
    await noOverlay(page);
    const edited = source.slice(0, insertion) + '-- needle inserted\n' + source.slice(insertion);
    await value(page, edited); assert.match(await page.locator('#editor-find-position').innerText(), /^\d+\/4$/);
    await preservesNativeEdit(page, 'ordinary insertion');
    await page.keyboard.press('Control+z'); await value(page, source);
    assert.match(await page.locator('#editor-find-position').innerText(), /^\d+\/3$/);
    await preservesNativeEdit(page, 'undo');
    await page.keyboard.press('Control+Shift+z'); await value(page, edited);
    assert.match(await page.locator('#editor-find-position').innerText(), /^\d+\/4$/);
    await preservesNativeEdit(page, 'redo');
    await page.locator('#editor-find-next').click(); await jump(page, 100, edited);
    // Chromium's native undo history spans text controls: the first transaction belongs to entering line 100.
    // Undo that request, then verify the original source transaction still exists behind it.
    await page.keyboard.press('Control+z'); await page.keyboard.press('Control+z'); await value(page, source);
    await pristine(page, source, recovery);
    await closeDialog(page, '#source-editor', () => page.locator('#cancel-editor').click());
    assert.equal(await page.locator('#editor-discard-dialog').isVisible(), false, 'undo back to the original source remains clean');
  });

  await scenario('Editor shortcuts respect IME and Escape closes a navigation tool before asking about dirty changes', async ({ page }) => {
    const source = 'theorem navigation_escape_fixture : True := by\n  sorry';
    await editSource(page, source);
    for (const key of ['f', 'g']) {
      assert.equal(await page.locator('#expanded-source').evaluate((node, key) => node.dispatchEvent(new KeyboardEvent('keydown', {
        key, ctrlKey: true, isComposing: true, bubbles: true, cancelable: true,
      })), key), true, 'IME shortcuts must not be prevented');
      assert.equal(await page.locator('#editor-navigation').isVisible(), false);
    }
    await page.keyboard.press('Control+f'); await focused(page, '#editor-find-input');
    await search(page, 'sorry', '1/1'); await page.keyboard.press('Meta+g'); await focused(page, '#editor-line-input');
    assert.equal(await page.locator('#editor-find-controls').isVisible(), false);
    await page.keyboard.press('Meta+f'); await focused(page, '#editor-find-input');
    await page.locator('#editor-find-input').fill('sorry');
    await page.locator('#editor-find-input').evaluate(node => node.dispatchEvent(new KeyboardEvent('keydown', {
      key: 'Enter', isComposing: true, bubbles: true, cancelable: true,
    })));
    await position(page, '1/1');
    await page.keyboard.press('Escape'); await focused(page, '#expanded-source');
    assert.equal(await page.locator('#source-editor').evaluate(dialog => (dialog as HTMLDialogElement).open), true);
    await select(page, source.length); await page.keyboard.insertText('\n-- pending change');
    await page.keyboard.press('Control+f'); await search(page, 'pending', '1/1');
    await page.keyboard.press('Escape');
    assert.equal(await page.locator('#editor-navigation').isVisible(), false);
    assert.equal(await page.locator('#editor-discard-dialog').isVisible(), false); await focused(page, '#expanded-source');
    await page.keyboard.press('Escape'); await page.locator('#editor-discard-dialog[open]').waitFor();
    await closeDialog(page, '#editor-discard-dialog', () => page.locator('#keep-editing').click());
    await value(page, source + '\n-- pending change'); await focused(page, '#expanded-source');
    await page.keyboard.press('Control+g'); await page.keyboard.press('Escape');
    assert.equal(await page.locator('#editor-navigation').isVisible(), false);
    assert.equal(await page.locator('#editor-discard-dialog').isVisible(), false);
    await discardSourceEditor(page, () => page.keyboard.press('Escape'));
    await closeSettings(page);
    for (const key of ['f', 'g']) assert.equal(await page.locator('#task').evaluate((node, key) => node.dispatchEvent(new KeyboardEvent('keydown', {
      key, ctrlKey: true, bubbles: true, cancelable: true,
    })), key), true, 'editor shortcuts must not intercept the draft task input');
  });

  await scenario('Query length and match-count caps remain explicit and navigation wraps at the displayed boundary', async ({ page }) => {
    const longQuery = 'a'.repeat(256), source = `${longQuery}\n${Array.from({ length: 1005 }, (_, index) => `-- needle ${index + 1}`).join('\n')}`;
    await editSource(page, source); await openFind(page);
    await page.locator('#editor-find-input').press('Control+a'); await page.keyboard.insertText('a'.repeat(257));
    assert.equal((await page.locator('#editor-find-input').inputValue()).length, 256, 'native query input must enforce maxlength 256');
    await position(page, '1/1'); await selection(page, 0, 256, longQuery);
    await search(page, 'needle', '1/1000+');
    await page.locator('#editor-find-prev').click(); await position(page, '1000/1000+');
    const last = source.indexOf('needle 1000'); await selection(page, last, last + 6, 'needle');
    await page.locator('#editor-find-next').click(); await position(page, '1/1000+');
    await search(page, '', '0/0');
    assert.equal(await page.locator('#editor-find-next').isDisabled(), true);
    assert.equal(await page.locator('#editor-find-prev').isDisabled(), true);
    await screenshot(page, 'editor-find-limits.png');
    await closeDialog(page, '#source-editor', () => page.locator('#close-editor').click());
  });

  await scenario('Switching tools is exclusive and reopening the editor starts a fresh navigation session', async ({ page }) => {
    const source = '-- Needle\r\n\r\n-- needle\r\n'; const normalized = normalize(source);
    await editSource(page, source); await openFind(page); await search(page, 'needle', '1/2');
    await page.locator('#editor-find-case').click(); await position(page, '1/1');
    await openLine(page); assert.equal(await page.locator('#editor-find-controls').isVisible(), false);
    await page.locator('#editor-line-close').click();
    assert.equal(await page.locator('#editor-navigation').isVisible(), false); await focused(page, '#expanded-source');
    await openFind(page);
    assert.equal(await page.locator('#editor-find-input').inputValue(), 'needle');
    assert.equal(await page.locator('#editor-find-case').getAttribute('aria-pressed'), 'true');
    await jump(page, 3, normalized);
    await closeDialog(page, '#source-editor', () => page.locator('#close-editor').click());
    await page.locator('#expand-source').click(); await page.locator('#source-editor[open]').waitFor();
    assert.equal(await page.locator('#editor-navigation').isVisible(), false);
    await selection(page, 0); await openFind(page);
    assert.equal(await page.locator('#editor-find-input').inputValue(), '');
    assert.equal(await page.locator('#editor-find-case').getAttribute('aria-pressed'), 'false');
    await position(page, '0/0'); await value(page, normalized);
    await closeDialog(page, '#source-editor', () => page.locator('#cancel-editor').click());
  });

  await scenario('Applying after navigation creates one recoverable draft update and reopening clears old undo and search state', async ({ page }) => {
    const source = 'theorem navigation_apply_fixture : True := by\n  sorry';
    await editSource(page, source); await openFind(page); await search(page, 'sorry', '1/1');
    await page.locator('#editor-find-close').click(); await select(page, source.length);
    await page.keyboard.insertText('\n-- applied navigation fixture');
    const edited = source + '\n-- applied navigation fixture';
    await openFind(page); await search(page, 'applied', '1/1');
    await closeDialog(page, '#source-editor', () => page.locator('#apply-editor').click());
    assert.equal(await page.locator('#source').inputValue(), edited);
    const recovery = await page.evaluate(key => JSON.parse(sessionStorage.getItem(key)!), draftRecoveryStorageKey);
    assert.equal(recovery.reason, 'edit'); assert.equal(recovery.task.draft.source, source);
    assert.equal(await page.locator('#editor-discard-dialog').isVisible(), false);
    await page.locator('#expand-source').click(); await page.keyboard.press('Control+z'); await value(page, edited);
    assert.equal(await page.locator('#editor-navigation').isVisible(), false);
    await openFind(page); assert.equal(await page.locator('#editor-find-input').inputValue(), '');
    await position(page, '0/0');
    await closeDialog(page, '#source-editor', () => page.locator('#cancel-editor').click());
  });

  await writeReport('passed');
  console.log(`Editor navigation checks passed: ${checks.length} scenarios; literal and Unicode find, wrapping and line navigation, native undo, Escape protection and no API writes.`);
  console.log(`Report: ${path.relative(root, reportFile)}`);
} catch (error) { await writeReport('failed', error); throw error; }
finally { try { await browser?.close(); } finally { await service.close(); } }
