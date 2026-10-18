#!/usr/bin/env bun
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import net from 'node:net';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium, type BrowserContext, type Page } from 'playwright';
import { readWebConfig, webLimits } from '../apps/web/config';
import { createWebService } from '../apps/web/server';
import type { WebRunner } from '../apps/web/runner';
import type { WebResult, WebRun, WebRunInput } from '../apps/web/shared';
import { closeHistory, closeSettings, fillConfig, openHistory, openSettings, selectHistoryRun } from './web-ui-controls';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const output = path.join(root, 'out/web-ui-smoke');
const reportFile = path.join(output, 'source-reader-report.json');
const credential = `sk-theoremos-reader-fixture-${crypto.randomUUID()}`;
const markup = '<img data-reader-injection src=x onerror="window.__readerInjected=true">';
const widths = [1440, 375, 320];
const draftCode = '#draft-preview-code code', draftScroll = '.draft-source-scroll';
const runCode = '#detail-panel .source-code code', runScroll = '#detail-panel .source-code-grid';
const normalize = (source: string) => source.replace(/\r\n?/g, '\n');
await fs.access(path.join(root, 'out/web/app.js')).catch(() => { throw new Error('Run bun run build:web before the source reader check.'); });
await fs.mkdir(output, { recursive: true });
await fs.rm(reportFile, { force: true });
const probe = net.createServer();
await new Promise<void>(resolve => probe.listen(0, '127.0.0.1', resolve));
const port = (probe.address() as net.AddressInfo).port;
await new Promise<void>((resolve, reject) => probe.close(error => error ? reject(error) : resolve()));
const origin = `http://127.0.0.1:${port}`;
type Control = { artifact(source: string): void; progress(message: string): void; finish(result?: WebResult): void };
const controls = new Map<string, Control>();
let workerStarts = 0;
const runner: WebRunner = {
  async readiness() { return { ready: true, message: 'Local source reader fixture' }; },
  async run(input, send, signal) {
    workerStarts++;
    await new Promise<void>((resolve, reject) => {
      const cleanup = () => { controls.delete(input.id); signal.removeEventListener('abort', abort); };
      const abort = () => { cleanup(); reject(new Error('Cancelled source reader fixture')); };
      signal.addEventListener('abort', abort, { once: true });
      controls.set(input.id, {
        artifact: source => send({ type: 'artifact', artifact: { source, workerId: 'reader-fixture', capturedAt: new Date().toISOString(), status: 'candidate' } }),
        progress: message => send({ type: 'progress', event: 'worker_activity', message }),
        finish: result => { if (result) send({ type: 'result', result }); cleanup(); resolve(); },
      });
      if (signal.aborted) abort();
    });
  },
};
const service = createWebService(readWebConfig({ THEOREMOS_WEB_PORT: String(port), THEOREMOS_WEB_PUBLIC_URL: origin,
  THEOREMOS_WEB_STATIC_ROOT: path.join(root, 'out/web'), THEOREMOS_WEB_CONCURRENCY: '8' }), runner);
type RequestRecord = { method: string; pathname: string };
type Harness = { page: Page; context: BrowserContext; requests: RequestRecord[]; runIds: string[] };
type HighlightRegistry = { get(name: string): Iterable<Range> | undefined };
const checks: Array<{ name: string; elapsedMs: number; requests: RequestRecord[]; fixtureCreates: number }> = [];
const screenshots: string[] = [];
const visibility: Array<{ label: string; width: number; geometry: unknown }> = [];
let browser: Awaited<ReturnType<typeof chromium.launch>> | undefined;
let failedScenario = '', failureScreenshot = '';

async function scenario(name: string, run: (h: Harness) => Promise<void>, width = 1440, withoutHighlights = false) {
  failedScenario = name;
  const started = performance.now();
  const context = await browser!.newContext({ viewport: { width, height: width > 850 ? 900 : 812 },
    reducedMotion: 'reduce', permissions: ['clipboard-read', 'clipboard-write'] });
  if (withoutHighlights) await context.addInitScript(() => {
    Object.defineProperty(CSS, 'highlights', { configurable: true, value: undefined });
    Object.defineProperty(window, 'Highlight', { configurable: true, value: undefined });
  });
  const page = await context.newPage();
  page.setDefaultTimeout(10_000);
  const h: Harness = { page, context, requests: [], runIds: [] };
  const errors: string[] = [], external: string[] = [];
  page.on('pageerror', error => errors.push(error.message));
  await context.route(/^https?:\/\//, async route => {
    const destination = new URL(route.request().url());
    if (destination.origin !== origin) { external.push(destination.href); await route.abort(); return; }
    if (destination.pathname.startsWith('/api/')) h.requests.push({ method: route.request().method(), pathname: destination.pathname });
    await route.continue();
  });
  let deadline: ReturnType<typeof setTimeout> | undefined;
  try {
    await page.goto(origin);
    await page.locator('#submit-run:enabled').waitFor();
    await Promise.race([run(h), new Promise<never>((_, reject) => {
      deadline = setTimeout(() => reject(new Error(`Source reader scenario exceeded 45 seconds: ${name}`)), 45_000);
    })]);
    assert.deepEqual(errors, [], 'uncaught browser errors');
    assert.deepEqual(external, [], 'source reading must not contact an external site or provider');
    const writes = h.requests.filter(request => request.method !== 'GET');
    assert.equal(writes.length, h.runIds.length, 'search must not create, change or delete runs');
    assert.equal(writes.every(request => request.method === 'POST' && request.pathname === '/api/runs'), true);
    checks.push({ name, elapsedMs: Math.round(performance.now() - started), requests: h.requests, fixtureCreates: h.runIds.length });
    console.log(`PASS ${name}`);
  } catch (error) {
    failureScreenshot = `source-reader-failure-${checks.length + 1}.png`;
    await page.screenshot({ path: path.join(output, failureScreenshot) }).catch(() => {});
    throw error;
  } finally {
    clearTimeout(deadline);
    for (const id of h.runIds) controls.get(id)?.finish();
    await context.close();
  }
}
async function text(page: Page, selector: string, expected: string) {
  await page.waitForFunction(({ selector, expected }) => document.querySelector(selector)?.textContent === expected, { selector, expected });
}
async function position(page: Page, expected: string) { await text(page, '#source-find-position', expected); }
async function showSource(page: Page) {
  if (page.viewportSize()!.width <= 850) await page.locator('#mobile-runs').click();
}
async function openFind(page: Page) {
  await page.locator('#open-source-find').click();
  await page.locator('#source-find-controls:not([hidden])').waitFor();
  assert.equal(await page.locator('#open-source-find').getAttribute('aria-expanded'), 'true');
  assert.equal(await page.locator('#source-find-input').evaluate(input => input === document.activeElement), true);
  assert.equal(await page.locator('#source-find-input').getAttribute('maxlength'), '256');
  assert.equal(await page.locator('#source-find-position').getAttribute('role'), 'status');
}
async function search(page: Page, query: string, expected: string) {
  await page.locator('#source-find-input').fill(query);
  await position(page, expected);
}
async function openLine(page: Page) {
  await page.locator('#open-source-line').click();
  await page.locator('#source-line-controls:not([hidden])').waitFor();
  assert.equal(await page.locator('#open-source-line').getAttribute('aria-expanded'), 'true');
  assert.equal(await page.locator('#source-line-input').evaluate(input => input === document.activeElement), true);
  assert.equal(await page.locator('#source-find-controls').isVisible(), false);
}
async function jumpLine(page: Page, line: number) {
  await openLine(page);
  await page.locator('#source-line-input').fill(String(line));
  await page.keyboard.press('Enter');
  assert.equal(await page.locator('#source-line-controls').isVisible(), false);
  assert.match(await page.locator('#source-find-location').innerText(), new RegExp(`^第 ${line} 行`));
}
async function lineVisible(page: Page, line: number, scrollSelector: string, expected: string, fallback = false) {
  const geometry = await page.locator(scrollSelector).evaluate((scroll, { line, fallback }) => {
    const numbers = scroll.querySelector('.source-line-numbers,.preview-line-numbers')!;
    const lines = numbers.textContent!.split('\n');
    const start = lines.slice(0, line - 1).join('\n').length + (line > 1 ? 1 : 0);
    const range = document.createRange();
    range.setStart(numbers.firstChild!, start); range.setEnd(numbers.firstChild!, start + String(line).length);
    const row = range.getBoundingClientRect(), frame = scroll.getBoundingClientRect();
    const highlights = fallback ? [] : Array.from((CSS as unknown as { highlights: HighlightRegistry }).highlights.get('source-line') ?? []);
    return { number: range.toString(), text: highlights.map(item => item.toString()),
      top: row.top, bottom: row.bottom, left: row.left, right: row.right,
      visibleTop: Math.max(frame.top + scroll.clientTop, 0),
      visibleBottom: Math.min(frame.top + scroll.clientTop + scroll.clientHeight, innerHeight),
      leftScroll: scroll.scrollLeft, pageWidth: innerWidth, background: fallback ? ''
        : getComputedStyle(scroll.querySelector('code')!, '::highlight(source-line)').backgroundColor };
  }, { line, fallback });
  visibility.push({ label: `line ${line}`, width: page.viewportSize()!.width, geometry });
  assert.equal(geometry.number, String(line));
  assert.ok(geometry.top >= geometry.visibleTop - 1 && geometry.bottom <= geometry.visibleBottom + 1,
    `target line must be visible: ${JSON.stringify(geometry)}`);
  assert.ok(geometry.left >= 0 && geometry.right <= geometry.pageWidth);
  assert.equal(geometry.leftScroll, 0, 'line navigation returns to the start of a long line');
  if (!fallback) {
    assert.deepEqual(geometry.text, [expected]);
    assert.ok(geometry.background && !['transparent', 'rgba(0, 0, 0, 0)'].includes(geometry.background));
  }
}
async function screenshot(page: Page, name: string) {
  await page.screenshot({ path: path.join(output, name) }); screenshots.push(name);
}
async function noInjection(page: Page) {
  assert.equal(await page.locator('[data-reader-injection]').count(), 0, 'Lean and queries must remain inert text');
  assert.equal(await page.evaluate(() => (window as unknown as { __readerInjected?: boolean }).__readerInjected), undefined);
}
async function plainTextNode(page: Page, selector: string, expected: string) {
  await text(page, selector, expected);
  assert.equal(await page.locator(selector).evaluate(code => code.childNodes.length === 1 && code.firstChild?.nodeType === Node.TEXT_NODE), true,
    'source reading must retain a single plain text node');
}
async function fit(page: Page, selector: string) {
  const box = await page.locator(selector).boundingBox(), viewport = page.viewportSize()!;
  assert.ok(box && box.x >= -1 && box.y >= -1 && box.x + box.width <= viewport.width + 1 && box.y + box.height <= viewport.height + 1,
    `${selector} must fit the ${viewport.width}px viewport: ${JSON.stringify(box)}`);
  assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth + 1), true, 'source tools must not widen the page');
}
async function matchVisible(page: Page, label: string, codeSelector: string, scrollSelector: string, expectedText: string, fallback = false) {
  const geometry = await page.evaluate(({ codeSelector, scrollSelector, expectedText, fallback }) => {
    const scroll = document.querySelector<HTMLElement>(scrollSelector)!;
    const registry = (CSS as unknown as { highlights?: HighlightRegistry }).highlights;
    let ranges = Array.from(registry?.get('source-current') ?? []);
    if (fallback) {
      const node = document.querySelector(codeSelector)!.firstChild!;
      const start = node.textContent!.indexOf(expectedText), range = document.createRange();
      if (start < 0) return { found: false };
      range.setStart(node, start); range.setEnd(node, start + expectedText.length); ranges = [range];
    }
    if (ranges.length !== 1) return { found: false, ranges: ranges.length };
    const range = ranges[0]!, rect = range.getBoundingClientRect(), frame = scroll.getBoundingClientRect();
    const gutter = scroll.querySelector('.source-line-numbers,.preview-line-numbers')?.getBoundingClientRect();
    const visible = { top: Math.max(frame.top + scroll.clientTop, 0), left: Math.max(gutter?.right ?? frame.left, 0),
      right: Math.min(frame.left + scroll.clientLeft + scroll.clientWidth, innerWidth),
      bottom: Math.min(frame.top + scroll.clientTop + scroll.clientHeight, innerHeight) };
    return { found: true, text: range.toString(), range: { top: rect.top, right: rect.right, bottom: rect.bottom, left: rect.left }, visible,
      fullyVisible: rect.width > 0 && rect.height > 0 && rect.top >= visible.top - 1 && rect.left >= visible.left - 1 &&
        rect.right <= visible.right + 1 && rect.bottom <= visible.bottom + 1, scrollTop: scroll.scrollTop, scrollLeft: scroll.scrollLeft,
      background: getComputedStyle(document.querySelector(codeSelector)!, '::highlight(source-current)').backgroundColor };
  }, { codeSelector, scrollSelector, expectedText, fallback });
  visibility.push({ label, width: page.viewportSize()!.width, geometry });
  assert.equal(geometry.found, true, `one current match must exist: ${JSON.stringify(geometry)}`);
  assert.equal(geometry.text, expectedText);
  assert.equal(geometry.fullyVisible, true, `current match must be visible below the toolbar and beside the sticky gutter: ${JSON.stringify(geometry)}`);
  if (!fallback) assert.ok(geometry.background && !['transparent', 'rgba(0, 0, 0, 0)'].includes(geometry.background), 'current search result must have a painted highlight');
}
async function createRun(h: Harness, source: string, proof?: string) {
  const input: WebRunInput = { providerId: 'openai', apiKey: credential, model: 'fixture-reader-model', effort: 'low', environment: 'standard',
    source, task: 'Inspect the local source reader fixture', maxTurns: 2, maxRunSeconds: 60, workers: 1, coordination: 'independent' };
  const run = await h.page.evaluate(async input => {
    const session = await (await fetch('/api/session')).json();
    const response = await fetch('/api/runs', { method: 'POST', headers: { 'Content-Type': 'application/json', 'X-CSRF-Token': session.csrfToken }, body: JSON.stringify(input) });
    if (response.status !== 201) throw new Error(`Fixture creation failed: ${response.status}`);
    return (await response.json()).run as WebRun;
  }, input);
  h.runIds.push(run.id);
  assert.ok(controls.has(run.id));
  if (proof !== undefined) controls.get(run.id)!.finish({ status: 'incomplete', proof, report: { fixture: 'source-reader' } });
  return run;
}
async function selectSource(h: Harness, id: string) {
  await openHistory(h.page);
  await h.page.locator('#refresh-runs:enabled').waitFor();
  const response = h.page.waitForResponse(response => new URL(response.url()).pathname === '/api/runs' && response.request().method() === 'GET');
  await h.page.locator('#refresh-runs').click(); await response;
  await h.page.locator('#refresh-runs:enabled').waitFor();
  await closeHistory(h.page);
  await selectHistoryRun(h.page, id);
  await showSource(h.page);
  await h.page.locator('#detail-tab-source').click();
}
async function writeReport(status: 'passed' | 'failed', error?: unknown) {
  const report = { status, checkedAt: new Date().toISOString(),
    mode: 'Real local HTTP service and Chromium with a controlled fixture runner. No Docker, Lean or model provider is called.',
    paidModelCalls: false, workerStarts, widths, checks, screenshots, visibility,
    ...(error ? { failedScenario, error: error instanceof Error ? error.message : String(error), failureScreenshot } : {}) };
  assert.equal(JSON.stringify(report).includes(credential), false);
  await fs.writeFile(reportFile, JSON.stringify(report, null, 2) + '\n');
}

const longLines = Array.from({ length: 220 }, (_, index) => `-- context line ${index + 1}`);
longLines[14] = `-- ${'long_identifier_'.repeat(40)}needleFar`;
longLines[174] = '-- NeedleAfter160';
longLines[204] = '-- needleEnd';
const longSource = longLines.join('\n');

try {
  await new Promise<void>((resolve, reject) => { service.server.once('error', reject); service.server.listen(port, '127.0.0.1', resolve); });
  browser = await chromium.launch({ headless: true });

  for (const width of widths) await scenario(`Draft find reaches beyond 160 lines and long horizontal code at ${width}px`, async h => {
    const { page } = h;
    await fillConfig(page, 'source', longSource);
    await showSource(page);
    await text(page, draftCode, longLines.slice(0, 160).join('\n'));
    assert.match(await page.locator('.preview-source-heading>span').innerText(), /前 160/);
    await openFind(page);
    await plainTextNode(page, draftCode, longSource);
    assert.doesNotMatch(await page.locator('.preview-source-heading>span').innerText(), /前 160/);
    assert.equal(await page.locator('#source-find-case').getAttribute('aria-pressed'), 'false');
    await search(page, 'needle', '1/3');
    await matchVisible(page, 'first long-line match', draftCode, draftScroll, 'needle');
    assert.ok(await page.locator(draftScroll).evaluate(scroll => scroll.scrollLeft) > 100, 'finding a distant column must scroll horizontally');
    await page.locator('#source-find-next').click(); await position(page, '2/3');
    assert.match(await page.locator('#source-find-location').innerText(), /第 175 行/);
    await matchVisible(page, 'match beyond draft preview', draftCode, draftScroll, 'Needle');
    await page.locator('#source-find-next').click(); await position(page, '3/3');
    await matchVisible(page, 'last draft match', draftCode, draftScroll, 'needle');
    await page.locator('#source-find-next').click(); await position(page, '1/3');
    await matchVisible(page, 'wrapped draft match', draftCode, draftScroll, 'needle');
    await page.locator('#source-find-prev').click(); await position(page, '3/3');
    await page.locator('#source-find-input').focus();
    await page.keyboard.press('Enter'); await position(page, '1/3');
    await page.keyboard.press('Shift+Enter'); await position(page, '3/3');
    await page.locator('#source-find-input').evaluate(input => input.dispatchEvent(new KeyboardEvent('keydown', { key: 'Enter', isComposing: true, bubbles: true, cancelable: true })));
    await position(page, '3/3');
    await search(page, 'Needle', '1/3');
    await page.locator('#source-find-case').click(); await position(page, '1/1');
    await matchVisible(page, 'case-sensitive draft match', draftCode, draftScroll, 'Needle');
    await screenshot(page, `source-reader-${width}.png`);
    for (const selector of ['.source-reader', '#source-find-input', '#source-find-prev', '#source-find-next', '#source-find-case', '#close-source-find']) await fit(page, selector);
    await page.locator('#source-find-input').focus(); await page.keyboard.press('Escape');
    assert.equal(await page.locator('#source-find-controls').isVisible(), false);
    assert.equal(await page.locator(draftScroll).evaluate(scroll => scroll === document.activeElement), true);
    await page.keyboard.press('Control+f');
    assert.equal(await page.locator('#source-find-input').evaluate(input => input === document.activeElement), true);
    await page.locator('#close-source-find').click();
    assert.equal(await page.locator(draftScroll).evaluate(scroll => scroll === document.activeElement), true);
    await page.keyboard.press('Meta+f');
    assert.equal(await page.locator('#source-find-input').evaluate(input => input === document.activeElement), true);
    await page.locator('#close-source-find').click();
    assert.equal(await page.locator('#source').inputValue(), longSource, 'finding must not modify the submitted source');
  }, width);

  for (const width of widths) await scenario(`Line navigation validates input and reaches first, last and blank draft lines at ${width}px`, async h => {
    const { page } = h;
    const source = `${longSource}\n\n`;
    await fillConfig(page, 'source', source); await showSource(page);
    await openLine(page);
    await plainTextNode(page, draftCode, source);
    assert.equal(await page.locator('#source-line-input').getAttribute('max'), '222');
    await screenshot(page, `source-line-${width}-controls.png`);
    for (const selector of ['.source-reader', '#source-line-controls', '#source-line-input', '#source-line-go', '#close-source-line']) await fit(page, selector);
    await page.locator('#source-line-input').fill('175');
    await page.locator('#source-line-go').click();
    await lineVisible(page, 175, draftScroll, longLines[174]!);
    assert.equal(await page.locator(draftScroll).evaluate(scroll => scroll === document.activeElement), true);
    await page.evaluate(({ code, scroll }) => {
      const source = document.querySelector(code)!;
      (window as unknown as { __lineProbe: unknown }).__lineProbe = { source, node: source.firstChild, scroll: document.querySelector(scroll) };
    }, { code: draftCode, scroll: draftScroll });
    await openLine(page);
    const top = await page.locator(draftScroll).evaluate(scroll => scroll.scrollTop);
    for (const invalid of ['', '0', '-1', '223', '1.5', '1e2']) {
      await page.locator('#source-line-input').fill(invalid);
      await page.keyboard.press('Enter');
      assert.equal(await page.locator('#source-line-input').getAttribute('aria-invalid'), 'true');
      assert.equal(await page.locator('#source-line-error').isVisible(), true);
      assert.match(await page.locator('#source-line-error').innerText(), /1 至 222/);
      assert.equal(await page.locator(draftScroll).evaluate(scroll => scroll.scrollTop), top, 'invalid line input must not change reading position');
    }
    await screenshot(page, `source-line-${width}-validation.png`);
    await fit(page, '#source-line-error');
    await page.locator('#source-line-input').fill('15');
    assert.equal(await page.locator('#source-line-input').getAttribute('aria-invalid'), 'false');
    const composing = await page.locator('#source-line-input').evaluate(input => input.dispatchEvent(new KeyboardEvent('keydown', {
      key: 'Enter', isComposing: true, bubbles: true, cancelable: true,
    })));
    assert.equal(composing, true, 'line navigation must not consume IME confirmation');
    assert.equal(await page.locator('#source-line-controls').isVisible(), true);
    await page.keyboard.press('Escape');
    for (const line of [1, 15, 205, 220, 221, 222]) {
      await jumpLine(page, line);
      await lineVisible(page, line, draftScroll, source.split('\n')[line - 1]!);
    }
    const stable = await page.evaluate(({ code, scroll }) => {
      const before = (window as unknown as { __lineProbe: { source: Element; node: Node; scroll: Element } }).__lineProbe;
      return { source: before.source === document.querySelector(code), node: before.node === document.querySelector(code)!.firstChild,
        scroll: before.scroll === document.querySelector(scroll) };
    }, { code: draftCode, scroll: draftScroll });
    assert.deepEqual(stable, { source: true, node: true, scroll: true });
    await openFind(page); await search(page, 'needle', '1/3');
    await jumpLine(page, 175); await lineVisible(page, 175, draftScroll, longLines[174]!);
    await screenshot(page, `source-line-${width}-target.png`);
    await openFind(page); await position(page, '1/3');
    assert.equal(await page.locator('#source-find-input').inputValue(), 'needle', 'switching tools preserves the text query');
    await page.locator('#close-source-find').click();
    for (const modifier of ['Control', 'Meta']) {
      await page.keyboard.press(`${modifier}+g`);
      assert.equal(await page.locator('#source-line-input').evaluate(input => input === document.activeElement), true);
      await page.keyboard.press('Escape');
      assert.equal(await page.locator(draftScroll).evaluate(scroll => scroll === document.activeElement), true);
    }
    assert.equal(await page.locator('#source').inputValue(), source);
  }, width);

  await scenario('Syntax and literal search keep text nodes, selections and malicious code inert', async h => {
    const { page } = h;
    const source = `import Mathlib\n/- outer /- theorem nested -/ exact sorry -/\ndef «quoted sorry» := "exact \\" theorem"\ndef answer := 42\ntheorem reader_fixture : True := by\n  exact True.intro\nexample : True := by sorry\n-- ${markup}\n-- a+b[0].*? \\tail`;
    await fillConfig(page, 'source', source);
    await showSource(page);
    await plainTextNode(page, draftCode, source);
    const lexical = await page.evaluate(() => {
      const registry = (CSS as unknown as { highlights: HighlightRegistry }).highlights;
      return Object.fromEntries(['comment', 'keyword', 'tactic', 'placeholder', 'string', 'number'].map(kind =>
        [kind, Array.from(registry.get(`lean-${kind}`) ?? []).map(range => range.toString())]));
    });
    for (const kind of ['comment', 'keyword', 'tactic', 'placeholder', 'string', 'number']) assert.ok(lexical[kind]!.length > 0, `Lean ${kind} must be highlighted`);
    assert.ok(lexical.comment!.includes('/- outer /- theorem nested -/ exact sorry -/'));
    await openFind(page);
    await search(page, 'True := by', '1/2');
    await search(page, 'a+b[0].*? \\tail', '1/1');
    await search(page, markup, '1/1');
    await noInjection(page);
    await search(page, 'no-such-needle', '0/0');
    assert.equal(await page.locator('#source-find-prev').isDisabled(), true);
    assert.equal(await page.locator('#source-find-next').isDisabled(), true);
    await page.locator(draftScroll).focus();
    const preserved = await page.evaluate(({ codeSelector, scrollSelector }) => {
      const code = document.querySelector(codeSelector)!, node = code.firstChild!, scroll = document.querySelector(scrollSelector)!;
      const range = document.createRange(); range.setStart(node, 0); range.setEnd(node, 6);
      getSelection()!.removeAllRanges(); getSelection()!.addRange(range);
      const before = { code, node, scroll, selection: getSelection()!.toString(), focus: document.activeElement };
      const input = document.querySelector<HTMLInputElement>('#source-find-input')!;
      input.value = 'theorem'; input.dispatchEvent(new Event('input', { bubbles: true }));
      return { code: code === document.querySelector(codeSelector), text: node === code.firstChild,
        scroll: scroll === document.querySelector(scrollSelector), selection: getSelection()!.toString(),
        sameFocus: before.focus === document.activeElement, beforeSelection: before.selection };
    }, { codeSelector: draftCode, scrollSelector: draftScroll });
    assert.deepEqual(preserved, { code: true, text: true, scroll: true, selection: 'import', sameFocus: true, beforeSelection: 'import' });
    await plainTextNode(page, draftCode, source);
    await screenshot(page, 'source-reader-syntax.png');
    await page.locator('#close-source-find').click();
    await page.locator('#task').focus();
    assert.equal(await page.locator('#task').evaluate(task => !task.dispatchEvent(new KeyboardEvent('keydown', { key: 'f', ctrlKey: true, bubbles: true, cancelable: true }))), false,
      'browser find must remain available outside the source reader');
    assert.equal(await page.locator('#source-find-controls').isVisible(), false);
    assert.equal(await page.locator('#task').evaluate(task => task.dispatchEvent(new KeyboardEvent('keydown', { key: 'g', ctrlKey: true, bubbles: true, cancelable: true }))), true,
      'line navigation must not intercept shortcuts outside the source reader');
    await openSettings(page);
    assert.equal(await page.locator('#model').evaluate(model => !model.dispatchEvent(new KeyboardEvent('keydown', { key: 'f', metaKey: true, bubbles: true, cancelable: true }))), false,
      'source find must not intercept shortcuts in a settings dialog');
    assert.equal(await page.locator('#model').evaluate(model => model.dispatchEvent(new KeyboardEvent('keydown', { key: 'g', metaKey: true, bubbles: true, cancelable: true }))), true,
      'line navigation must not intercept shortcuts in a settings dialog');
    await closeSettings(page);
  });

  await scenario('Original and candidate find scopes preserve query, copy bytes, downloads and the separate draft', async h => {
    const { page } = h;
    const draft = await page.locator('#source').inputValue(), task = await page.locator('#task').inputValue();
    await fillConfig(page, 'api-key', credential);
    const source = 'theorem needle : True := by\r\n  sorry\r\n-- needle original\r\n';
    const proof = 'theorem needle : True := by\r\n  trivial\r\n-- needle candidate\r\n-- needle extra\r\n';
    const run = await createRun(h, source, proof);
    await selectSource(h, run.id); await plainTextNode(page, runCode, normalize(proof));
    await openFind(page); await search(page, 'needle', '1/3');
    await page.locator('[data-action="copy-source"]').click();
    assert.equal(await page.evaluate(() => navigator.clipboard.readText()), proof);
    const download = page.waitForEvent('download');
    await page.locator('[data-action="download-proof"]').click();
    const file = await download;
    assert.deepEqual(await fs.readFile((await file.path())!), Buffer.from(proof));
    await page.locator('[data-source-view="input"]').click();
    await plainTextNode(page, runCode, normalize(run.source));
    assert.equal(await page.locator('#source-find-input').inputValue(), 'needle'); await position(page, '1/2');
    await jumpLine(page, 2); await lineVisible(page, 2, runScroll, '  sorry');
    await openFind(page); await position(page, '1/2');
    await page.locator('[data-action="copy-source"]').click();
    assert.ok(run.source.includes('\r\n'), 'the accepted original fixture must retain internal CRLF');
    assert.equal(await page.evaluate(() => navigator.clipboard.readText()), run.source);
    await page.locator('[data-source-view="diff"]').click();
    assert.equal(await page.locator('.source-reader').isVisible(), false, 'diff navigation must not imply searching folded-out text');
    await page.locator('[data-source-view="proof"]').click();
    assert.equal(await page.locator('#source-find-input').inputValue(), 'needle'); await position(page, '1/3');
    const other = await createRun(h, 'theorem second : True := by sorry', 'theorem second : True := by trivial');
    await selectSource(h, other.id);
    assert.equal(await page.locator('#source-find-input').inputValue(), '', 'a different run must start with a fresh source search');
    assert.equal(await page.locator('#source-line-input').inputValue(), '1', 'a different run must start with a fresh line input');
    assert.equal(await page.locator('#source-line-controls').isVisible(), false);
    assert.equal(await page.locator('#source-find-location').innerText(), '');
    await openFind(page); await search(page, 'second', '1/1');
    assert.equal(await page.locator('#source').inputValue(), draft, 'source inspection must preserve the separate composer source');
    assert.equal(await page.locator('#task').inputValue(), task, 'source inspection must preserve the separate composer task');
    assert.equal(await page.locator('#api-key').inputValue(), credential, 'source inspection must leave the separate composer key alone');
    await page.locator('#new-research').click(); await showSource(page);
    assert.equal(await page.locator('#source-find-input').inputValue(), '', 'a new draft must not inherit a run query');
  });

  await scenario('Live candidate and event updates recalculate matches without moving focus or reading position', async h => {
    const { page } = h;
    const run = await createRun(h, longSource);
    const control = controls.get(run.id)!;
    control.artifact(longSource);
    await selectSource(h, run.id); await plainTextNode(page, runCode, longSource);
    await openFind(page); await search(page, 'needle', '1/3');
    await page.locator('#source-find-next').click(); await position(page, '2/3');
    await page.locator('#source-find-input').focus();
    await page.evaluate(({ codeSelector, scrollSelector }) => {
      const code = document.querySelector(codeSelector)!, scroll = document.querySelector(scrollSelector)!;
      const input = document.querySelector<HTMLInputElement>('#source-find-input')!;
      input.setSelectionRange(2, 4);
      (window as unknown as { __readerLiveProbe: unknown }).__readerLiveProbe = { code, scroll, input, top: scroll.scrollTop, left: scroll.scrollLeft };
    }, { codeSelector: runCode, scrollSelector: runScroll });
    const updated = `${longSource}\n-- needle live append`;
    control.artifact(updated);
    await plainTextNode(page, runCode, updated); await position(page, '2/4');
    const live = await page.evaluate(({ codeSelector, scrollSelector }) => {
      const before = (window as unknown as { __readerLiveProbe: { code: Element; scroll: Element; input: HTMLInputElement; top: number; left: number } }).__readerLiveProbe;
      const scroll = document.querySelector(scrollSelector)!;
      return { sameCode: before.code === document.querySelector(codeSelector), sameScroll: before.scroll === scroll,
        sameInput: before.input === document.querySelector('#source-find-input'), sameFocus: before.input === document.activeElement,
        scrollBefore: { top: before.top, left: before.left }, scrollAfter: { top: scroll.scrollTop, left: scroll.scrollLeft },
        selection: [before.input.selectionStart, before.input.selectionEnd] };
    }, { codeSelector: runCode, scrollSelector: runScroll });
    assert.equal(live.sameCode && live.sameScroll && live.sameInput && live.sameFocus, true);
    assert.deepEqual(live.scrollAfter, live.scrollBefore, 'a candidate update must not jump to the first match');
    assert.deepEqual(live.selection, [2, 4]);
    await page.evaluate(selector => { (window as unknown as { __readerText: Node | null }).__readerText = document.querySelector(selector)!.firstChild; }, runCode);
    control.progress('Source reader fixture activity');
    await page.waitForFunction(() => document.querySelector('#conversation')?.textContent?.includes('Source reader fixture activity'));
    assert.equal(await page.locator(runCode).evaluate(code => code.firstChild === (window as unknown as { __readerText: Node }).__readerText), true,
      'unrelated activity must preserve the highlighted source text node');
    assert.equal(await page.locator('#source-find-input').evaluate(input => input === document.activeElement), true);
    await position(page, '2/4');
    await screenshot(page, 'source-reader-live.png');
    await jumpLine(page, 175); await lineVisible(page, 175, runScroll, longLines[174]!);
    await openLine(page); await page.locator('#source-line-input').fill('21');
    const beforeLineUpdate = await page.locator(runScroll).evaluate(scroll => {
      (window as unknown as { __lineInput: Element | null }).__lineInput = document.querySelector('#source-line-input');
      return { top: scroll.scrollTop, left: scroll.scrollLeft };
    });
    control.artifact(`${updated}\n-- needle another live append`);
    await plainTextNode(page, runCode, `${updated}\n-- needle another live append`);
    assert.equal(await page.locator('#source-line-input').inputValue(), '21');
    assert.equal(await page.locator('#source-line-input').getAttribute('max'), '222');
    assert.equal(await page.locator('#source-line-input').evaluate(input => input === document.activeElement
      && input === (window as unknown as { __lineInput: Element }).__lineInput), true);
    assert.deepEqual(await page.locator(runScroll).evaluate(scroll => ({ top: scroll.scrollTop, left: scroll.scrollLeft })), beforeLineUpdate,
      'a live candidate update must not move the line reader');
    await page.keyboard.press('Escape');
  });

  await scenario('Match caps are explicit and navigation wraps within bounded results', async h => {
    const { page } = h;
    await fillConfig(page, 'source', '-- target\n'.repeat(1001));
    await showSource(page); await openFind(page); await search(page, 'target', '1/1000+');
    await page.locator('#source-find-prev').click(); await position(page, '1000/1000+');
    assert.match(await page.locator('#source-find-location').innerText(), /第 1000 行/);
    await matchVisible(page, 'last bounded match', draftCode, draftScroll, 'target');
    await page.locator('#source-find-next').click(); await position(page, '1/1000+');
    await search(page, '', '0/0');
    assert.equal(await page.locator('#source-find-prev').isDisabled(), true);
    assert.equal(await page.locator('#source-find-next').isDisabled(), true);
  });

  await scenario('An oversized draft explains that find is limited to the displayed preview', async h => {
    const { page } = h;
    const lines = Array.from({ length: 250 }, (_, index) => `-- ${'context_'.repeat(20)} ${index + 1}`);
    lines[199] = `-- outsidePreviewNeedle ${'context_'.repeat(20)}`;
    const source = lines.join('\n');
    assert.ok(new TextEncoder().encode(source).byteLength > webLimits.maxSourceBytes);
    await fillConfig(page, 'source', source);
    await showSource(page); await openFind(page);
    await plainTextNode(page, draftCode, lines.slice(0, 160).join('\n'));
    assert.equal(await page.locator('#source-find-scope').isVisible(), true);
    assert.match(await page.locator('#source-find-scope').innerText(), /前 160 行/);
    assert.match(await page.locator('.preview-source-heading>span').innerText(), /前 160 \/ 250 行/);
    await search(page, 'outsidePreviewNeedle', '0/0');
    await openLine(page);
    assert.equal(await page.locator('#source-line-input').getAttribute('max'), '160');
    await page.locator('#source-line-input').fill('200'); await page.keyboard.press('Enter');
    assert.match(await page.locator('#source-line-error').innerText(), /1 至 160/);
    assert.equal(await page.locator('#source-find-scope').isVisible(), true);
    assert.equal(await page.locator('#source').inputValue(), source, 'bounded inspection must retain the complete oversized draft');
    await screenshot(page, 'source-reader-preview-scope.png');
  });

  await scenario('Missing CSS Highlight support keeps plain source and find navigation usable', async h => {
    const { page } = h;
    await fillConfig(page, 'source', longSource);
    await showSource(page); await openFind(page);
    await plainTextNode(page, draftCode, longSource);
    await search(page, 'needle', '1/3');
    await matchVisible(page, 'fallback horizontal match', draftCode, draftScroll, 'needle', true);
    await page.locator('#source-find-next').click(); await position(page, '2/3');
    await matchVisible(page, 'fallback match beyond preview', draftCode, draftScroll, 'Needle', true);
    await screenshot(page, 'source-reader-fallback.png');
    await page.locator('#close-source-find').click();
    assert.equal(await page.locator(draftScroll).evaluate(scroll => scroll === document.activeElement), true);
    await jumpLine(page, 205); await lineVisible(page, 205, draftScroll, longLines[204]!, true);
    assert.equal(await page.locator('#source').inputValue(), longSource);
  }, 375, true);

  await writeReport('passed');
  console.log(`Source reader checks passed: ${checks.length} scenarios; syntax, literal find, line navigation, stable text and live updates, original-byte exports, mobile layouts and plain-text fallback.`);
  console.log(`Report: ${path.relative(root, reportFile)}`);
} catch (error) {
  await writeReport('failed', error); throw error;
} finally {
  await browser?.close(); await service.close();
}
