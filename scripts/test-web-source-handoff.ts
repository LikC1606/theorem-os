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
import type { WebRun, WebRunInput } from '../apps/web/shared';
import { draftRecoveryStorageKey } from '../apps/web/client/draftRecovery';
import { closeDialog, closeSettings, openSettings, selectHistoryRun } from './web-ui-controls';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const output = path.join(root, 'out/web-source-handoff'), reportFile = path.join(output, 'report.json');
const widths = [1440, 375, 320];
const credential = `sk-theoremos-handoff-fixture-${crypto.randomUUID()}`;
await fs.access(path.join(root, 'out/web/app.js')).catch(() => { throw new Error('Run bun run build:web before the source handoff check.'); });
await fs.mkdir(output, { recursive: true }); await fs.rm(reportFile, { force: true });
const probe = net.createServer();
await new Promise<void>(resolve => probe.listen(0, '127.0.0.1', resolve));
const port = (probe.address() as net.AddressInfo).port;
await new Promise<void>((resolve, reject) => probe.close(error => error ? reject(error) : resolve()));
const origin = `http://127.0.0.1:${port}`;
let workerStarts = 0, cleanedOwners = 0;
const runner: WebRunner = {
  async readiness() { return { ready: true, message: 'Local source handoff fixture' }; },
  async run(input, send) {
    workerStarts++;
    send({ type: 'result', result: { status: 'incomplete', proof: `-- candidateNeedle for ${input.id}\n${input.input.source}`,
      report: { fixture: true } } });
  },
};
const service = createWebService(readWebConfig({ THEOREMOS_WEB_PORT: String(port), THEOREMOS_WEB_PUBLIC_URL: origin,
  THEOREMOS_WEB_STATIC_ROOT: path.join(root, 'out/web') }), runner);
type RequestRecord = { method: string; pathname: string };
type Harness = { page: Page; context: BrowserContext; requests: RequestRecord[]; creates: number; owner: string; releases: Array<() => Promise<void>> };
const checks: Array<{ name: string; width: number; elapsedMs: number; fixtureCreates: number; unexpectedWrites: number; requests: RequestRecord[] }> = [];
const screenshots: string[] = [];
const visibility: Array<{ label: string; width: number; geometry: unknown }> = [];
const handoffs: Array<{ label: string; width: number; start: number; end: number; sourceBytes: number }> = [];
const focusChecks: Array<{ label: string; target: string; visible: boolean }> = [];
let browser: Awaited<ReturnType<typeof chromium.launch>> | undefined;
let activeHarness: Harness | undefined;
let failedScenario = '', failureScreenshot = '';
const lineOffset = (source: string, line: number) => source.split('\n').slice(0, line - 1).reduce((offset, value) => offset + value.length + 1, 0);
const previewEdit = '[data-draft-action="edit"]';

async function settled(page: Page) {
  await page.evaluate(() => new Promise<void>(resolve => requestAnimationFrame(() => requestAnimationFrame(() => resolve()))));
}
async function scenario(name: string, run: (h: Harness) => Promise<void>, width = 1440) {
  failedScenario = name;
  const started = performance.now();
  const context = await browser!.newContext({ viewport: { width, height: width > 850 ? 900 : 812 }, reducedMotion: 'reduce' });
  const page = await context.newPage(); page.setDefaultTimeout(10_000);
  const h: Harness = { page, context, requests: [], creates: 0, owner: '', releases: [] }; activeHarness = h;
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
    h.owner = (await context.cookies(origin)).find(cookie => cookie.name === 'theoremos_session')?.value ?? '';
    assert.ok(h.owner, 'a handoff fixture requires a real local session');
    await Promise.race([run(h), new Promise<never>((_, reject) => {
      deadline = setTimeout(() => reject(new Error(`Source handoff scenario exceeded 50 seconds: ${name}`)), 50_000);
    })]);
    assert.deepEqual(errors, [], 'uncaught browser errors'); assert.deepEqual(external, [], 'source handoff must remain local');
    const writes = h.requests.filter(request => request.method !== 'GET');
    assert.equal(writes.length, h.creates, 'handoff must not create, cancel, change or delete a run');
    assert.equal(writes.every(request => request.method === 'POST' && request.pathname === '/api/runs'), true,
      'the only allowed API write is explicit creation of a read-only local run fixture');
    const stored = await page.evaluate(() => ({ text: document.body.innerText, session: JSON.stringify(sessionStorage), local: JSON.stringify(localStorage) }));
    assert.equal(JSON.stringify(stored).includes(credential), false, 'fixture credentials must not be shown or stored');
    checks.push({ name, width, elapsedMs: Math.round(performance.now() - started), fixtureCreates: h.creates,
      unexpectedWrites: writes.length - h.creates, requests: h.requests });
    console.log(`PASS ${name}`);
  } catch (error) {
    failureScreenshot = `failure-${checks.length + 1}.png`;
    await page.screenshot({ path: path.join(output, failureScreenshot) }).catch(() => {}); throw error;
  } finally {
    clearTimeout(deadline);
    try {
      for (const release of h.releases) await release().catch(() => {});
      if (h.owner) { service.jobs.forget(h.owner); assert.equal(service.jobs.list(h.owner).length, 0); cleanedOwners++; }
    } finally { await context.close(); }
  }
}
async function showDraft(page: Page) {
  if (page.viewportSize()!.width <= 850) await page.locator('#mobile-runs').click();
  await page.locator('#draft-preview').waitFor(); await settled(page);
}
async function prepare(page: Page, source: string) {
  await openSettings(page); await page.locator('#environment').selectOption('standard');
  await page.locator('#template').selectOption(''); await page.locator('#source').fill(source);
  await closeSettings(page); await showDraft(page);
}
async function setSource(page: Page, source: string) {
  await openSettings(page); await page.locator('#source').fill(source); await closeSettings(page); await showDraft(page);
}
async function text(page: Page, selector: string, expected: string) {
  await page.waitForFunction(({ selector, expected }) => document.querySelector(selector)?.textContent === expected, { selector, expected });
}
async function find(page: Page, query: string, count: string) {
  if (!await page.locator('#source-find-controls').isVisible()) await page.locator('#open-source-find').click();
  await page.locator('#source-find-input').fill(query); await text(page, '#source-find-position', count); await settled(page);
}
async function closeFind(page: Page, escape = false) {
  if (!await page.locator('#source-find-controls').isVisible()) return;
  if (escape) { await page.locator('#source-find-input').focus(); await page.keyboard.press('Escape'); }
  else await page.locator('#close-source-find').click();
  assert.equal(await page.locator('#source-find-controls').isVisible(), false); await settled(page);
}
async function openLine(page: Page) {
  if (!await page.locator('#source-line-controls').isVisible()) await page.locator('#open-source-line').click();
  await page.locator('#source-line-controls').waitFor();
}
async function jump(page: Page, line: number) {
  await openLine(page); await page.locator('#source-line-input').fill(String(line)); await page.keyboard.press('Enter');
  assert.equal(await page.locator('#source-line-controls').isVisible(), false); await settled(page);
}
async function locationAvailable(page: Page, available = true) {
  await settled(page); assert.equal(await page.locator('#edit-source-location').isVisible(), available);
  if (available) assert.equal((await page.locator('#edit-source-location').innerText()).trim(), '编辑此处');
}
async function editor(page: Page, source: string, start: number, end = start, label = 'source handoff') {
  await page.locator('#source-editor[open]').waitFor(); await settled(page);
  const actual = await page.locator('#expanded-source').evaluate(node => {
    const editor = node as HTMLTextAreaElement;
    return { source: editor.value, start: editor.selectionStart, end: editor.selectionEnd, focused: document.activeElement === editor };
  });
  assert.equal(actual.source, source, `${label}: the editor must retain the exact draft buffer`);
  assert.equal(actual.start, start, `${label}: expected UTF-16 start offset`); assert.equal(actual.end, end, `${label}: expected UTF-16 end offset`);
  assert.equal(actual.focused, true, `${label}: the native textarea must retain focus so its selection is visible`);
  assert.equal(await page.locator('#editor-navigation').isVisible(), false, `${label}: preview handoff must not open editor find controls`);
  assert.equal(await page.locator('#editor-change-status').textContent(), '未修改');
  handoffs.push({ label, width: page.viewportSize()!.width, start, end, sourceBytes: Buffer.byteLength(source) });
}
async function enter(page: Page, source: string, start: number, end = start, via = '#edit-source-location', label = 'source handoff') {
  await page.locator(via).evaluate(node => { (window as unknown as { __handoffOpener: Element }).__handoffOpener = node; });
  await page.locator(via).click(); await editor(page, source, start, end, label);
}
async function closeEditor(page: Page) {
  await closeDialog(page, '#source-editor', () => page.locator('#close-editor').click()); await settled(page);
  assert.equal(await page.locator('#editor-discard-dialog').isVisible(), false, 'navigation alone must never dirty the buffer');
  const restored = await page.evaluate(() => {
    const opener = (window as unknown as { __handoffOpener: HTMLElement }).__handoffOpener;
    return { visible: opener.getClientRects().length > 0, focused: document.activeElement === opener,
      active: (document.activeElement as HTMLElement | null)?.id || (document.activeElement as HTMLElement | null)?.dataset.draftAction || '' };
  });
  if (restored.visible) assert.equal(restored.focused, true,
    `closing without changes must return focus to the same visible editor trigger: ${JSON.stringify(restored)}`);
  else await visibleFocus(page, 'the original trigger became hidden before closing');
}
async function visibleFocus(page: Page, label: string) {
  await settled(page);
  const evidence = await page.evaluate(() => {
    const target = document.activeElement as HTMLElement | null;
    return { target: target?.id || target?.dataset.draftAction || target?.tagName || '',
      visible: Boolean(target && target !== document.body && target.getClientRects().length && !target.closest('dialog:not([open])')) };
  });
  assert.equal(evidence.visible, true, `${label}: closing must leave keyboard focus on a visible control outside the closed editor`);
  focusChecks.push({ label, ...evidence });
}
async function recovery(page: Page) { return page.evaluate(key => sessionStorage.getItem(key), draftRecoveryStorageKey); }
async function unchangedDraft(page: Page, source: string, backup: string | null) {
  assert.equal(await page.locator('#source').inputValue(), source);
  assert.equal(await recovery(page), backup, 'handoff and unapplied edits must not replace the existing recovery backup');
}
async function fit(page: Page, selector: string) {
  const box = await page.locator(selector).boundingBox(), viewport = page.viewportSize()!;
  assert.ok(box && box.x >= -1 && box.y >= -1 && box.x + box.width <= viewport.width + 1 && box.y + box.height <= viewport.height + 1,
    `${selector} must fit ${viewport.width}px: ${JSON.stringify(box)}`);
  assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth + 1), true, 'source handoff must not widen the page');
}
async function screenshot(page: Page, name: string) {
  await page.screenshot({ path: path.join(output, name) }); screenshots.push(name);
}
async function visibleSelection(page: Page, label: string) {
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
      if (!rect.height && editor.selectionStart === editor.selectionEnd) {
        content.data = editor.value.slice(0, editor.selectionStart) + '\u200b' + editor.value.slice(editor.selectionStart) + '\u200b';
        range.setStart(content, editor.selectionStart); range.setEnd(content, editor.selectionStart + 1);
        rect = range.getClientRects()[0] ?? range.getBoundingClientRect();
      }
      const origin = mirror.getBoundingClientRect(), bounds = editor.getBoundingClientRect();
      return { selected: editor.value.slice(editor.selectionStart, editor.selectionEnd), start: editor.selectionStart, end: editor.selectionEnd,
        focused: editor === document.activeElement, scrollTop: editor.scrollTop, scrollLeft: editor.scrollLeft, height: rect.height,
        top: rect.top - origin.top - editor.scrollTop, bottom: rect.bottom - origin.top - editor.scrollTop,
        left: rect.left - origin.left - editor.scrollLeft, right: rect.right - origin.left - editor.scrollLeft,
        visibleTop: Math.max(0, -bounds.top - editor.clientTop), visibleBottom: Math.min(editor.clientHeight, innerHeight - bounds.top - editor.clientTop),
        visibleLeft: Math.max(0, -bounds.left - editor.clientLeft), visibleRight: Math.min(editor.clientWidth, innerWidth - bounds.left - editor.clientLeft) };
    } finally { mirror.remove(); }
  });
  visibility.push({ label, width: page.viewportSize()!.width, geometry });
  assert.equal(geometry.focused, true);
  assert.ok(geometry.height > 0, `${label}: an independently measured native Range must occupy a rendered line`);
  assert.ok(geometry.top >= geometry.visibleTop - 2 && geometry.bottom <= geometry.visibleBottom + 2,
    `${label}: the inherited position must be vertically visible after textarea wrapping: ${JSON.stringify(geometry)}`);
  assert.ok(geometry.left >= geometry.visibleLeft - 2 && geometry.right <= geometry.visibleRight + 2,
    `${label}: the inherited position must be horizontally visible: ${JSON.stringify(geometry)}`);
}
async function createRun(h: Harness, title: string) {
  const input: WebRunInput = { providerId: 'openai', apiKey: credential, model: 'fixture-handoff-model', effort: 'low', environment: 'standard',
    source: `-- runOriginalNeedle ${title}\ntheorem readonly_handoff : True := by sorry`, task: title,
    maxTurns: 2, maxRunSeconds: 60, workers: 1, coordination: 'independent' };
  const run = await h.page.evaluate(async input => {
    const session = await (await fetch('/api/session')).json();
    const response = await fetch('/api/runs', { method: 'POST', headers: { 'Content-Type': 'application/json', 'X-CSRF-Token': session.csrfToken },
      body: JSON.stringify(input) });
    if (response.status !== 201) throw new Error(`Read-only handoff fixture creation failed: ${response.status}`);
    return (await response.json()).run as WebRun;
  }, input);
  h.creates++;
  await h.page.waitForFunction(async id => {
    const run = (await (await fetch(`/api/runs/${id}`)).json()).run as WebRun;
    return run.status === 'completed';
  }, run.id);
  return run;
}
async function poll(h: Harness) {
  await h.page.locator('#refresh-runs:enabled').waitFor({ state: 'attached' });
  const loaded = h.page.waitForResponse(response => response.request().method() === 'GET'
    && new URL(response.url()).pathname === '/api/runs' && response.status() === 200);
  await h.page.evaluate(() => document.dispatchEvent(new Event('visibilitychange'))); await loaded;
  await h.page.locator('#refresh-runs:enabled').waitFor({ state: 'attached' }); await settled(h.page);
}
async function delayedLean(h: Harness, source: string) {
  await h.page.evaluate(() => {
    const original = File.prototype.arrayBuffer;
    File.prototype.arrayBuffer = async function() {
      const value = await original.call(this);
      if (this.name === 'late-handoff.lean') await new Promise<void>(resolve => {
        (window as unknown as { __releaseHandoffFile: () => void }).__releaseHandoffFile = resolve;
      });
      return value;
    };
  });
  const release = () => h.page.evaluate(() => (window as unknown as { __releaseHandoffFile?: () => void }).__releaseHandoffFile?.());
  h.releases.push(release);
  await h.page.locator('#source-file').setInputFiles({ name: 'late-handoff.lean', mimeType: 'text/plain', buffer: Buffer.from(source) });
  await h.page.waitForFunction(() => typeof (window as unknown as { __releaseHandoffFile?: unknown }).__releaseHandoffFile === 'function');
  return release;
}
async function writeReport(status: 'passed' | 'failed', error?: unknown) {
  const report = { status, checkedAt: new Date().toISOString(),
    mode: 'Real local HTTP service and Chromium. Native textarea selection and independent DOM Range mirrors verify preview-to-editor handoff. Only explicit read-only fixture setup may POST; no Docker, Lean, models or external requests.',
    paidModelCalls: false, workerStarts, cleanedOwners, widths, checks, handoffs, visibility, focusChecks, screenshots,
    unexpectedWrites: checks.reduce((sum, check) => sum + check.unexpectedWrites, 0),
    ...(error ? { failedScenario, error: error instanceof Error ? error.message : String(error), failureScreenshot, failureRequests: activeHarness?.requests } : {}) };
  assert.equal(JSON.stringify(report).includes(credential), false);
  await fs.writeFile(reportFile, JSON.stringify(report, null, 2) + '\n');
}

const longLines = Array.from({ length: 222 }, (_, index) => `-- context ${index + 1}`);
longLines[0] = `-- ${'lead '.repeat(500)}`;
longLines[7] = '';
longLines[174] = `-- ${'prefix '.repeat(60)}🙂x needleAfter160`;
longLines[221] = '';
const longSource = longLines.join('\n'), needle = 'needleAfter160';

try {
  await new Promise<void>((resolve, reject) => { service.server.once('error', reject); service.server.listen(port, '127.0.0.1', resolve); });
  browser = await chromium.launch({ headless: true });

  for (const width of widths) await scenario(`A Unicode match beyond 160 lines opens at its wrapped editing position at ${width}px`, async ({ page }) => {
    await prepare(page, longSource); await locationAvailable(page, false);
    assert.match(await page.locator('.preview-source-heading>span').innerText(), /前 160/);
    const backup = await recovery(page);
    await find(page, needle, '1/1'); await locationAvailable(page);
    assert.equal(await page.locator('#draft-preview-code code').textContent(), longSource);
    const start = longSource.indexOf(needle), end = start + needle.length;
    for (const selector of ['#edit-source-location', '#open-source-line', '#open-source-find']) await fit(page, selector);
    await screenshot(page, `handoff-${width}-preview.png`);
    await enter(page, longSource, start, end); await visibleSelection(page, 'long Unicode search handoff');
    await unchangedDraft(page, longSource, backup);
    await screenshot(page, `handoff-${width}-native-selection.png`);
    await closeEditor(page); await locationAvailable(page);
    await closeFind(page, width === 1440); await locationAvailable(page);
    await enter(page, longSource, start, end, previewEdit, 'closed-search existing preview edit');
    await visibleSelection(page, 'match retained after closing reader find'); await closeEditor(page);
    await enter(page, longSource, start, end, '#edit-source-location', 'same-buffer editor reopen');
    await page.keyboard.press('Control+z'); assert.equal(await page.locator('#expanded-source').inputValue(), longSource);
    await closeEditor(page); await unchangedDraft(page, longSource, backup);
  }, width);

  await scenario('Confirmed logical lines hand off the first, blank, last and post-preview line starts', async ({ page }) => {
    await prepare(page, longSource);
    for (const line of [175, 8, 222, 1]) {
      await jump(page, line); await locationAvailable(page);
      await enter(page, longSource, lineOffset(longSource, line), undefined, '#edit-source-location', `confirmed line ${line}`);
      await visibleSelection(page, `confirmed logical line ${line}`); await closeEditor(page);
    }
    await screenshot(page, 'handoff-line-first.png');
  });

  await scenario('Typing or rejecting a new line number cannot replace the last successful location', async ({ page }) => {
    await prepare(page, longSource); await jump(page, 175);
    await openLine(page); await page.locator('#source-line-input').fill('20');
    await enter(page, longSource, lineOffset(longSource, 175), undefined, '#edit-source-location', 'unconfirmed line input'); await closeEditor(page);
    await page.locator('#source-line-input').fill('999'); await page.keyboard.press('Enter');
    await page.locator('#source-line-error').waitFor();
    await enter(page, longSource, lineOffset(longSource, 175), undefined, previewEdit, 'invalid line retains last success'); await closeEditor(page);
    await page.locator('#source-line-input').fill('20'); await page.locator('#source-line-go').click();
    await enter(page, longSource, lineOffset(longSource, 20)); await closeEditor(page);
  });

  await scenario('No matches and an emptied query clear old match locations while closing find preserves a successful one', async ({ page }) => {
    const source = '-- before\n-- needleTarget\n-- after'; await prepare(page, source);
    const start = source.indexOf('needleTarget'); await find(page, 'needleTarget', '1/1'); await closeFind(page);
    await locationAvailable(page); await enter(page, source, start, start + 12, previewEdit); await closeEditor(page);
    await find(page, 'absentTheorem', '0/0'); await locationAvailable(page, false);
    await enter(page, source, 0, 0, previewEdit, 'no matches do not reuse an old match'); await closeEditor(page);
    await find(page, 'needleTarget', '1/1'); await locationAvailable(page);
    await find(page, '', '0/0'); await locationAvailable(page, false);
    await enter(page, source, 0, 0, previewEdit, 'empty query clears match handoff'); await closeEditor(page);
  });

  await scenario('Reopening a cached query hands off the currently highlighted match after closing on the third result', async ({ page }) => {
    const query = 'cachedNeedle', source = `-- ${query} first\n-- between\n-- 🙂 ${query} second\n-- another\n-- ${query} third`;
    await prepare(page, source); await find(page, query, '1/3');
    await page.locator('#source-find-next').click(); await page.locator('#source-find-next').click();
    await text(page, '#source-find-position', '3/3'); await closeFind(page, true);
    const third = source.lastIndexOf(query);
    await enter(page, source, third, third + query.length, previewEdit, 'closed third match'); await closeEditor(page);
    await page.locator('#open-source-find').click(); await text(page, '#source-find-position', '1/3'); await settled(page);
    const current = await page.evaluate(() => {
      const highlights = (CSS as unknown as { highlights: Map<string, Iterable<Range>> }).highlights;
      return [...(highlights.get('source-current') ?? [])].map(range => ({ start: range.startOffset, end: range.endOffset, text: range.toString() }));
    });
    const first = source.indexOf(query);
    assert.deepEqual(current, [{ start: first, end: first + query.length, text: query }],
      'cached-query count and current rendered highlight must identify the same match');
    await locationAvailable(page);
    await screenshot(page, 'handoff-cached-current-match.png');
    await enter(page, source, first, first + query.length, '#edit-source-location', 'reopened query matches visible highlight');
    await visibleSelection(page, 'reopened cached query'); await closeEditor(page);
  });

  await scenario('Model, budget and task edits retain a successful location when the exact source stays unchanged', async ({ page }) => {
    await prepare(page, longSource); await find(page, needle, '1/1'); await closeFind(page);
    await openSettings(page); await page.locator('#model').fill('fixture-metadata-handoff');
    await page.locator('#max-seconds').fill('120'); await page.locator('#max-turns').fill('3'); await closeSettings(page);
    if (page.viewportSize()!.width <= 850) await page.locator('#mobile-compose').click();
    await page.locator('#task').fill('Revise the task description while preserving the Lean source.'); await showDraft(page);
    await locationAvailable(page); const start = longSource.indexOf(needle);
    await enter(page, longSource, start, start + needle.length); await visibleSelection(page, 'handoff after metadata edits'); await closeEditor(page);
  }, 375);

  await scenario('A same-length source replacement invalidates the snapshot and changing back cannot revive it', async ({ page }) => {
    const source = '-- contextA\n-- needleTarget\n-- unchanged'; const changed = source.replace('contextA', 'contextB');
    assert.equal(source.length, changed.length);
    await prepare(page, source); await find(page, 'needleTarget', '1/1'); await closeFind(page);
    await setSource(page, changed); await locationAvailable(page, false);
    await enter(page, changed, 0, 0, previewEdit, 'same-length changed source'); await closeEditor(page);
    await setSource(page, source); await locationAvailable(page, false);
    await enter(page, source, 0, 0, previewEdit, 'changing source back does not revive a stale snapshot'); await closeEditor(page);
  });

  await scenario('Switching a template and restoring its backup both invalidate previous source locations', async ({ page }) => {
    await prepare(page, longSource); await find(page, needle, '1/1'); await closeFind(page);
    await openSettings(page); await page.locator('#template').selectOption('logic');
    const template = await page.locator('#source').inputValue(); assert.notEqual(template, longSource);
    await closeSettings(page); await showDraft(page); await locationAvailable(page, false);
    await enter(page, template, 0, 0, previewEdit, 'template replacement'); await closeEditor(page);
    await openSettings(page); await page.locator('#restore-draft-settings').click();
    assert.equal(await page.locator('#source').inputValue(), longSource); await closeSettings(page); await showDraft(page);
    await locationAvailable(page, false); await enter(page, longSource, 0, 0, previewEdit, 'restored source has no stale location'); await closeEditor(page);
  });

  await scenario('A delayed Lean import invalidates an older preview location after the file actually arrives', async h => {
    const { page } = h; await prepare(page, longSource); await find(page, needle, '1/1'); await closeFind(page);
    const imported = longSource.replace('context 222', 'context NEW') + '\n-- late file import';
    const release = await delayedLean(h, imported);
    await release();
    await page.waitForFunction(source => (document.querySelector('#source') as HTMLTextAreaElement).value === source, imported);
    await settled(page); await locationAvailable(page, false);
    await enter(page, imported, 0, 0, previewEdit, 'delayed import invalidates handoff'); await closeEditor(page);
  });

  await scenario('Oversized drafts hand off only displayed prefix locations and verify the full source snapshot', async ({ page }) => {
    const lines = Array.from({ length: 220 }, (_, index) => `-- ${String(index + 1).padStart(3, '0')} ${'context '.repeat(27)}`);
    lines[49] = '-- 🙂 prefixNeedle'; lines[174] = '-- outsidePreviewNeedle';
    const source = lines.join('\n'); assert.ok(Buffer.byteLength(source) > webLimits.maxSourceBytes);
    await prepare(page, source); await find(page, 'prefixNeedle', '1/1'); await locationAvailable(page);
    assert.match(await page.locator('#source-find-scope').innerText(), /160/);
    const start = source.indexOf('prefixNeedle'); await enter(page, source, start, start + 12);
    await visibleSelection(page, 'oversized draft displayed-prefix handoff'); await closeEditor(page); await closeFind(page);
    const changed = source.slice(0, -1) + (source.endsWith('x') ? 'y' : 'x');
    assert.equal(source.length, changed.length); assert.equal(source.split('\n').slice(0, 160).join('\n'), changed.split('\n').slice(0, 160).join('\n'));
    await setSource(page, changed); await locationAvailable(page, false);
    await enter(page, changed, 0, 0, previewEdit, 'changed invisible tail invalidates the full-source snapshot'); await closeEditor(page);
    await find(page, 'outsidePreviewNeedle', '0/0'); await locationAvailable(page, false);
    await openLine(page); await page.locator('#source-line-input').fill('175'); await page.keyboard.press('Enter');
    await page.locator('#source-line-error').waitFor(); await locationAvailable(page, false);
    assert.equal(await page.locator('#source-line-input').getAttribute('max'), '160');
    await screenshot(page, 'handoff-oversized-prefix-scope.png');
  });

  await scenario('Read-only runs and candidate searches cannot pass positions or source text into the independent draft editor', async h => {
    const { page } = h; const source = '-- draft before\n-- draftNeedle\n-- draft after';
    await prepare(page, source); await find(page, 'draftNeedle', '1/1'); await closeFind(page);
    const a = await createRun(h, 'Read-only run A'), b = await createRun(h, 'Read-only run B'); await poll(h);
    for (const run of [a, b]) {
      await selectHistoryRun(page, run.id); await find(page, 'candidateNeedle', '1/1'); await locationAvailable(page, false);
      await page.locator('[data-source-view="input"]').click(); await find(page, 'runOriginalNeedle', '1/1'); await locationAvailable(page, false);
      if (page.viewportSize()!.width <= 850) await page.locator('#mobile-compose').click();
      await enter(page, source, 0, 0, '#edit-draft-source', 'run view opens a separate draft editor'); await closeEditor(page);
      assert.equal(service.jobs.get(h.owner, run.id)?.source, run.source, 'submitted source must remain frozen');
    }
    await page.locator('#return-to-draft').click(); await showDraft(page); await locationAvailable(page, false);
    await enter(page, source, 0, 0, previewEdit, 'returning from run scopes cannot reuse a run match'); await closeEditor(page);
  }, 375);

  await scenario('Handoff preserves native undo, dirty-close confirmation and one recoverable applied draft update', async ({ page }) => {
    const source = '-- 🙂 needleTarget\ntheorem handoff_undo : True := by sorry';
    const start = source.indexOf('needleTarget'); await prepare(page, source); await find(page, 'needleTarget', '1/1');
    const backup = await recovery(page); await enter(page, source, start, start + 12);
    await page.keyboard.insertText('editedTarget'); const edited = source.replace('needleTarget', 'editedTarget');
    assert.equal(await page.locator('#expanded-source').inputValue(), edited);
    await page.keyboard.press('Control+z'); assert.equal(await page.locator('#expanded-source').inputValue(), source);
    await page.keyboard.press('Control+Shift+z'); assert.equal(await page.locator('#expanded-source').inputValue(), edited);
    await unchangedDraft(page, source, backup);
    await page.locator('#close-editor').click(); await page.locator('#editor-discard-dialog[open]').waitFor();
    await closeDialog(page, '#editor-discard-dialog', () => page.locator('#keep-editing').click());
    assert.equal(await page.locator('#expanded-source').inputValue(), edited);
    assert.equal(await page.locator('#expanded-source').evaluate(node => node === document.activeElement), true);
    await closeDialog(page, '#source-editor', () => page.locator('#apply-editor').click());
    await visibleFocus(page, 'applied source hides the original handoff trigger');
    assert.equal(await page.locator('#source').inputValue(), edited);
    const saved = JSON.parse((await recovery(page))!); assert.equal(saved.reason, 'edit'); assert.equal(saved.task.draft.source, source);
    await showDraft(page); await locationAvailable(page, false);
    await enter(page, edited, 0, 0, previewEdit, 'applying creates a new source snapshot');
    await page.keyboard.press('Control+z'); assert.equal(await page.locator('#expanded-source').inputValue(), edited,
      'a fresh editor cannot expose an undo transaction from the previous scratch buffer'); await closeEditor(page);
  });

  await scenario('An old editor close cannot take focus from a new control, another modal or a reopened editor', async ({ page }) => {
    let source = '-- before\n-- focusNeedle\n-- after'; const query = 'focusNeedle'; await prepare(page, source);
    for (const [index, next] of ['control', 'modal', 'editor'].entries()) {
      await find(page, query, '1/1');
      const start = source.indexOf(query); await enter(page, source, start, start + query.length);
      const replacement = `${query}${index}`; await page.keyboard.insertText(replacement);
      source = source.slice(0, start) + replacement + source.slice(start + query.length);
      if (next === 'editor') {
        await page.evaluate(() => {
          const dialog = document.querySelector<HTMLDialogElement>('#source-editor')!;
          dialog.dataset.handoffClosed = 'false';
          dialog.addEventListener('close', () => { dialog.dataset.handoffClosed = 'true'; }, { once: true });
          document.querySelector<HTMLButtonElement>('#apply-editor')!.click();
          const opener = document.querySelector<HTMLButtonElement>('#draft-preview [data-draft-action="edit"]')!;
          (window as unknown as { __handoffOpener: Element }).__handoffOpener = opener;
          opener.focus(); opener.click();
        });
        await page.waitForFunction(() => document.querySelector<HTMLDialogElement>('#source-editor')?.dataset.handoffClosed === 'true');
        await editor(page, source, 0, 0, 'reopening before the previous asynchronous close event');
        await visibleFocus(page, 'an earlier close does not affect a reopened editor');
        await closeEditor(page);
      } else {
        await closeDialog(page, '#source-editor', () => page.evaluate(next => {
          document.querySelector<HTMLButtonElement>('#apply-editor')!.click();
          if (next === 'modal') {
            document.querySelector<HTMLButtonElement>('#open-settings')!.click();
            document.querySelector<HTMLInputElement>('#model')!.focus();
          } else document.querySelector<HTMLTextAreaElement>('#task')!.focus();
        }, next));
        await visibleFocus(page, `an earlier close does not take ${next} focus`);
        assert.equal(await page.evaluate(() => document.activeElement?.id), next === 'modal' ? 'model' : 'task');
        if (next === 'modal') await closeSettings(page);
      }
      assert.equal(await page.locator('#source').inputValue(), source); await showDraft(page);
    }
  });

  await writeReport('passed');
  console.log(`Source handoff checks passed: ${checks.length} scenarios; wrapped and Unicode positions, line confirmation, full-source invalidation, independent run scopes and native editing safety.`);
  console.log(`Report: ${path.relative(root, reportFile)}`);
} catch (error) { await writeReport('failed', error); throw error; }
finally { try { await browser?.close(); } finally { await service.close(); } }
