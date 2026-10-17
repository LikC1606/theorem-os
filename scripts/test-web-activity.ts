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
import type { WebEvent, WebRun, WebRunInput } from '../apps/web/shared';
import { closeHistory, openHistory, selectHistoryRun } from './web-ui-controls';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const output = path.join(root, 'out/web-activity');
const reportFile = path.join(output, 'report.json');
const credential = `sk-theoremos-activity-fixture-${crypto.randomUUID()}`;
const markup = '<img data-activity-injection src=x onerror="window.__activityInjected=true">';
const rowSelector = '.activity-table tbody tr[data-sequence]';
const widths = [1440, 375, 320];
await fs.access(path.join(root, 'out/web/app.js')).catch(() => { throw new Error('Run bun run build:web before the activity check.'); });
await fs.mkdir(output, { recursive: true });
await fs.rm(reportFile, { force: true });
const probe = net.createServer();
await new Promise<void>(resolve => probe.listen(0, '127.0.0.1', resolve));
const port = (probe.address() as net.AddressInfo).port;
await new Promise<void>((resolve, reject) => probe.close(error => error ? reject(error) : resolve()));
const origin = `http://127.0.0.1:${port}`;
type Control = { progress(type: string, message: string): void; finish(): void };
const controls = new Map<string, Control>();
let workerStarts = 0;
const runner: WebRunner = {
  async readiness() { return { ready: true, message: 'Local activity fixture' }; },
  async run(input, send, signal) {
    workerStarts++;
    await new Promise<void>((resolve, reject) => {
      const cleanup = () => { controls.delete(input.id); signal.removeEventListener('abort', abort); };
      const abort = () => { cleanup(); reject(new Error('Cancelled activity fixture')); };
      signal.addEventListener('abort', abort, { once: true });
      controls.set(input.id, { progress: (event, message) => send({ type: 'progress', event, message }), finish: () => { cleanup(); resolve(); } });
      if (signal.aborted) abort();
    });
  },
};
const service = createWebService(readWebConfig({ THEOREMOS_WEB_PORT: String(port), THEOREMOS_WEB_PUBLIC_URL: origin,
  THEOREMOS_WEB_STATIC_ROOT: path.join(root, 'out/web'), THEOREMOS_WEB_CONCURRENCY: '8' }), runner);
type RequestRecord = { method: string; pathname: string };
type Harness = { page: Page; context: BrowserContext; requests: RequestRecord[]; runIds: string[] };
type Anchor = { sequence: number; offset: number; scrollTop: number; scrollLeft: number };
type ActivityExport = { format: string; version: number; runId: string; exportedAt: string; order: string;
  filters: { query: string; type: string | null }; retention: { limit: number; retainedCount: number;
    firstSequence: number | null; lastSequence: number | null; earlierEventsOmitted: boolean };
  matchedCount: number; events: WebEvent[] };
const checks: Array<{ name: string; elapsedMs: number; fixtureCreates: number; featureApiWrites: number; requests: RequestRecord[] }> = [];
const screenshots: string[] = [];
const anchors: Array<{ label: string; width: number; before: Anchor; after: Anchor }> = [];
const exports: Array<{ runId: string; matchedCount: number; retainedCount: number; earlierEventsOmitted: boolean }> = [];
let browser: Awaited<ReturnType<typeof chromium.launch>> | undefined;
let failedScenario = '', failureScreenshot = '';

async function scenario(name: string, run: (h: Harness) => Promise<void>, width = 1440) {
  failedScenario = name;
  const started = performance.now();
  const context = await browser!.newContext({ viewport: { width, height: width > 850 ? 900 : 812 }, reducedMotion: 'reduce' });
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
    const draft = await page.locator('#source').inputValue(), task = await page.locator('#task').inputValue();
    await Promise.race([run(h), new Promise<never>((_, reject) => {
      deadline = setTimeout(() => reject(new Error(`Activity scenario exceeded 50 seconds: ${name}`)), 50_000);
    })]);
    assert.deepEqual(errors, [], 'uncaught browser errors');
    assert.deepEqual(external, [], 'activity inspection must not contact external sites or model providers');
    assert.equal(await page.locator('#source').inputValue(), draft, 'activity inspection must preserve the composer source');
    assert.equal(await page.locator('#task').inputValue(), task, 'activity inspection must preserve the composer task');
    assert.equal(await page.locator('#api-key').inputValue(), '', 'activity inspection must not populate a credential');
    const writes = h.requests.filter(request => request.method !== 'GET');
    assert.equal(writes.length, h.runIds.length, 'only explicit fixture creation may write to the API');
    assert.equal(writes.every(request => request.method === 'POST' && request.pathname === '/api/runs'), true);
    assert.equal(h.requests.some(request => request.pathname.endsWith('/download')), false, 'activity export must use the local snapshot, including while running');
    checks.push({ name, elapsedMs: Math.round(performance.now() - started), fixtureCreates: h.runIds.length,
      featureApiWrites: writes.length - h.runIds.length, requests: h.requests });
    console.log(`PASS ${name}`);
  } catch (error) {
    failureScreenshot = `failure-${checks.length + 1}.png`;
    await page.screenshot({ path: path.join(output, failureScreenshot) }).catch(() => {});
    throw error;
  } finally {
    clearTimeout(deadline);
    for (const id of h.runIds) controls.get(id)?.finish();
    await context.close();
  }
}
async function createRun(h: Harness, title = 'Inspect local activity fixture') {
  const input: WebRunInput = { providerId: 'openai', apiKey: credential, model: 'fixture-activity-model', effort: 'low', environment: 'standard',
    source: 'theorem activity_fixture : True := by sorry', task: title, maxTurns: 2, maxRunSeconds: 60, workers: 1, coordination: 'independent' };
  const run = await h.page.evaluate(async input => {
    const session = await (await fetch('/api/session')).json();
    const response = await fetch('/api/runs', { method: 'POST', headers: { 'Content-Type': 'application/json', 'X-CSRF-Token': session.csrfToken }, body: JSON.stringify(input) });
    if (response.status !== 201) throw new Error(`Fixture creation failed: ${response.status}`);
    return (await response.json()).run as WebRun;
  }, input);
  h.runIds.push(run.id); assert.ok(controls.has(run.id), 'the local worker fixture must start');
  return run;
}
async function readRun(h: Harness, id: string): Promise<WebRun> {
  return h.page.evaluate(async id => (await (await fetch(`/api/runs/${id}`)).json()).run as WebRun, id);
}
async function showWorkspace(page: Page) {
  if (page.viewportSize()!.width <= 850) await page.locator('#mobile-runs').click();
}
async function selectActivity(h: Harness, id: string) {
  await openHistory(h.page); await h.page.locator('#refresh-runs:enabled').waitFor();
  const refreshed = h.page.waitForResponse(response => new URL(response.url()).pathname === '/api/runs' && response.request().method() === 'GET');
  await h.page.locator('#refresh-runs').click(); await refreshed;
  await h.page.locator('#refresh-runs:enabled').waitFor(); await closeHistory(h.page);
  await selectHistoryRun(h.page, id); await showWorkspace(h.page);
  await h.page.locator('#detail-tab-events').click(); await h.page.locator('.activity-workspace').waitFor();
}
async function rowCount(page: Page, expected: number) {
  await page.waitForFunction(({ selector, expected }) => document.querySelectorAll(selector).length === expected, { selector: rowSelector, expected });
  const numbers = (await page.locator('#activity-count').innerText()).match(/\d+/g)?.map(Number) ?? [];
  assert.equal(numbers[0], expected, 'the activity count must lead with the matched record count');
}
async function listed(page: Page, message: string) {
  await page.waitForFunction(({ selector, message }) => Array.from(document.querySelectorAll(selector))
    .some(row => row.lastElementChild?.textContent === message), { selector: rowSelector, message });
}
async function follow(page: Page, value: boolean) {
  await page.locator(`#activity-follow[aria-pressed="${value}"]`).waitFor();
}
async function settled(page: Page) {
  await page.evaluate(() => new Promise<void>(resolve => requestAnimationFrame(() => requestAnimationFrame(() => resolve()))));
}
async function pauseByScrolling(page: Page, top = 340) {
  await page.locator('.activity-scroll').evaluate((scroll, top) => { scroll.scrollTop = top; }, top);
  await follow(page, false); await settled(page);
  assert.ok(await page.locator('.activity-scroll').evaluate(scroll => scroll.scrollTop) > 30, 'the fixture must actually scroll away from the latest records');
}
async function anchor(page: Page): Promise<Anchor> {
  return page.locator('.activity-scroll').evaluate(scroll => {
    const frame = scroll.getBoundingClientRect(), heading = scroll.querySelector('thead th')!.getBoundingClientRect();
    const top = Math.max(frame.top + scroll.clientTop, heading.bottom), bottom = Math.min(frame.bottom, innerHeight);
    const row = Array.from(scroll.querySelectorAll<HTMLElement>('tbody tr[data-sequence]')).find(row => {
      const box = row.getBoundingClientRect(); return box.bottom > top + 1 && box.top < bottom;
    });
    if (!row) throw new Error('No activity row intersects the visible scroller');
    return { sequence: Number(row.dataset.sequence), offset: row.getBoundingClientRect().top - top, scrollTop: scroll.scrollTop, scrollLeft: scroll.scrollLeft };
  });
}
async function preservesAnchor(page: Page, label: string, before: Anchor) {
  await settled(page);
  const after = await anchor(page); anchors.push({ label, width: page.viewportSize()!.width, before, after });
  assert.equal(after.sequence, before.sequence, `${label}: a different activity row replaced the reading anchor`);
  assert.ok(Math.abs(after.offset - before.offset) <= 1.5, `${label}: visible row moved: ${JSON.stringify({ before, after })}`);
  assert.equal(after.scrollLeft, before.scrollLeft, `${label}: horizontal reading position moved`);
}
async function fit(page: Page, selector: string) {
  const box = await page.locator(selector).boundingBox(), viewport = page.viewportSize()!;
  assert.ok(box && box.x >= -1 && box.y >= -1 && box.x + box.width <= viewport.width + 1 && box.y + box.height <= viewport.height + 1,
    `${selector} must fit ${viewport.width}px: ${JSON.stringify(box)}`);
  assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth + 1), true, 'activity tools must not widen the document');
}
async function screenshot(page: Page, name: string) {
  await page.screenshot({ path: path.join(output, name) }); screenshots.push(name);
}
async function noInjection(page: Page) {
  assert.equal(await page.locator('[data-activity-injection]').count(), 0, 'activity type, message and search must remain inert text');
  assert.equal(await page.evaluate(() => (window as unknown as { __activityInjected?: boolean }).__activityInjected), undefined);
}
async function downloadActivity(h: Harness, run: WebRun, expectedEvents: WebEvent[], filters: { query: string; type: string | null }) {
  const started = Date.now(), pending = h.page.waitForEvent('download');
  await h.page.locator('#download-activity').click();
  const file = await pending;
  assert.equal(file.suggestedFilename(), `${run.id}-activity.json`);
  const raw = await fs.readFile((await file.path())!, 'utf8');
  assert.equal(raw.includes(credential), false, 'activity exports must preserve server credential redaction');
  const exported = JSON.parse(raw) as ActivityExport;
  assert.deepEqual(Object.keys(exported).sort(), ['format', 'version', 'runId', 'exportedAt', 'order', 'filters', 'retention', 'matchedCount', 'events'].sort());
  assert.equal(exported.format, 'theoremos-activity'); assert.equal(exported.version, 1);
  assert.equal(exported.runId, run.id); assert.equal(exported.order, 'newest-first');
  assert.ok(Date.parse(exported.exportedAt) >= started - 1000 && Date.parse(exported.exportedAt) <= Date.now() + 1000);
  assert.deepEqual(exported.filters, filters);
  assert.equal(exported.matchedCount, expectedEvents.length); assert.deepEqual(exported.events, expectedEvents);
  assert.deepEqual(exported.retention, { limit: 200, retainedCount: run.events.length,
    firstSequence: run.events[0]?.sequence ?? null, lastSequence: run.events.at(-1)?.sequence ?? null,
    earlierEventsOmitted: Boolean(run.events.length && run.events[0]!.sequence > 1) });
  exports.push({ runId: run.id, matchedCount: exported.matchedCount, retainedCount: exported.retention.retainedCount,
    earlierEventsOmitted: exported.retention.earlierEventsOmitted });
}
async function pollContains(page: Page, id: string, message: string) {
  return page.waitForResponse(async response => {
    if (new URL(response.url()).pathname !== '/api/runs' || response.request().method() !== 'GET' || response.status() !== 200) return false;
    const payload = await response.json() as { runs: WebRun[] };
    return payload.runs.some(run => run.id === id && run.events.some(event => event.message === message));
  });
}
async function writeReport(status: 'passed' | 'failed', error?: unknown) {
  const report = { status, checkedAt: new Date().toISOString(),
    mode: 'Real local HTTP service and Chromium with a controlled in-process runner. No models, Docker, Lean or external requests.',
    paidModelCalls: false, workerStarts, widths, checks, anchors, exports, screenshots,
    ...(error ? { failedScenario, error: error instanceof Error ? error.message : String(error), failureScreenshot } : {}) };
  assert.equal(JSON.stringify(report).includes(credential), false);
  await fs.writeFile(reportFile, JSON.stringify(report, null, 2) + '\n');
}

try {
  await new Promise<void>((resolve, reject) => { service.server.once('error', reject); service.server.listen(port, '127.0.0.1', resolve); });
  browser = await chromium.launch({ headless: true });

  await scenario('Literal keyword and type filters retain duplicate events and export only the active selection', async h => {
    const { page } = h, run = await createRun(h), control = controls.get(run.id)!;
    const repeated = 'Literal a+b[0].*? & 数学 🧪';
    control.progress('worker_activity', repeated); control.progress('worker_activity', repeated);
    control.progress('proof_checked', repeated); control.progress('worker_activity', 'Different message');
    control.progress(`<${markup.slice(1, 65)}>`, `Unsafe text ${markup}`);
    control.progress('diagnostic', `Diagnostic ${credential}\n${'完整诊断 '.repeat(600)}`);
    await selectActivity(h, run.id); await listed(page, 'Different message');
    assert.equal(await page.locator('#activity-search').getAttribute('type'), 'search');
    assert.equal(await page.locator('#activity-search').getAttribute('maxlength'), '256');
    const literalQuery = '  A+B[0].*?  ';
    await page.locator('#activity-search').fill(literalQuery); await rowCount(page, 3);
    await page.locator('#activity-type').selectOption('worker_activity'); await rowCount(page, 2);
    const snapshot = await readRun(h, run.id), expected = snapshot.events.filter(event => event.type === 'worker_activity' && event.message === repeated).reverse();
    const sequences = await page.locator(rowSelector).evaluateAll(rows => rows.map(row => Number((row as HTMLElement).dataset.sequence)));
    assert.deepEqual(sequences, expected.map(event => event.sequence));
    assert.equal(new Set(sequences).size, 2, 'identical messages must retain their distinct event sequences');
    await follow(page, true);
    assert.equal(snapshot.status, 'running'); assert.equal(snapshot.result, undefined);
    await downloadActivity(h, snapshot, expected, { query: literalQuery, type: 'worker_activity' });
    await page.locator('#activity-search').fill('no matching record'); await rowCount(page, 0);
    await page.locator('#clear-activity-filters').click();
    assert.equal(await page.locator('#activity-search').inputValue(), ''); assert.equal(await page.locator('#activity-type').inputValue(), '');
    await rowCount(page, snapshot.events.length);
    await page.locator('#activity-search').fill(markup); await rowCount(page, 1); await noInjection(page);
    await page.locator('#clear-activity-search').click(); await rowCount(page, snapshot.events.length);
    await page.locator('#activity-type').selectOption('diagnostic'); await rowCount(page, 1);
    const diagnostic = snapshot.events.filter(event => event.type === 'diagnostic');
    assert.ok(diagnostic[0]!.message.includes('[REDACTED]')); assert.equal(diagnostic[0]!.message.length, 2000);
    await downloadActivity(h, snapshot, diagnostic, { query: '', type: 'diagnostic' });
    await screenshot(page, 'filtered-active-export.png');
  });

  await scenario('Multiline arrivals preserve the reading anchor, selected text, input focus and matched unread count', async h => {
    const { page } = h, run = await createRun(h), control = controls.get(run.id)!;
    for (let index = 0; index < 85; index++) control.progress('worker_activity', `inspect reading step ${index + 1}`);
    await selectActivity(h, run.id); await listed(page, 'inspect reading step 85');
    await page.locator('#activity-search').fill('inspect'); await rowCount(page, 85);
    await pauseByScrolling(page); const before = await anchor(page);
    await page.locator('#activity-search').focus();
    await page.evaluate(sequence => {
      const input = document.querySelector<HTMLInputElement>('#activity-search')!, workspace = document.querySelector('.activity-workspace')!, scroll = document.querySelector('.activity-scroll')!;
      input.setSelectionRange(1, 4);
      const row = document.querySelector(`.activity-table tbody tr[data-sequence="${sequence}"]`)!, cell = row.lastElementChild!;
      const textNode = cell.firstChild!, range = document.createRange(); range.setStart(textNode, 0); range.setEnd(textNode, 7);
      getSelection()!.removeAllRanges(); getSelection()!.addRange(range);
      (window as unknown as { __activityProbe: unknown }).__activityProbe = { input, workspace, scroll, selection: getSelection()!.toString(),
        rows: Array.from(document.querySelectorAll('.activity-table tbody tr[data-sequence]')).map(row => ({ sequence: (row as HTMLElement).dataset.sequence, node: row })) };
    }, before.sequence);
    const multiline = `inspect multiline arrival\n${Array.from({ length: 16 }, (_, index) => `Detail line ${index + 1}`).join('\n')}`;
    control.progress('new_activity_type', multiline); control.progress('worker_activity', 'inspect one more matching event');
    control.progress('proof_checked', 'not a match');
    await listed(page, multiline); await rowCount(page, 87); await preservesAnchor(page, 'multiline insertion', before);
    const stable = await page.evaluate(() => {
      type Probe = { input: HTMLInputElement; workspace: Element; scroll: Element; selection: string; rows: Array<{ sequence: string; node: Element }> };
      const before = (window as unknown as { __activityProbe: Probe }).__activityProbe;
      return { sameInput: before.input === document.querySelector('#activity-search'), sameWorkspace: before.workspace === document.querySelector('.activity-workspace'),
        sameScroll: before.scroll === document.querySelector('.activity-scroll'), focused: before.input === document.activeElement,
        inputSelection: [before.input.selectionStart, before.input.selectionEnd], textSelection: getSelection()!.toString(), beforeSelection: before.selection,
        oldRowsRetained: before.rows.every(row => row.node === document.querySelector(`.activity-table tbody tr[data-sequence="${row.sequence}"]`)) };
    });
    // Chromium clears an input's selection when a separate DOM Range is selected.
    assert.deepEqual(stable, { sameInput: true, sameWorkspace: true, sameScroll: true, focused: true, inputSelection: [0, 0],
      textSelection: 'inspect', beforeSelection: 'inspect', oldRowsRetained: true });
    assert.equal(await page.locator('#activity-type option[value="new_activity_type"]').count(), 1, 'new types must join the existing type control');
    await follow(page, false); assert.match(await page.locator('#activity-latest').innerText(), /2/);
    await screenshot(page, 'paused-multiline-arrivals.png');
    await page.locator('#activity-search').evaluate(input => {
      getSelection()!.removeAllRanges();
      (input as HTMLInputElement).focus({ preventScroll: true });
      (input as HTMLInputElement).setSelectionRange(1, 4);
    });
    const beforeInputSelection = await anchor(page);
    control.progress('worker_activity', 'inspect arrival while the search input has a selection');
    await listed(page, 'inspect arrival while the search input has a selection');
    await preservesAnchor(page, 'focused search selection', beforeInputSelection);
    assert.deepEqual(await page.locator('#activity-search').evaluate(input => {
      const search = input as HTMLInputElement;
      return { focused: document.activeElement === search, start: search.selectionStart, end: search.selectionEnd };
    }), { focused: true, start: 1, end: 4 });
    assert.match(await page.locator('#activity-latest').innerText(), /3/);
    await page.locator('#activity-latest').click(); await follow(page, true);
    assert.ok(await page.locator('.activity-scroll').evaluate(scroll => scroll.scrollTop) <= 1);
    await page.locator('#activity-follow').click(); await follow(page, false); const pausedAtTop = await anchor(page);
    control.progress('worker_activity', 'inspect arrival while explicitly paused at top');
    await listed(page, 'inspect arrival while explicitly paused at top');
    await follow(page, false); await preservesAnchor(page, 'explicit pause at newest row', pausedAtTop);
    await page.locator('#activity-follow').click(); await follow(page, true);
    assert.ok(await page.locator('.activity-scroll').evaluate(scroll => scroll.scrollTop) <= 1);
  });

  await scenario('Rotation retains a vanished type selection and explains when the reading anchor has expired', async h => {
    const { page } = h, run = await createRun(h), control = controls.get(run.id)!;
    control.progress('vanishing_type', 'One old type that will rotate out');
    for (let index = 0; index < 55; index++) control.progress('worker_activity', `retention baseline ${index + 1}`);
    await selectActivity(h, run.id); await listed(page, 'retention baseline 55');
    await page.locator('#activity-type').selectOption('vanishing_type'); await rowCount(page, 1);
    for (let index = 0; index < 210; index++) control.progress('worker_activity', `retention first wave ${index + 1}`);
    await page.waitForFunction(() => document.querySelector('#activity-retention')?.textContent?.includes('200') && document.querySelectorAll('.activity-table tbody tr[data-sequence]').length === 0);
    assert.equal(await page.locator('#activity-type').inputValue(), 'vanishing_type');
    assert.equal(await page.locator('#activity-type option[value="vanishing_type"]').count(), 1);
    await rowCount(page, 0); assert.ok((await page.locator('#activity-retention').innerText()).trim());
    await page.locator('#clear-activity-filters').click(); await rowCount(page, 200);
    await listed(page, 'retention first wave 210');
    const retainedBefore = await readRun(h, run.id), oldNewest = retainedBefore.events.at(-1)!.sequence;
    await pauseByScrolling(page, 1_000_000); const expired = await anchor(page);
    assert.ok(retainedBefore.events.slice(0, 20).some(event => event.sequence === expired.sequence),
      'the actually visible reading anchor must be among the oldest twenty records');
    for (let index = 0; index < 20; index++) control.progress('worker_activity', `retention second wave ${index + 1}`);
    await listed(page, 'retention second wave 20'); await rowCount(page, 200); await follow(page, false);
    assert.equal(await page.locator(`${rowSelector}[data-sequence="${expired.sequence}"]`).count(), 0, 'the fixture must evict the actual reading anchor');
    assert.equal(await page.locator(`${rowSelector}[data-sequence="${oldNewest}"]`).count(), 1,
      'partial rotation must retain the old latest event, so it cannot stand in for the actual reading anchor');
    assert.equal(await page.locator('#activity-reading-notice').isVisible(), true);
    assert.ok((await page.locator('#activity-reading-notice').innerText()).trim(), 'expired reading positions must be explained');
    const snapshot = await readRun(h, run.id);
    assert.equal(snapshot.events.length, 200); assert.ok(snapshot.events[0]!.sequence > 1);
    await downloadActivity(h, snapshot, [...snapshot.events].reverse(), { query: '', type: null });
    await screenshot(page, 'retention-expired-anchor.png');
  });

  await scenario('Activity tab returns retain filters and reading position while another run starts fresh', async h => {
    const { page } = h, run = await createRun(h), control = controls.get(run.id)!;
    for (let index = 0; index < 70; index++) control.progress('worker_activity', `inspect tab history ${index + 1}`);
    const other = await createRun(h, 'A different local activity fixture');
    controls.get(other.id)!.progress('proof_checked', 'Other run event');
    await selectActivity(h, run.id); await listed(page, 'inspect tab history 70');
    await page.locator('#activity-search').fill('inspect'); await page.locator('#activity-type').selectOption('worker_activity'); await rowCount(page, 70);
    await pauseByScrolling(page); const before = await anchor(page);
    await page.locator('#detail-tab-source').click();
    control.progress('worker_activity', 'inspect arrival while source tab is open');
    const response = await pollContains(page, run.id, 'inspect arrival while source tab is open'); assert.equal(response.status(), 200);
    await page.locator('#detail-tab-events').click();
    assert.equal(await page.locator('#activity-search').inputValue(), 'inspect'); assert.equal(await page.locator('#activity-type').inputValue(), 'worker_activity');
    await rowCount(page, 71); await follow(page, false); await preservesAnchor(page, 'same-run tab return', before);
    await selectActivity(h, other.id); await listed(page, 'Other run event');
    assert.equal(await page.locator('#activity-search').inputValue(), ''); assert.equal(await page.locator('#activity-type').inputValue(), '');
    await follow(page, true); assert.ok(await page.locator('.activity-scroll').evaluate(scroll => scroll.scrollTop) <= 1);
    await screenshot(page, 'different-run-reset.png');
  });

  for (const width of widths) await scenario(`Activity controls fit and preserve visible or hidden reading at ${width}px`, async h => {
    const { page } = h, run = await createRun(h), control = controls.get(run.id)!;
    for (let index = 0; index < 60; index++) control.progress('worker_activity', `inspect responsive activity ${index + 1}\nA second diagnostic line`);
    await selectActivity(h, run.id); await listed(page, 'inspect responsive activity 60\nA second diagnostic line');
    await page.locator('#activity-search').fill('inspect'); await rowCount(page, 60); await pauseByScrolling(page);
    for (const selector of ['.activity-workspace', '#activity-search', '#activity-type', '#clear-activity-search', '#activity-count', '#activity-follow', '#activity-latest', '#download-activity', '.activity-scroll']) await fit(page, selector);
    await screenshot(page, `activity-${width}.png`);
    if (width <= 850) {
      const before = await anchor(page);
      await page.locator('#mobile-compose').click();
      const matching = `inspect hidden mobile arrival at ${width}px\n${'Additional diagnostic line\n'.repeat(9)}`;
      const arrived = pollContains(page, run.id, matching);
      control.progress('worker_activity', matching); await arrived;
      await page.locator('#mobile-runs').click(); await listed(page, matching); await follow(page, false);
      await preservesAnchor(page, `hidden ${width}px workspace`, before);
      await page.locator('#activity-latest').click(); await follow(page, true);
      await page.locator('#mobile-compose').click();
      const latest = `inspect followed hidden mobile arrival ${width}px`, followed = pollContains(page, run.id, latest);
      control.progress('worker_activity', latest); await followed;
      await page.locator('#mobile-runs').click(); await listed(page, latest); await follow(page, true);
      assert.ok(await page.locator('.activity-scroll').evaluate(scroll => scroll.scrollTop) <= 1, 'a followed hidden workspace must return at its latest activity');
      await page.locator('#activity-search').fill('zero matching mobile result'); await rowCount(page, 0);
      await fit(page, '#clear-activity-filters'); await page.locator('#clear-activity-filters').click();
      assert.equal(await page.locator('#activity-search').inputValue(), '');
      await screenshot(page, `activity-${width}-returned.png`);
      if (width === 375) {
        await page.locator('#activity-search').fill('inspect');
        await page.locator('#activity-type').selectOption('worker_activity');
        await pauseByScrolling(page);
        const visible = await anchor(page);
        await page.locator('.activity-scroll').evaluate((scroll, sequence) => {
          const row = scroll.querySelector(`tr[data-sequence="${sequence}"]`)!, heading = scroll.querySelector('thead th')!;
          scroll.scrollTop += row.getBoundingClientRect().top - heading.getBoundingClientRect().bottom;
        }, visible.sequence);
        await settled(page);
        const beforeResize = await anchor(page);
        await page.locator('#mobile-compose').click();
        const resizedArrival = 'inspect arrival before resizing a hidden mobile workspace';
        const received = pollContains(page, run.id, resizedArrival);
        control.progress('worker_activity', resizedArrival); await received;
        await page.setViewportSize({ width: 1440, height: 900 });
        await listed(page, resizedArrival); await follow(page, false);
        assert.equal(await page.locator('#activity-search').inputValue(), 'inspect');
        assert.equal(await page.locator('#activity-type').inputValue(), 'worker_activity');
        await preservesAnchor(page, 'hidden mobile workspace resized directly to desktop', beforeResize);
        await fit(page, '.activity-workspace');
        await screenshot(page, 'activity-hidden-mobile-to-desktop.png');
      }
    }
  }, width);

  await writeReport('passed');
  console.log(`Activity checks passed: ${checks.length} scenarios; local filtering and active exports, stable reading anchors, selection/focus, bounded retention, run and tab scopes, and mobile layouts.`);
  console.log(`Report: ${path.relative(root, reportFile)}`);
} catch (error) {
  await writeReport('failed', error); throw error;
} finally {
  await browser?.close(); await service.close();
}
