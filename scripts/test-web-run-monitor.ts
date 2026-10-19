#!/usr/bin/env bun
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import net from 'node:net';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium, type BrowserContext, type Page, type Route } from 'playwright';
import { readWebConfig } from '../apps/web/config';
import type { TaskDraft } from '../apps/web/client/draft';
import { createWebService } from '../apps/web/server';
import type { WebRunner } from '../apps/web/runner';
import type { WebRun, WebRunInput } from '../apps/web/shared';
import { closeHistory, openHistory, withSettings } from './web-ui-controls';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const output = path.join(root, 'out/web-run-monitor'), reportFile = path.join(output, 'report.json');
const recoveryKey = 'theorem-os.web-draft-recovery.v1';
const credential = `sk-theoremos-monitor-fixture-${crypto.randomUUID()}`;
const injection = '<img data-monitor-injection src=x onerror="window.__monitorInjected=true">';
const widths = [1440, 375, 320];
await fs.access(path.join(root, 'out/web/app.js')).catch(() => { throw new Error('Run bun run build:web before the run monitor check.'); });
await fs.mkdir(output, { recursive: true }); await fs.rm(reportFile, { force: true });
const probe = net.createServer();
await new Promise<void>(resolve => probe.listen(0, '127.0.0.1', resolve));
const port = (probe.address() as net.AddressInfo).port;
await new Promise<void>((resolve, reject) => probe.close(error => error ? reject(error) : resolve()));
const origin = `http://127.0.0.1:${port}`;
type Control = { progress(type: string, message: string): void; finish(): void; fail(): void };
const controls = new Map<string, Control>();
let workerStarts = 0, workerAborts = 0;
const runner: WebRunner = {
  async readiness() { return { ready: true, message: 'Local run monitor fixture' }; },
  async run(input, send, signal) {
    workerStarts++;
    await new Promise<void>((resolve, reject) => {
      const cleanup = () => { controls.delete(input.id); signal.removeEventListener('abort', abort); };
      const abort = () => { workerAborts++; cleanup(); reject(new Error('Cancelled local monitor fixture')); };
      controls.set(input.id, {
        progress: (event, message) => send({ type: 'progress', event, message }),
        finish: () => { cleanup(); send({ type: 'result', result: { status: 'incomplete', proof: input.input.source, report: { fixture: true } } }); resolve(); },
        fail: () => { cleanup(); reject(new Error('Local monitor fixture failed')); },
      });
      signal.addEventListener('abort', abort, { once: true }); if (signal.aborted) abort();
    });
  },
};
const service = createWebService(readWebConfig({ THEOREMOS_WEB_PORT: String(port), THEOREMOS_WEB_PUBLIC_URL: origin,
  THEOREMOS_WEB_STATIC_ROOT: path.join(root, 'out/web'), THEOREMOS_WEB_CONCURRENCY: '2', THEOREMOS_WEB_QUEUE_LIMIT: '32' }), runner);
type RequestRecord = { method: string; pathname: string };
type Harness = { page: Page; context: BrowserContext; requests: RequestRecord[]; creates: number; deletes: number;
  owners: Set<string>; intercept?: (route: Route) => Promise<boolean>; releases: Array<() => void | Promise<void>> };
type Editable = { draft: TaskDraft; key: string; recovery: string | null; query: string; filter: string };
const checks: Array<{ name: string; width: number; elapsedMs: number; fixtureCreates: number; fixtureDeletes: number;
  cancelRequests: number; unexpectedWrites: number; requests: RequestRecord[] }> = [];
const screenshots: string[] = [], restorations: Array<{ width: number; keyPreserved: boolean; backupPreserved: boolean }> = [];
const readingChecks: Array<{ listScrollable: boolean; beforeListLeft: number; afterListLeft: number; beforeChatTop: number; afterChatTop: number }> = [];
let raceEvidence: { confirmedByGetBeforeLostResponse: boolean; cancelPosts: number; extraSessionRequests: number; workerAborts: number } | undefined;
let browser: Awaited<ReturnType<typeof chromium.launch>> | undefined;
let failedScenario = '', failureScreenshot = '';
const row = (id: string) => `[data-monitor-id="${id}"]`;
const opener = (id: string) => `[data-monitor-run-id="${id}"]`;
const dismiss = (id: string) => `[data-dismiss-run-notice="${id}"]`;
const isList = (route: Route) => route.request().method() === 'GET' && new URL(route.request().url()).pathname === '/api/runs';
function deferred() { let resolve!: () => void; const promise = new Promise<void>(done => { resolve = done; }); return { promise, resolve }; }
const count = (h: Harness, method: string, pathname: string) => h.requests.filter(request => request.method === method && request.pathname === pathname).length;
async function settled(page: Page) { await page.evaluate(() => new Promise<void>(resolve => requestAnimationFrame(() => requestAnimationFrame(() => resolve())))); }

async function scenario(name: string, run: (h: Harness) => Promise<void>, width = 1440, expectedCancels = 0) {
  failedScenario = name;
  const started = performance.now(), context = await browser!.newContext({ viewport: { width, height: width > 850 ? 900 : 812 }, reducedMotion: 'reduce' });
  const page = await context.newPage(); page.setDefaultTimeout(10_000);
  const h: Harness = { page, context, requests: [], creates: 0, deletes: 0, owners: new Set(), releases: [] };
  const errors: string[] = [], external: string[] = [];
  page.on('pageerror', error => errors.push(error.message));
  await context.route(/^https?:\/\//, async route => {
    const url = new URL(route.request().url());
    if (url.origin !== origin) { external.push(url.href); await route.abort(); return; }
    if (url.pathname.startsWith('/api/')) {
      h.requests.push({ method: route.request().method(), pathname: url.pathname });
      if (await h.intercept?.(route)) return;
    }
    await route.continue();
  });
  let deadline: ReturnType<typeof setTimeout> | undefined;
  try {
    await Promise.race([run(h), new Promise<never>((_, reject) => {
      deadline = setTimeout(() => reject(new Error(`Run monitor scenario exceeded 50 seconds: ${name}`)), 50_000);
    })]);
    assert.deepEqual(errors, [], 'uncaught browser errors'); assert.deepEqual(external, [], 'monitor operations must remain local');
    const writes = h.requests.filter(request => request.method !== 'GET');
    const cancels = writes.filter(request => request.method === 'POST' && /^\/api\/runs\/[^/]+\/cancel$/.test(request.pathname)).length;
    assert.equal(count(h, 'POST', '/api/runs'), h.creates, 'monitor navigation must not submit a research task');
    assert.equal(writes.filter(request => request.method === 'DELETE').length, h.deletes);
    assert.equal(cancels, expectedCancels, 'cancel must run only for an explicit fixture or user command');
    assert.equal(writes.length, h.creates + h.deletes + expectedCancels, 'unexpected API write');
    await privacy(page);
    checks.push({ name, width, elapsedMs: Math.round(performance.now() - started), fixtureCreates: h.creates,
      fixtureDeletes: h.deletes, cancelRequests: cancels, unexpectedWrites: writes.length - h.creates - h.deletes - cancels, requests: h.requests });
    console.log(`PASS ${name}`);
  } catch (error) {
    failureScreenshot = `failure-${checks.length + 1}.png`;
    await page.screenshot({ path: path.join(output, failureScreenshot) }).catch(() => {}); throw error;
  } finally {
    clearTimeout(deadline);
    for (const release of h.releases) await release();
    await collectOwner(h);
    for (const owner of h.owners) service.jobs.forget(owner);
    await context.close();
  }
}
async function collectOwner(h: Harness) {
  const cookie = (await h.context.cookies(origin)).find(cookie => cookie.name === 'theoremos_session');
  if (cookie) h.owners.add(cookie.value);
}
async function open(h: Harness) { await h.page.goto(origin); await h.page.locator('#submit-run:enabled').waitFor(); await collectOwner(h); }
async function refresh(h: Harness) {
  await openHistory(h.page); await h.page.locator('#refresh-runs:enabled').waitFor();
  const loaded = h.page.waitForResponse(response => new URL(response.url()).pathname === '/api/runs' && response.request().method() === 'GET');
  await h.page.locator('#refresh-runs').click(); await loaded;
  await h.page.locator('#refresh-runs:enabled').waitFor(); await closeHistory(h.page); await settled(h.page);
}
async function createRun(h: Harness, title = 'Local monitored task') {
  const input: WebRunInput = { providerId: 'openai', apiKey: credential, model: 'fixture-monitor-model', effort: 'low', environment: 'standard',
    source: 'theorem monitored_fixture : True := by sorry', task: title, maxTurns: 2, maxRunSeconds: 60, workers: 1, coordination: 'independent' };
  const run = await h.page.evaluate(async input => {
    const session = await (await fetch('/api/session')).json();
    const response = await fetch('/api/runs', { method: 'POST', headers: { 'Content-Type': 'application/json', 'X-CSRF-Token': session.csrfToken }, body: JSON.stringify(input) });
    if (response.status !== 201) throw new Error(`Monitor fixture creation failed: ${response.status}`);
    return (await response.json()).run as WebRun;
  }, input);
  h.creates++; await collectOwner(h); return run;
}
async function mutateFixture(h: Harness, id: string, method: 'DELETE' | 'POST') {
  const pathname = `/api/runs/${id}${method === 'POST' ? '/cancel' : ''}`;
  const status = await h.page.evaluate(async ({ pathname, method }) => {
    const session = await (await fetch('/api/session')).json();
    return (await fetch(pathname, { method, headers: { 'X-CSRF-Token': session.csrfToken } })).status;
  }, { pathname, method });
  assert.equal(status, 200);
  if (method === 'DELETE') h.deletes++;
}
async function readRun(h: Harness, id: string): Promise<WebRun> {
  return h.page.evaluate(async id => (await (await fetch(`/api/runs/${id}`)).json()).run as WebRun, id);
}
async function waitTerminal(h: Harness, id: string) {
  await h.page.waitForFunction(async id => {
    const response = await fetch(`/api/runs/${id}`);
    const run = (await response.json()).run as WebRun;
    return !['queued', 'running'].includes(run.status);
  }, id);
}
async function monitorItems(page: Page, expected: string[]) {
  await page.waitForFunction(expected => {
    const ids = Array.from(document.querySelectorAll<HTMLElement>('#run-monitor-list [data-monitor-id]')).map(item => item.dataset.monitorId!);
    return ids.length === expected.length && expected.every(id => ids.includes(id));
  }, expected);
  assert.equal(await page.locator('#run-monitor').isVisible(), Boolean(expected.length));
}
async function openMonitored(page: Page, id: string, terminal = false) {
  await page.locator(opener(id)).click();
  await page.waitForFunction(id => document.querySelector('.detail-identifier code')?.textContent === id, id);
  assert.equal(await page.locator(`#detail-tab-${terminal ? 'report' : 'source'}`).getAttribute('aria-selected'), 'true');
  assert.equal(await page.locator('#return-to-draft').evaluate(button => (button as HTMLButtonElement).hidden), false);
  if (page.viewportSize()!.width > 850) assert.equal(await page.locator('#return-to-draft').isVisible(), true);
  if (page.viewportSize()!.width <= 850) assert.equal(await page.evaluate(() => document.body.dataset.mobileView), 'runs');
}
async function editable(page: Page): Promise<Editable> {
  return page.evaluate(key => {
    const value = (id: string) => (document.getElementById(id) as HTMLInputElement).value;
    return { draft: { providerId: value('provider'), model: value('model'), source: value('source'), task: value('task'),
      maxTurns: value('max-turns'), maxRunSeconds: value('max-seconds'), workers: value('workers'), effort: value('effort'),
      environment: value('environment'), coordination: (document.querySelector('input[name="coordination"]:checked') as HTMLInputElement).value,
      templateId: value('template') } as TaskDraft, key: value('api-key'), recovery: sessionStorage.getItem(key), query: value('run-search'), filter: value('run-filter') };
  }, recoveryKey);
}
async function preserved(page: Page, before: Editable) { assert.deepEqual(await editable(page), before, 'monitor actions must preserve every draft field, Key, backup and history filter'); }
async function returnToDraft(page: Page, before: Editable) {
  if (page.viewportSize()!.width <= 850) await page.locator('#mobile-compose').click();
  await fit(page, '#return-to-draft');
  await page.locator('#return-to-draft').click(); await preserved(page, before);
  assert.equal(await page.locator('#return-to-draft').isVisible(), false);
  assert.equal(await page.locator('#task').evaluate(input => input === document.activeElement), true);
  if (page.viewportSize()!.width <= 850) assert.equal(await page.evaluate(() => document.body.dataset.mobileView), 'compose');
  else assert.equal(await page.locator('#draft-preview').count(), 1);
  restorations.push({ width: page.viewportSize()!.width, keyPreserved: true, backupPreserved: true });
}
async function prepareDraft(page: Page) {
  await page.locator('#new-research').click();
  await withSettings(page, async () => {
    await page.locator('#environment').selectOption('standard'); await page.locator('#template').selectOption('');
    await page.locator('#source').fill(`-- ${injection}\ntheorem unsent_monitor_draft : True := by sorry\n`);
    await page.locator('#model').fill('fixture-unsent-model'); await page.locator('#effort').selectOption('medium');
    await page.locator('#max-turns').fill('4'); await page.locator('#max-seconds').fill('120'); await page.locator('#workers').fill('2');
    await page.locator('input[name="coordination"][value="independent"]').check();
  });
  await page.locator('#task').fill(`Unsent task ${injection}`);
  await page.locator('[data-chat-template="logic"]').click();
  await withSettings(page, () => page.locator('#api-key').fill(credential));
  await openHistory(page); await page.locator('#run-filter').selectOption('passed'); await page.locator('#run-search').fill('no matching fixture task');
  await closeHistory(page);
  const draft = await editable(page); assert.ok(draft.recovery, 'the fixture must include an existing replacement backup');
  return draft;
}
async function privacy(page: Page) {
  const stored = await page.evaluate(() => ({ session: JSON.stringify(sessionStorage), local: JSON.stringify(localStorage), text: document.body.innerText }));
  assert.equal(stored.session.includes(credential), false); assert.equal(stored.local.includes(credential), false);
  assert.equal(stored.text.includes(credential), false);
  assert.equal(await page.locator('[data-monitor-injection]').count(), 0);
  assert.equal(await page.evaluate(() => (window as unknown as { __monitorInjected?: boolean }).__monitorInjected), undefined);
}
async function fit(page: Page, selector: string) {
  const box = await page.locator(selector).boundingBox(), viewport = page.viewportSize()!;
  assert.ok(box && box.x >= -1 && box.y >= -1 && box.x + box.width <= viewport.width + 1 && box.y + box.height <= viewport.height + 1,
    `${selector} must fit ${viewport.width}px: ${JSON.stringify(box)}`);
  assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth + 1), true, 'monitor must not widen the page');
}
async function screenshot(page: Page, name: string) { await page.screenshot({ path: path.join(output, name) }); screenshots.push(name); }
async function pollWith(page: Page, id: string, predicate: 'cancelled' | 'marker', marker = '') {
  return page.waitForResponse(async response => {
    if (response.request().method() !== 'GET' || new URL(response.url()).pathname !== '/api/runs' || response.status() !== 200) return false;
    const { runs } = await response.json() as { runs: WebRun[] }, run = runs.find(run => run.id === id);
    return Boolean(run && (predicate === 'cancelled' ? run.status === 'cancelled' : run.events.some(event => event.message === marker)));
  });
}
async function writeReport(status: 'passed' | 'failed', error?: unknown) {
  const report = { status, checkedAt: new Date().toISOString(),
    mode: 'Real temporary-port HTTP service and Chromium with a controlled in-process runner, queued tasks and response gates. No models, Docker, Lean or external requests.',
    paidModelCalls: false, workerStarts, workerAborts, widths, checks, restorations, readingChecks, raceEvidence, screenshots,
    ...(error ? { failedScenario, error: error instanceof Error ? error.message : String(error), failureScreenshot } : {}) };
  assert.equal(JSON.stringify(report).includes(credential), false);
  await fs.writeFile(reportFile, JSON.stringify(report, null, 2) + '\n');
}

try {
  await new Promise<void>((resolve, reject) => { service.server.once('error', reject); service.server.listen(port, '127.0.0.1', resolve); });
  browser = await chromium.launch({ headless: true });

  await scenario('Initial terminal history stays quiet while every queued and running task is monitored', async h => {
    const firstList = deferred(), release = deferred(); h.releases.push(release.resolve);
    let hold = true;
    h.intercept = async route => { if (isList(route) && hold) { hold = false; firstList.resolve(); await release.promise; } return false; };
    await h.page.goto(origin); await firstList.promise;
    const old = await createRun(h, 'Already completed before the initial list'); controls.get(old.id)!.finish(); await waitTerminal(h, old.id);
    release.resolve(); await h.page.locator('#submit-run:enabled').waitFor(); await settled(h.page); await monitorItems(h.page, []);
    await h.page.locator('#new-research').click();
    const a = await createRun(h, 'Running task A'), b = await createRun(h, 'Running task B'), queued = await createRun(h, 'Queued task C');
    assert.equal((await readRun(h, queued.id)).status, 'queued'); assert.equal(controls.has(queued.id), false);
    await refresh(h); await monitorItems(h.page, [a.id, b.id, queued.id]);
    assert.equal(await h.page.locator('[data-dismiss-run-notice]:visible').count(), 0, 'active tasks cannot be dismissed from monitoring');
    assert.ok((await h.page.locator('#run-monitor-summary').innerText()).trim());
    await screenshot(h.page, 'queued-and-running.png');
  });

  await scenario('Only background transitions retain completion notices until opened, dismissed or deleted', async h => {
    const { page } = h; await open(h); await page.locator('#new-research').click();
    const selected = await createRun(h, 'Foreground completion'), failed = await createRun(h, 'Background failed task'), cancelled = await createRun(h, 'Background cancelled task');
    await refresh(h); await monitorItems(page, [selected.id, failed.id, cancelled.id]); await openMonitored(page, selected.id);
    await mutateFixture(h, cancelled.id, 'POST'); controls.get(selected.id)!.finish(); controls.get(failed.id)!.fail();
    await waitTerminal(h, selected.id); await waitTerminal(h, failed.id); await refresh(h);
    await monitorItems(page, [failed.id, cancelled.id]);
    assert.equal(await page.locator(dismiss(failed.id)).isVisible(), true); assert.equal(await page.locator(dismiss(cancelled.id)).isVisible(), true);
    await refresh(h); await monitorItems(page, [failed.id, cancelled.id]);
    await screenshot(page, 'background-completion-notices.png');
    await openMonitored(page, cancelled.id, true); await monitorItems(page, [failed.id]);
    await page.locator(dismiss(failed.id)).click(); await monitorItems(page, []);
    const removed = await createRun(h, 'Background notice removed with history'); await refresh(h);
    await monitorItems(page, [removed.id]); controls.get(removed.id)!.finish(); await waitTerminal(h, removed.id); await refresh(h);
    assert.equal(await page.locator(dismiss(removed.id)).isVisible(), true);
    await mutateFixture(h, removed.id, 'DELETE'); await refresh(h); await monitorItems(page, []);
  }, 1440, 1);

  await scenario('A new session clears old completion notices without reviving terminal history', async h => {
    const { page } = h; await open(h); await page.locator('#new-research').click();
    const run = await createRun(h, 'Completion from the previous session'); await refresh(h); await monitorItems(page, [run.id]);
    controls.get(run.id)!.finish(); await waitTerminal(h, run.id); await refresh(h);
    assert.equal(await page.locator(dismiss(run.id)).isVisible(), true);
    const session = page.waitForResponse(response => new URL(response.url()).pathname === '/api/session' && response.status() === 200);
    await h.context.clearCookies(); await refresh(h); await session; await page.locator('#submit-run:enabled').waitFor();
    await monitorItems(page, []); assert.equal(await page.locator(`[data-run-id="${run.id}"]`).count(), 0);
  });

  await scenario('Monitor polling reuses nodes and preserves keyboard focus, list scroll and paused conversation reading', async h => {
    const { page } = h; await open(h); await page.locator('#new-research').click();
    const runs: WebRun[] = [];
    for (let index = 0; index < 10; index++) runs.push(await createRun(h, `Task ${index + 1}: ${'A long monitored mathematical research title '.repeat(3)}`));
    await refresh(h); await monitorItems(page, runs.map(run => run.id)); await openMonitored(page, runs[0]!.id);
    const control = controls.get(runs[0]!.id)!;
    for (let index = 0; index < 85; index++) control.progress('worker_activity', `Conversation reading record ${index + 1}`);
    await page.waitForFunction(() => document.querySelector('#conversation')?.textContent?.includes('Conversation reading record 85'));
    await page.locator('#conversation-scroll').evaluate(scroll => { scroll.scrollTop = 120; }); await settled(page);
    assert.ok(await page.locator('#conversation-scroll').evaluate(scroll => scroll.scrollTop) > 30, 'the conversation fixture must actually pause reading');
    await page.evaluate(id => {
      const root = document.querySelector('#run-monitor')!, list = document.querySelector<HTMLElement>('#run-monitor-list')!;
      const button = document.querySelector<HTMLElement>(`[data-monitor-run-id="${id}"]`)!;
      list.scrollLeft = Math.min(240, list.scrollWidth - list.clientWidth); button.focus({ preventScroll: true });
      (window as unknown as { __monitorProbe: unknown }).__monitorProbe = { root, list, button, focused: document.activeElement,
        rows: Array.from(list.querySelectorAll<HTMLElement>('[data-monitor-id]')).map(row => ({ id: row.dataset.monitorId!, node: row })),
        listLeft: list.scrollLeft, listScrollable: list.scrollWidth > list.clientWidth,
        chatTop: document.querySelector('#conversation-scroll')!.scrollTop };
    }, runs[1]!.id);
    const marker = 'A new event while monitor controls have focus', arrived = pollWith(page, runs[0]!.id, 'marker', marker);
    control.progress('worker_activity', marker); await arrived; await settled(page);
    const stable = await page.evaluate(() => {
      type Probe = { root: Element; list: HTMLElement; button: Element; focused: Element; rows: Array<{ id: string; node: Element }>;
        listLeft: number; listScrollable: boolean; chatTop: number };
      const p = (window as unknown as { __monitorProbe: Probe }).__monitorProbe;
      return { sameRoot: p.root === document.querySelector('#run-monitor'), sameList: p.list === document.querySelector('#run-monitor-list'),
        sameButton: p.button === document.querySelector(`[data-monitor-run-id="${(p.button as HTMLElement).dataset.monitorRunId}"]`),
        focusPreserved: p.focused === document.activeElement, rowsRetained: p.rows.every(row => row.node === document.querySelector(`[data-monitor-id="${row.id}"]`)),
        listScrollable: p.listScrollable, beforeListLeft: p.listLeft, afterListLeft: p.list.scrollLeft,
        beforeChatTop: p.chatTop, afterChatTop: document.querySelector('#conversation-scroll')!.scrollTop };
    });
    assert.equal(stable.sameRoot && stable.sameList && stable.sameButton && stable.focusPreserved && stable.rowsRetained, true,
      `monitor polling replaced a node or focus: ${JSON.stringify(stable)}`);
    assert.equal(stable.listScrollable, true, 'the monitor fixture must overflow horizontally');
    assert.ok(stable.beforeListLeft > 0, 'the monitor fixture must actually scroll horizontally');
    assert.ok(Math.abs(stable.afterListLeft - stable.beforeListLeft) <= 1);
    assert.ok(Math.abs(stable.afterChatTop - stable.beforeChatTop) <= 1);
    readingChecks.push({ listScrollable: stable.listScrollable, beforeListLeft: stable.beforeListLeft, afterListLeft: stable.afterListLeft,
      beforeChatTop: stable.beforeChatTop, afterChatTop: stable.afterChatTop });
    await screenshot(page, 'stable-focus-and-reading.png');
  });

  await scenario('Cancellation stays immediate, busy in both places and sends only one request while switching views', async h => {
    const { page } = h; await open(h); const before = await prepareDraft(page);
    const run = await createRun(h, 'Cancel once while returning to a draft'); await refresh(h); await openMonitored(page, run.id);
    const seen = deferred(), release = deferred(); h.releases.push(release.resolve);
    h.intercept = async route => {
      if (route.request().method() === 'POST' && new URL(route.request().url()).pathname === `/api/runs/${run.id}/cancel`) {
        seen.resolve(); await release.promise;
      }
      return false;
    };
    const response = page.waitForResponse(response => new URL(response.url()).pathname === `/api/runs/${run.id}/cancel`);
    void response.catch(() => {});
    await page.locator('#stop-research').click(); await seen.promise;
    assert.equal(await page.locator('dialog[open]').count(), 0, 'stopping retains its immediate command behavior');
    assert.equal(await page.locator('#stop-research').isDisabled(), true);
    assert.match(`${await page.locator('#stop-research').getAttribute('aria-label')} ${await page.locator('#stop-research').getAttribute('title')}`, /正在取消/);
    assert.match(await page.locator(row(run.id)).innerText(), /正在取消/);
    await page.locator('#stop-research').evaluate(button => { (button as HTMLButtonElement).click(); (button as HTMLButtonElement).click(); });
    await returnToDraft(page, before); assert.match(await page.locator(row(run.id)).innerText(), /正在取消/);
    await openMonitored(page, run.id); assert.equal(await page.locator('#stop-research').isDisabled(), true);
    assert.equal(count(h, 'POST', `/api/runs/${run.id}/cancel`), 1);
    await screenshot(page, 'cancellation-busy.png'); release.resolve(); assert.equal((await response).status(), 200);
    await page.locator('#stop-research').waitFor({ state: 'hidden' }); await monitorItems(page, []);
    await returnToDraft(page, before);
  }, 1440, 1);

  await scenario('A lost cancel response after GET confirmation cannot report uncertainty, reconnect or replay cancellation', async h => {
    const { page } = h; await open(h); await page.locator('#new-research').click();
    const run = await createRun(h, 'Cancel accepted before its response is lost'); await refresh(h); await openMonitored(page, run.id);
    const accepted = deferred(), release = deferred(); h.releases.push(release.resolve);
    const beforeSessions = count(h, 'GET', '/api/session'), beforeAborts = workerAborts;
    h.intercept = async route => {
      if (route.request().method() !== 'POST' || new URL(route.request().url()).pathname !== `/api/runs/${run.id}/cancel`) return false;
      const response = await route.fetch(); assert.equal(response.status(), 200);
      assert.equal(((await response.json()) as { run: WebRun }).run.status, 'cancelled');
      accepted.resolve(); await release.promise; await route.abort('failed'); return true;
    };
    const confirmed = pollWith(page, run.id, 'cancelled');
    await page.locator('#stop-research').click(); await accepted.promise; await confirmed;
    await page.waitForFunction(() => document.querySelector('.detail-statusline .badge')?.textContent?.includes('已取消'));
    const lost = page.waitForEvent('requestfailed', request => new URL(request.url()).pathname === `/api/runs/${run.id}/cancel`);
    release.resolve(); await lost; await settled(page);
    assert.equal(await page.locator('#global-notice').isVisible(), false);
    assert.equal(await page.locator('#submit-run').isEnabled(), true);
    assert.doesNotMatch(await page.locator('#toast').innerText(), /未确认|尚未确认|连接需要恢复/);
    assert.equal(count(h, 'GET', '/api/session'), beforeSessions, 'an already confirmed cancellation must not reconnect');
    assert.equal(count(h, 'POST', `/api/runs/${run.id}/cancel`), 1);
    assert.equal(workerAborts - beforeAborts, 1); await monitorItems(page, []);
    raceEvidence = { confirmedByGetBeforeLostResponse: true, cancelPosts: 1, extraSessionRequests: 0, workerAborts: 1 };
    await screenshot(page, 'cancel-lost-response-reconciled.png');
  }, 1440, 1);

  for (const width of widths) await scenario(`Monitor navigation and return preserve the draft, Key, backup and filters at ${width}px`, async h => {
    const { page } = h; await open(h); const before = await prepareDraft(page);
    const foreground = await createRun(h, `Active mathematical task ${injection}`), background = await createRun(h, 'Background task completing during draft editing');
    await refresh(h); await monitorItems(page, [foreground.id, background.id]); await preserved(page, before);
    assert.equal(await page.locator('#return-to-draft').isVisible(), false);
    for (const selector of ['#run-monitor', '#run-monitor-summary', '#run-monitor-list']) await fit(page, selector);
    for (const id of [foreground.id, background.id]) {
      await page.locator(opener(id)).evaluate(button => button.scrollIntoView({ inline: 'nearest', block: 'nearest', behavior: 'instant' }));
      await fit(page, opener(id));
    }
    await screenshot(page, `monitor-${width}-draft.png`);
    await openMonitored(page, foreground.id); await preserved(page, before);
    await screenshot(page, `monitor-${width}-active.png`); await returnToDraft(page, before);
    controls.get(background.id)!.finish(); await waitTerminal(h, background.id); await refresh(h);
    await page.locator(dismiss(background.id)).waitFor(); await preserved(page, before);
    await openMonitored(page, background.id, true); await preserved(page, before);
    await monitorItems(page, [foreground.id]); await returnToDraft(page, before);
    await screenshot(page, `monitor-${width}-returned.png`);
  }, width);

  await writeReport('passed');
  console.log(`Run monitor checks passed: ${checks.length} scenarios; live and background task notices, draft return, stable reading and focus, immediate cancellation and delayed-response reconciliation.`);
  console.log(`Report: ${path.relative(root, reportFile)}`);
} catch (error) { await writeReport('failed', error); throw error; }
finally { await browser?.close(); await service.close(); }
