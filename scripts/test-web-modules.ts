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
import type { WebEventDetails, WebModuleId, WebResult, WebRun, WebRunInput } from '../apps/web/shared';
import { closeHistory, openHistory, selectHistoryRun, showArtifacts, showChat } from './web-ui-controls';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const output = path.join(root, 'out/web-modules');
const reportFile = path.join(output, 'report.json');
const credential = `sk-theoremos-module-fixture-${crypto.randomUUID()}`;
const markup = '<img data-module-injection src=x onerror="window.__moduleInjected=true">';
const source = 'theorem module_fixture : True := by sorry\n';
const moduleIds: WebModuleId[] = ['M1', 'M2', 'M3', 'M4', 'M5', 'S3'];
const widths = [1440, 1024, 375, 320];
await fs.access(path.join(root, 'out/web/app.js')).catch(() => { throw new Error('Run bun run build:web before the module check.'); });
await fs.mkdir(output, { recursive: true });
await fs.rm(reportFile, { force: true });
const probe = net.createServer();
await new Promise<void>(resolve => probe.listen(0, '127.0.0.1', resolve));
const port = (probe.address() as net.AddressInfo).port;
await new Promise<void>((resolve, reject) => probe.close(error => error ? reject(error) : resolve()));
const origin = `http://127.0.0.1:${port}`;
const result = (status = 'incomplete'): WebResult => ({ status, proof: source.replace('sorry', 'trivial'), report: { status, fixture: true } });
type Control = {
  progress(type: string, message: string, details?: WebEventDetails): void;
  emit(value: WebResult): void;
  finish(value?: WebResult): void;
  fail(): void;
};
const controls = new Map<string, Control>();
let workerStarts = 0;
const runner: WebRunner = {
  async readiness() { return { ready: true, message: 'Local module visualization fixture' }; },
  async run(input, send, signal) {
    workerStarts++;
    await new Promise<void>((resolve, reject) => {
      const cleanup = () => { controls.delete(input.id); signal.removeEventListener('abort', abort); };
      const abort = () => { cleanup(); reject(new Error('Cancelled module fixture')); };
      signal.addEventListener('abort', abort, { once: true });
      controls.set(input.id, {
        progress: (event, message, details) => send({ type: 'progress', event, message, ...(details ? { details } : {}) }),
        emit: value => send({ type: 'result', result: value }),
        finish: (value = result()) => { send({ type: 'result', result: value }); cleanup(); resolve(); },
        fail: () => { cleanup(); reject(new Error('Local fixture runtime failure')); },
      });
      if (signal.aborted) abort();
    });
  },
};
const service = createWebService(readWebConfig({ THEOREMOS_WEB_PORT: String(port), THEOREMOS_WEB_PUBLIC_URL: origin,
  THEOREMOS_WEB_STATIC_ROOT: path.join(root, 'out/web'), THEOREMOS_WEB_CONCURRENCY: '8' }), runner);
type RequestRecord = { method: string; pathname: string };
type Harness = { page: Page; context: BrowserContext; requests: RequestRecord[]; runIds: string[]; fixtureCancels: number };
const checks: Array<{ name: string; elapsedMs: number; fixtureCreates: number; fixtureCancels: number;
  featureApiWrites: number; requests: RequestRecord[] }> = [];
const screenshots: string[] = [];
const retainedSummaries: Array<{ runId: string; retainedEvents: number; contextEvents: number; constructionEvents: number }> = [];
let browser: Awaited<ReturnType<typeof chromium.launch>> | undefined;
let failedScenario = '', failureScreenshot = '';

async function settled(page: Page) {
  await page.evaluate(() => new Promise<void>(resolve => requestAnimationFrame(() => requestAnimationFrame(() => resolve()))));
}
async function scenario(name: string, run: (h: Harness) => Promise<void>, width = 1440) {
  failedScenario = name;
  const started = performance.now();
  const context = await browser!.newContext({ viewport: { width, height: width > 850 ? 900 : 812 }, reducedMotion: 'reduce' });
  const page = await context.newPage();
  page.setDefaultTimeout(10_000);
  const h: Harness = { page, context, requests: [], runIds: [], fixtureCancels: 0 };
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
    await page.goto(origin); await page.locator('#submit-run:enabled').waitFor();
    const draft = await page.locator('#source').inputValue(), task = await page.locator('#task').inputValue();
    await Promise.race([run(h), new Promise<never>((_, reject) => {
      deadline = setTimeout(() => reject(new Error(`Module scenario exceeded 50 seconds: ${name}`)), 50_000);
    })]);
    assert.deepEqual(errors, [], 'uncaught browser errors');
    assert.deepEqual(external, [], 'module inspection must not contact external sites or model providers');
    assert.equal(await page.locator('#source').inputValue(), draft, 'module inspection must preserve the draft source');
    assert.equal(await page.locator('#task').inputValue(), task, 'module inspection must preserve the draft task');
    assert.equal(await page.locator('#api-key').inputValue(), '', 'module inspection must not populate a credential');
    const writes = h.requests.filter(request => request.method !== 'GET');
    assert.equal(writes.length, h.runIds.length, 'only explicit fixture creation may write to the API');
    assert.ok(writes.every(request => request.method === 'POST' && request.pathname === '/api/runs'));
    checks.push({ name, elapsedMs: Math.round(performance.now() - started), fixtureCreates: h.runIds.length,
      fixtureCancels: h.fixtureCancels, featureApiWrites: writes.length - h.runIds.length, requests: h.requests });
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
async function createRun(h: Harness, title = 'Inspect local research modules', workers = 1) {
  const input: WebRunInput = { providerId: 'openai', apiKey: credential, model: 'fixture-module-model', effort: 'low',
    environment: 'standard', source, task: title, maxTurns: 2, maxRunSeconds: 60, workers,
    coordination: workers > 1 ? 'cooperative' : 'independent' };
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
async function selectModules(h: Harness, id: string) {
  await openHistory(h.page); await h.page.locator('#refresh-runs:enabled').waitFor();
  const refreshed = h.page.waitForResponse(response => new URL(response.url()).pathname === '/api/runs' && response.request().method() === 'GET');
  await h.page.locator('#refresh-runs').click(); await refreshed;
  await h.page.locator('#refresh-runs:enabled').waitFor(); await closeHistory(h.page);
  await selectHistoryRun(h.page, id); await showArtifacts(h.page);
  await h.page.locator('#detail-tab-modules').click(); await h.page.locator('.module-workspace').waitFor();
}
async function pollSnapshot(page: Page, id: string, expected: { sequence?: number; status?: WebRun['status']; result?: string } = {}) {
  const observed = page.waitForResponse(async response => {
    if (new URL(response.url()).pathname !== '/api/runs' || response.request().method() !== 'GET' || response.status() !== 200) return false;
    const payload = await response.json() as { runs: WebRun[] }, run = payload.runs.find(run => run.id === id);
    return Boolean(run && (expected.sequence === undefined || (run.events.at(-1)?.sequence ?? 0) >= expected.sequence)
      && (expected.status === undefined || run.status === expected.status) && (expected.result === undefined || run.result?.status === expected.result));
  });
  await page.evaluate(() => document.dispatchEvent(new Event('visibilitychange')));
  await observed; await settled(page);
}
async function sync(h: Harness, id: string) {
  const run = await readRun(h, id);
  await pollSnapshot(h.page, id, { sequence: run.events.at(-1)?.sequence, status: run.status, ...(run.result ? { result: run.result.status } : {}) });
  return run;
}
async function selectModule(page: Page, id: WebModuleId) {
  await page.locator(`[data-module-id="${id}"]`).click();
  await page.locator(`#module-inspector[data-module="${id}"]`).waitFor();
  assert.equal(await page.locator(`[data-module-id="${id}"]`).getAttribute('aria-pressed'), 'true');
  assert.equal(await page.locator('.module-node[aria-pressed="true"]').count(), 1);
}
async function state(page: Page, id: WebModuleId, tone: string, label?: string) {
  await page.locator(`[data-module-id="${id}"][data-tone="${tone}"]`).waitFor();
  if (label !== undefined) await page.waitForFunction(({ id, label }) =>
    document.querySelector(`[data-module-id="${id}"] [data-module-state]`)?.textContent === label, { id, label });
}
async function facts(page: Page) {
  return page.locator('.module-facts').evaluate(list => Object.fromEntries(Array.from(list.children)
    .map(row => [row.querySelector('dt')!.textContent, row.querySelector('dd')!.textContent])) as Record<string, string>);
}
async function noInjection(page: Page) {
  assert.equal(await page.locator('[data-module-injection]').count(), 0, 'module messages and summaries must remain inert text');
  assert.equal(await page.evaluate(() => (window as unknown as { __moduleInjected?: boolean }).__moduleInjected), undefined);
  assert.equal((await page.locator('.module-workspace').innerText()).includes(credential), false, 'module views must preserve server credential redaction');
}
async function screenshot(page: Page, name: string) {
  await page.screenshot({ path: path.join(output, name) }); screenshots.push(name);
}
async function horizontalFit(page: Page, selector: string) {
  const boxes = await page.locator(selector).evaluateAll(elements => elements.map(element => {
    const box = element.getBoundingClientRect(); return { x: box.x, right: box.right, width: box.width };
  }));
  assert.ok(boxes.length, `${selector} must exist`);
  for (const box of boxes) assert.ok(box.x >= -1 && box.width > 0 && box.right <= page.viewportSize()!.width + 1,
    `${selector} must fit ${page.viewportSize()!.width}px: ${JSON.stringify(box)}`);
  assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth + 1), true, 'module tools must not widen the document');
}
async function graphReadability(page: Page) {
  const failures = await page.locator('.module-node').evaluateAll(nodes => {
    const luminance = (color: string) => {
      const channels = color.match(/[\d.]+/g)!.slice(0, 3).map(Number).map(value => value / 255)
        .map(value => value <= .04045 ? value / 12.92 : ((value + .055) / 1.055) ** 2.4);
      return channels[0]! * .2126 + channels[1]! * .7152 + channels[2]! * .0722;
    };
    return nodes.flatMap(node => {
      const background = luminance(getComputedStyle(node).backgroundColor);
      return Array.from(node.querySelectorAll('.module-code,.module-node-name,.module-node-subject,[data-module-state]')).flatMap(label => {
        const foreground = luminance(getComputedStyle(label).color);
        const ratio = (Math.max(background, foreground) + .05) / (Math.min(background, foreground) + .05);
        return ratio < 4.5 ? [{ label: label.textContent, ratio }] : [];
      });
    });
  });
  assert.deepEqual(failures, [], 'small node labels must retain 4.5:1 contrast in selected and activity states');
  assert.equal(await page.locator('.module-node-selected:visible').count(), 1, 'selection must also have a visible text and icon cue');
  assert.equal(await page.locator('.module-node[aria-pressed="true"] .module-node-selected').isVisible(), true);
  assert.ok(await page.locator('.module-node[aria-current="true"]').count() <= 1, 'at most one module can carry the latest-record marker');
  assert.equal(await page.locator('.module-node[data-recent="true"]').count(), await page.locator('.module-node[aria-current="true"]').count(),
    'the latest-record marker must have both visual and accessible state');
  if (await page.locator('.module-node[aria-current="true"]').count()) {
    const marker = await page.locator('.module-node[aria-current="true"]').evaluate(node => getComputedStyle(node).boxShadow);
    assert.match(marker, /3px 0px 0px 0px inset/, 'latest records must have a visible inset marker');
    assert.match(await page.locator('.module-node[aria-current="true"]').getAttribute('title') ?? '', /最新模块记录/);
  }
  const selectedMarkerOverlap = await page.locator('.module-node[aria-pressed="true"]').evaluate(node => {
    const outer = node.getBoundingClientRect();
    const marker = node.querySelector<HTMLElement>('.module-node-selected')!.getBoundingClientRect();
    const code = node.querySelector<HTMLElement>('.module-code')!.getBoundingClientRect();
    return marker.left < code.right && marker.right > code.left || marker.left < outer.left || marker.right > outer.right;
  });
  assert.equal(selectedMarkerOverlap, false, 'selection marker must stay inside the card without colliding with its module code');
  const cycleLabelClipped = await page.locator('.module-cycle-label').evaluate(label => {
    const labelBox = label.getBoundingClientRect(), graphBox = label.closest('.module-research')!.getBoundingClientRect();
    return labelBox.left < graphBox.left || labelBox.right > graphBox.right || labelBox.top < graphBox.top || labelBox.bottom > graphBox.bottom;
  });
  assert.equal(cycleLabelClipped, false, 'research-cycle label must stay inside its highlighted region');
  const disconnected = await page.locator('.module-cycle .module-edge').evaluateAll(edges => edges.flatMap(edge => {
    const { from, to, direction } = (edge as HTMLElement).dataset;
    const source = document.querySelector(`[data-module-id="${from}"]`)!.getBoundingClientRect(),
      target = document.querySelector(`[data-module-id="${to}"]`)!.getBoundingClientRect(), line = edge.getBoundingClientRect();
    const gaps = direction === 'right' ? [line.left - source.right, target.left - line.right]
      : direction === 'left' ? [line.left - target.right, source.left - line.right]
      : direction === 'down' ? [line.top - source.bottom, target.top - line.bottom]
      : [line.top - target.bottom, source.top - line.bottom];
    return gaps.some(gap => Math.abs(gap) > 1.5) ? [{ from, to, gaps }] : [];
  }));
  assert.deepEqual(disconnected, [], 'cycle connectors must join the cards at every workspace width');
}
async function writeReport(status: 'passed' | 'failed', error?: unknown) {
  const report = { status, checkedAt: new Date().toISOString(),
    mode: 'Real local HTTP service and Chromium with a controlled in-process runner. No models, Docker, Lean or external requests.',
    paidModelCalls: false, workerStarts, widths, checks, retainedSummaries, screenshots,
    ...(error ? { failedScenario, error: error instanceof Error ? error.message : String(error), failureScreenshot } : {}) };
  assert.equal(JSON.stringify(report).includes(credential), false);
  await fs.writeFile(reportFile, JSON.stringify(report, null, 2) + '\n');
}

try {
  await new Promise<void>((resolve, reject) => { service.server.once('error', reject); service.server.listen(port, '127.0.0.1', resolve); });
  browser = await chromium.launch({ headless: true });

  await scenario('Draft modules support selection and keyboard navigation without starting a run', async ({ page }) => {
    await page.locator('#draft-tab-source').focus(); await page.keyboard.press('ArrowRight');
    await page.locator('#draft-tab-modules[aria-selected="true"]').waitFor();
    assert.equal(await page.locator('#draft-tab-modules').evaluate(element => document.activeElement === element), true);
    assert.equal(await page.locator('.module-node').count(), moduleIds.length);
    assert.equal(await page.locator('.module-observation').innerText(), '未提交');
    assert.equal(await page.locator('.module-live').isVisible(), false);
    for (const id of moduleIds) {
      await state(page, id, 'pending', '未运行'); await selectModule(page, id);
      assert.equal((await facts(page))['活动事件'], '0');
      assert.equal(await page.locator('.module-events li').count(), 0);
      assert.equal(await page.locator('.module-events-empty').isVisible(), true);
      assert.equal(await page.locator('[data-module-destination="events"]').isVisible(), false);
    }
    await graphReadability(page);
    assert.equal(await page.locator('.module-edge[data-selected="true"]').count(), 1);
    assert.equal(await page.locator('.module-edge[data-selected="true"]').getAttribute('data-to'), 'S3', 'draft links describe structure without implying execution');
    await screenshot(page, 'draft-modules-1440.png');
    await page.locator('[data-module-destination="source"]').click();
    await page.locator('#draft-tab-source[aria-selected="true"]').waitFor();
    assert.equal(await page.locator('#draft-tab-source').evaluate(element => document.activeElement === element), true);
    await page.keyboard.press('End'); await page.locator('#draft-tab-modules[aria-selected="true"]').waitFor();
    await page.keyboard.press('Home'); await page.locator('#draft-tab-source[aria-selected="true"]').waitFor();
  });

  await scenario('Structured research events populate the correct modules and local detail destinations', async h => {
    const { page } = h, run = await createRun(h, 'Structured module details', 2), control = controls.get(run.id)!;
    control.progress('solve_started', 'Research started');
    control.progress('context_compiled', 'Selected problem and retained research evidence', { workerId: 'worker1', turn: 1, usedBytes: 2048, maxBytes: 8192 });
    control.progress('research_action', 'Choose a decomposition', { workerId: 'worker1', turn: 1, operation: 'decompose' });
    control.progress('task_assigned', 'Assign helper theorem to Researcher', { workerId: 'worker1', taskId: 'helper1', role: 'researcher' });
    control.progress('turn_started', 'Start proof construction', { workerId: 'worker1', turn: 1 });
    control.progress('worker_activity', 'Constructing a local candidate', { workerId: 'worker1', turn: 1 });
    await selectModules(h, run.id);
    for (const id of ['M3', 'M4', 'M5'] as const) await state(page, id, 'observed');
    await state(page, 'M1', 'active'); await state(page, 'M2', 'pending'); await state(page, 'S3', 'pending');
    await selectModule(page, 'M4');
    assert.equal((await facts(page))['上下文大小'], '2.0 KB / 8.0 KB');
    assert.equal((await facts(page))['最近 Agent'], 'worker1'); assert.equal((await facts(page))['最近轮次'], '1');
    await selectModule(page, 'M3'); assert.equal((await facts(page))['最近决策'], '分解任务');
    await selectModule(page, 'M5'); assert.equal((await facts(page))['Agent 配置'], '2');
    assert.equal((await facts(page))['运行模式'], '任务协作');
    const snapshot = await readRun(h, run.id), sequence = snapshot.modules!.M5!.lastEvent.sequence;
    assert.equal(await page.locator(`.module-events li[data-sequence="${sequence}"] p`).innerText(), 'Assign helper theorem to Researcher');
    await page.locator('[data-module-destination="events"]').click(); await page.locator('.activity-workspace').waitFor();
    await page.locator('#detail-tab-modules').click();
    await selectModule(page, 'M1'); await page.locator('[data-module-destination="source"]').click();
    await page.locator('#detail-tab-source[aria-selected="true"]').waitFor();
    await page.locator('#detail-tab-modules').click(); await selectModule(page, 'S3');
    await page.locator('[data-module-destination="report"]').click(); await page.locator('#detail-tab-report[aria-selected="true"]').waitFor();
    await page.locator('#detail-tab-source').click(); await page.keyboard.press('ArrowRight');
    await page.locator('#detail-tab-modules[aria-selected="true"]').waitFor();
    assert.equal(await page.locator('#detail-tab-modules').evaluate(element => document.activeElement === element), true);
    await page.keyboard.press('ArrowRight'); await page.locator('#detail-tab-overview[aria-selected="true"]').waitFor();
    await page.keyboard.press('ArrowLeft'); await page.locator('#detail-tab-modules[aria-selected="true"]').waitFor();
    await page.keyboard.press('End'); await page.locator('#detail-tab-events[aria-selected="true"]').waitFor();
    await page.keyboard.press('Home'); await page.locator('#detail-tab-source[aria-selected="true"]').waitFor();
  });

  await scenario('Latest module activity can be followed, paused, located and reset across runs', async h => {
    const { page } = h, run = await createRun(h, 'Follow actual module activity'), control = controls.get(run.id)!;
    await selectModules(h, run.id);
    const follow = page.locator('[data-module-follow]');
    assert.equal(await follow.isChecked(), false);
    assert.equal(await page.locator('[data-module-latest]').isDisabled(), true);
    assert.equal(await page.locator('[data-module-live-message]').innerText(), '等待模块活动');
    await follow.focus(); await page.keyboard.press('Space');
    assert.equal(await follow.isChecked(), true);
    control.progress('solve_started', 'Research started');
    control.progress('context_compiled', 'Latest context evidence', { workerId: 'worker1', usedBytes: 1024 });
    await sync(h, run.id); await page.locator('#module-inspector[data-module="M4"]').waitFor();
    assert.equal(await follow.evaluate(element => document.activeElement === element), true, 'following must retain checkbox focus');
    assert.equal(await page.locator('[data-module-live-name]').innerText(), 'M4 · 上下文选择');
    await selectModule(page, 'M4'); assert.equal(await follow.isChecked(), false, 'selecting the current module must also pause following');
    control.progress('turn_started', 'A new candidate starts', { workerId: 'worker1', turn: 1 });
    await sync(h, run.id); await page.locator('#module-inspector[data-module="M4"]').waitFor();
    assert.equal(await page.locator('[data-module-live-name]').innerText(), 'M1 · 证明构造');
    await page.locator('[data-module-latest]').click(); await page.locator('#module-inspector[data-module="M1"]').waitFor();
    assert.equal(await follow.isChecked(), false, 'locating an event is a single navigation');
    await follow.check();
    await page.locator('#detail-tab-source').click();
    control.progress('proof_check_started', 'Check the latest candidate', { workerId: 'worker1', turn: 1 });
    await sync(h, run.id);
    await page.locator('#detail-tab-modules').click(); await page.locator('#module-inspector[data-module="M2"]').waitFor();
    assert.equal(await follow.isChecked(), true, 'returning to the same run must retain follow mode');
    const other = await createRun(h, 'A different module run');
    controls.get(other.id)!.progress('context_compiled', 'Another run context');
    await sync(h, other.id); await selectHistoryRun(page, other.id); await selectHistoryRun(page, run.id);
    await page.locator('#detail-tab-modules').click(); await page.locator('#module-inspector[data-module="M1"]').waitFor();
    assert.equal(await follow.isChecked(), false, 'visiting another run source must also reset following');
    await selectModules(h, other.id); await page.locator('#module-inspector[data-module="M1"]').waitFor();
    assert.equal(await follow.isChecked(), false, 'changing run must reset following');
    await follow.check(); await page.locator('#module-inspector[data-module="M4"]').waitFor();
    controls.get(other.id)!.finish(); await pollSnapshot(page, other.id, { status: 'completed' });
    assert.equal(await follow.isChecked(), false); assert.equal(await follow.isDisabled(), true);
    assert.equal(await page.locator('[data-module-live-name]').innerText(), 'M4 · 上下文选择', 'terminal events are not module events');
    await page.locator('[data-module-latest]').click(); await page.locator('#module-inspector[data-module="M4"]').waitFor();
  });

  await scenario('Mobile follow updates retain focus and scroll and resume after a connection interruption', async h => {
    const { page, context } = h, run = await createRun(h, 'Observe live modules on mobile'), control = controls.get(run.id)!;
    control.progress('solve_started', 'Research started');
    control.progress('context_compiled', 'Context before construction', { workerId: 'worker1' });
    await selectModules(h, run.id); await page.locator('[data-module-follow]').check();
    await page.locator('#module-inspector[data-module="M4"]').waitFor();
    await page.evaluate(() => {
      const workspace = document.querySelector('.module-workspace')!, node = document.querySelector('[data-module-id="M4"]')!,
        follow = document.querySelector<HTMLInputElement>('[data-module-follow]')!, panel = document.querySelector('#detail-panel')!;
      follow.focus({ preventScroll: true }); panel.scrollTop = 160;
      const title = node.querySelector('.module-node-name')!.firstChild!, range = document.createRange();
      range.selectNodeContents(title); getSelection()!.removeAllRanges(); getSelection()!.addRange(range);
      (window as unknown as { __moduleFollowing: unknown }).__moduleFollowing = { workspace, node, follow, scrollTop: panel.scrollTop };
    });
    control.progress('turn_started', 'Construct after context', { workerId: 'worker1', turn: 1 });
    await sync(h, run.id); await page.locator('#module-inspector[data-module="M1"]').waitFor();
    const stable = await page.evaluate(() => {
      const before = (window as unknown as { __moduleFollowing: { workspace: Element; node: Element; follow: Element; scrollTop: number } }).__moduleFollowing;
      return { workspace: before.workspace === document.querySelector('.module-workspace'), node: before.node === document.querySelector('[data-module-id="M4"]'),
        focused: document.activeElement === before.follow, selection: getSelection()!.toString(),
        scrollTop: document.querySelector('#detail-panel')!.scrollTop, beforeScrollTop: before.scrollTop };
    });
    assert.equal(stable.workspace, true); assert.equal(stable.node, true); assert.equal(stable.focused, true);
    assert.equal(stable.selection, '上下文选择'); assert.ok(stable.beforeScrollTop > 0);
    assert.ok(Math.abs(stable.scrollTop - stable.beforeScrollTop) <= 1.5, 'automatic follow must not scroll the stacked graph');
    let offline = true;
    await context.route('**/api/**', async route => offline ? route.abort('failed') : route.fallback());
    await page.evaluate(() => document.dispatchEvent(new Event('visibilitychange')));
    await page.locator('.module-workspace[data-stale="true"]').waitFor();
    assert.equal(await page.locator('[data-module-follow]').isChecked(), true);
    control.progress('proof_check_started', 'Check during connection interruption', { workerId: 'worker1', turn: 1 });
    await page.locator('#module-inspector[data-module="M1"]').waitFor();
    offline = false; await sync(h, run.id); await page.locator('.module-workspace[data-stale="false"]').waitFor();
    await page.locator('#module-inspector[data-module="M2"]').waitFor();
    await showChat(page);
    control.progress('context_compiled', 'Context while viewing conversation', { workerId: 'worker1' });
    await sync(h, run.id); await showArtifacts(page);
    await page.locator('#module-inspector[data-module="M4"]').waitFor();
    assert.equal(await page.locator('[data-module-follow]').isChecked(), true);
    await page.locator('[data-module-follow]').uncheck();
    control.progress('research_action', 'Choose another route', { operation: 'direct' });
    await sync(h, run.id); await page.locator('#module-inspector[data-module="M4"]').waitFor();
    await page.locator('[data-module-latest]').click(); await page.locator('#module-inspector[data-module="M3"]').waitFor();
    assert.equal(await page.locator('#module-inspector').evaluate(element => document.activeElement === element), true, 'explicit latest navigation must focus the stacked inspector');
    await page.locator('[data-module-return]').click();
    assert.equal(await page.locator('[data-module-id="M3"]').evaluate(element => document.activeElement === element), true);
    await screenshot(page, 'modules-live-follow-375.png');
  }, 375);

  await scenario('Conditional and complete candidate checks never imply independent acceptance', async h => {
    const { page } = h, run = await createRun(h), control = controls.get(run.id)!;
    control.progress('solve_started', 'Research started');
    control.progress('proof_check_started', 'Check a helper candidate', { workerId: 'worker1', turn: 1 });
    await selectModules(h, run.id); await state(page, 'M2', 'active', '检查中');
    control.progress('proof_checked', 'Conditional helper check passed', { workerId: 'worker1', turn: 1, passed: true, conditional: true });
    await sync(h, run.id); await state(page, 'M2', 'observed', '条件性通过'); await state(page, 'S3', 'pending');
    control.progress('lemma_checked', 'The next helper requires repair', { workerId: 'worker1', passed: false, conditional: true });
    await sync(h, run.id); await state(page, 'M2', 'feedback', '待修复');
    control.progress('task_checked', 'A local task passed its check', { workerId: 'worker1', taskId: 'helper1', passed: true });
    await sync(h, run.id); await state(page, 'M2', 'observed', '局部通过'); await state(page, 'S3', 'pending');
    control.progress('proof_checked', 'Complete candidate check passed', { workerId: 'worker1', passed: true, conditional: false });
    await sync(h, run.id); await state(page, 'M2', 'observed', '候选通过'); await state(page, 'S3', 'pending');
    await selectModule(page, 'M2'); assert.match(await page.locator('.module-verification-note').innerText(), /不代表完整原题验收通过/);
    assert.equal(await page.locator('.module-node[data-tone="passed"]').count(), 0);
  });

  await scenario('S3 waits for a completed accepted result even after a passed evaluation event or early result', async h => {
    const { page } = h, run = await createRun(h), control = controls.get(run.id)!;
    control.progress('evaluation_started', 'Independent acceptance started', { workerId: 'worker1' });
    await selectModules(h, run.id); await state(page, 'S3', 'active', '独立验收中');
    control.progress('evaluation_finished', 'Evaluation reported evaluated_passed', { status: 'evaluated_passed', passed: true });
    await sync(h, run.id); await state(page, 'S3', 'observed', '等待结果确认');
    control.emit(result('evaluated_passed'));
    const pending = await sync(h, run.id); assert.equal(pending.status, 'running');
    await state(page, 'S3', 'observed', '等待结果确认');
    assert.equal(await page.locator('.module-node[data-tone="passed"]').count(), 0);
    control.finish(result('evaluated_passed'));
    await pollSnapshot(page, run.id, { status: 'completed', result: 'evaluated_passed' });
    await state(page, 'S3', 'passed', '验收通过'); await selectModule(page, 'S3');
    await screenshot(page, 'independent-acceptance-passed.png');
  });

  await scenario('Failed, rejected, incomplete, cancelled and runtime-error runs cannot become accepted', async h => {
    for (const status of ['evaluated_failed', 'evaluated_rejected', 'incomplete', 'cancelled', 'runtime_error']) {
      const run = await createRun(h, `Terminal module state ${status}`), control = controls.get(run.id)!;
      control.progress('evaluation_started', 'Independent acceptance started');
      if (status === 'cancelled') {
        const owner = (await h.context.cookies(origin)).find(cookie => cookie.name === 'theoremos_session')!.value;
        assert.equal(service.jobs.cancel(owner, run.id)?.status, 'cancelled'); h.fixtureCancels++;
      } else control.finish(result(status));
      await selectModules(h, run.id);
      assert.notEqual(await h.page.locator('[data-module-id="S3"]').getAttribute('data-tone'), 'passed');
      if (status.startsWith('evaluated_')) await state(h.page, 'S3', 'failed', status === 'evaluated_rejected' ? '验收拒绝' : '验收未通过');
      if (status === 'cancelled' || status === 'runtime_error') await state(h.page, 'S3', 'stopped', '验收已中断');
      const snapshot = await readRun(h, run.id);
      assert.equal(snapshot.status, status === 'cancelled' ? 'cancelled' : status === 'runtime_error' ? 'error' : 'completed');
    }
  });

  await scenario('A checkpoint or proof result from one worker preserves another worker active module', async h => {
    const { page } = h, run = await createRun(h, 'Parallel module workers', 2), control = controls.get(run.id)!;
    control.progress('solve_started', 'Research started');
    control.progress('turn_started', 'Worker one started', { workerId: 'worker1', turn: 1 });
    control.progress('turn_started', 'Worker two started', { workerId: 'worker2', turn: 1 });
    await selectModules(h, run.id); await state(page, 'M1', 'active');
    assert.deepEqual(await page.locator('.module-workers code').allTextContents(), ['worker1', 'worker2']);
    assert.equal(await page.locator('[data-module-worker-count]').innerText(), '2');
    control.progress('turn_checkpoint', 'Only worker one checkpointed', { workerId: 'worker1', turn: 1 });
    let snapshot = await sync(h, run.id); assert.deepEqual(snapshot.modules!.M1!.activeWorkers, ['worker2']);
    assert.deepEqual(await page.locator('.module-workers code').allTextContents(), ['worker2']);
    await state(page, 'M1', 'active');
    control.progress('proof_check_started', 'Worker two checks its candidate', { workerId: 'worker2', turn: 1 });
    await sync(h, run.id); await state(page, 'M1', 'observed'); await state(page, 'M2', 'active');
    assert.equal(await page.locator('.module-workers').isVisible(), false);
    await selectModule(page, 'M2'); assert.deepEqual(await page.locator('.module-workers code').allTextContents(), ['worker2']);
    control.progress('turn_started', 'Worker one starts another turn', { workerId: 'worker1', turn: 2 });
    control.progress('proof_checked', 'Worker two candidate passed', { workerId: 'worker2', passed: true });
    snapshot = await sync(h, run.id); assert.deepEqual(snapshot.modules!.M1!.activeWorkers, ['worker1']);
    await state(page, 'M1', 'active'); await state(page, 'M2', 'observed'); await state(page, 'S3', 'pending');
    assert.equal(await page.locator('.module-workers').isVisible(), false);
    await selectModule(page, 'M1'); assert.deepEqual(await page.locator('.module-workers code').allTextContents(), ['worker1']);
    control.progress('evaluation_started', 'Independent acceptance closes research intervals');
    await sync(h, run.id); assert.equal(await page.locator('.module-workers').isVisible(), false);
    control.finish(result('evaluated_failed')); await pollSnapshot(page, run.id, { status: 'completed' });
    assert.equal(await page.locator('.module-workers').isVisible(), false);
  });

  await scenario('Rotated event logs retain module counts and inert redacted summary evidence after reload', async h => {
    const { page } = h, run = await createRun(h), control = controls.get(run.id)!;
    control.progress('solve_started', 'Research started');
    const diagnostic = `Context ${markup}\nCredential ${credential}\n<&> "quoted"`;
    control.progress('context_compiled', diagnostic, { workerId: 'worker1', usedBytes: 1024, maxBytes: 8192 });
    for (let index = 0; index < 25; index++) control.progress('worker_activity', index === 24 ? diagnostic : `Construction evidence ${index + 1}`, { workerId: 'worker1' });
    await selectModules(h, run.id); await selectModule(page, 'M4');
    assert.match(await page.locator('.module-events p').innerText(), /\[REDACTED\]/); await noInjection(page);
    for (let index = 0; index < 210; index++) control.progress('diagnostic', `Unrelated bounded log ${index + 1}`);
    const snapshot = await sync(h, run.id);
    assert.equal(snapshot.events.length, 200); assert.ok(snapshot.events[0]!.sequence > 1);
    assert.equal(snapshot.events.some(event => event.type === 'context_compiled'), false);
    assert.equal(JSON.stringify(snapshot).includes(credential), false);
    assert.equal(snapshot.modules!.M4!.eventCount, 1); assert.equal(snapshot.modules!.M1!.eventCount, 25);
    assert.equal((await facts(page))['活动事件'], '1');
    assert.equal(await page.locator('.module-events li').count(), 0);
    assert.equal(await page.locator('.module-events-empty').innerText(), diagnostic.replaceAll(credential, '[REDACTED]'));
    assert.match(await page.locator('.module-retention').innerText(), /较早活动已移出保留范围/); await noInjection(page);
    await page.reload(); await page.locator('#submit-run:enabled').waitFor(); await selectModules(h, run.id);
    await selectModule(page, 'M4'); assert.equal((await facts(page))['活动事件'], '1');
    assert.equal((await facts(page))['上下文大小'], '1.0 KB / 8.0 KB'); await noInjection(page);
    await selectModule(page, 'M1'); assert.equal((await facts(page))['活动事件'], '25'); await state(page, 'M1', 'active');
    assert.equal(await page.locator('[data-module-live-message]').textContent(), diagnostic.replaceAll(credential, '[REDACTED]'));
    await selectModule(page, 'M4'); await page.locator('[data-module-latest]').click();
    await page.locator('#module-inspector[data-module="M1"]').waitFor();
    await page.locator('[data-module-follow]').check(); await page.locator('#module-inspector[data-module="M1"]').waitFor();
    await noInjection(page);
    retainedSummaries.push({ runId: run.id, retainedEvents: snapshot.events.length,
      contextEvents: snapshot.modules!.M4!.eventCount, constructionEvents: snapshot.modules!.M1!.eventCount });
    await screenshot(page, 'rotated-module-summary.png');
  });

  await scenario('Unchanged and unrelated polling preserves module nodes, focus, text selection and reading position', async h => {
    const { page } = h, run = await createRun(h), control = controls.get(run.id)!;
    control.progress('solve_started', 'Research started');
    for (let index = 0; index < 6; index++) control.progress('context_compiled', `module reading ${index + 1}\n${'Retained context evidence\n'.repeat(8)}`, { workerId: 'worker1', usedBytes: 1024 + index });
    await selectModules(h, run.id); await selectModule(page, 'M4');
    await page.locator('.module-events li').first().waitFor();
    await page.evaluate(() => {
      const workspace = document.querySelector('.module-workspace')!, node = document.querySelector('[data-module-id="M4"]')!,
        row = document.querySelector('.module-events li')!, panel = document.querySelector('#detail-panel')!, text = row.querySelector('p')!.firstChild!;
      (node as HTMLElement).focus({ preventScroll: true });
      const range = document.createRange(); range.setStart(text, 0); range.setEnd(text, 6);
      getSelection()!.removeAllRanges(); getSelection()!.addRange(range);
      panel.scrollTop = 180;
      (window as unknown as { __moduleReading: unknown }).__moduleReading = { workspace, node, row,
        scrollTop: panel.scrollTop, selection: getSelection()!.toString() };
    });
    for (const changed of [false, true]) {
      if (changed) control.progress('diagnostic', 'An unrelated event updates the run');
      await sync(h, run.id);
      const stable = await page.evaluate(() => {
        const before = (window as unknown as { __moduleReading: { workspace: Element; node: Element; row: Element; scrollTop: number; selection: string } }).__moduleReading;
        const panel = document.querySelector('#detail-panel')!;
        return { workspace: before.workspace === document.querySelector('.module-workspace'), node: before.node === document.querySelector('[data-module-id="M4"]'),
          row: before.row === document.querySelector('.module-events li'), focused: document.activeElement === before.node,
          selection: getSelection()!.toString(), beforeSelection: before.selection, scrollTop: panel.scrollTop, beforeScrollTop: before.scrollTop };
      });
      assert.equal(stable.workspace, true); assert.equal(stable.node, true); assert.equal(stable.row, true); assert.equal(stable.focused, true);
      assert.equal(stable.selection, 'module'); assert.equal(stable.beforeSelection, 'module');
      assert.ok(stable.beforeScrollTop > 0, 'the module fixture must have a real reading position');
      assert.ok(Math.abs(stable.scrollTop - stable.beforeScrollTop) <= 1.5, 'polling must preserve module scroll position');
    }
    const before = await page.locator('#detail-panel').evaluate(panel => panel.scrollTop);
    await page.locator('#detail-tab-source').click(); await page.locator('#detail-tab-modules').click();
    await page.locator('#module-inspector[data-module="M4"]').waitFor();
    assert.ok(Math.abs(await page.locator('#detail-panel').evaluate(panel => panel.scrollTop) - before) <= 1.5, 'returning to the module tab must preserve its reading position');
  });

  for (const width of widths) await scenario(`Module graph and inspector fit and keep their selection at ${width}px`, async h => {
    const { page } = h, run = await createRun(h, 'Responsive module workspace', 2), control = controls.get(run.id)!;
    control.progress('solve_started', 'Research started');
    control.progress('task_assigned', 'Assign a helper theorem', { workerId: 'worker1', taskId: 'helper1', role: 'researcher' });
    control.progress('research_action', 'Select a direct route', { workerId: 'worker1', operation: 'direct' });
    control.progress('context_compiled', 'Selected problem and retained evidence', { workerId: 'worker1', usedBytes: 2048, maxBytes: 8192 });
    control.progress('turn_started', 'Construct the candidate proof', { workerId: 'worker1', turn: 1 });
    control.progress('proof_check_started', 'Another Agent checks a helper', { workerId: 'worker2', turn: 1 });
    await selectModules(h, run.id); await state(page, 'M1', 'active'); await state(page, 'M2', 'active');
    await graphReadability(page);
    assert.equal(await page.locator('.module-node[aria-current="true"]').getAttribute('data-module-id'), 'M2', 'latest module records must be identified in the graph');
    assert.notEqual(await page.locator('[data-module-id="M1"]').evaluate(node => getComputedStyle(node).backgroundColor),
      await page.locator('[data-module-id="M2"]').evaluate(node => getComputedStyle(node).backgroundColor), 'selected and unselected active modules must stay visually distinct');
    for (const selector of ['.detail-tabs', '.module-workspace', '.module-view-heading', '.module-live', '.module-live-controls', '.module-live-event', '.module-graph', '.module-node', '.module-inspector', '.module-facts', '.module-workers']) await horizontalFit(page, selector);
    const clipped = await page.locator('.module-node').evaluateAll(nodes => nodes.flatMap(node => {
      const outer = node.getBoundingClientRect();
      return Array.from(node.querySelectorAll('.module-node-name,.module-node-subject,.module-node-state')).filter(child => {
        const box = child.getBoundingClientRect(); return box.left < outer.left - 1 || box.right > outer.right + 1 || box.top < outer.top - 1 || box.bottom > outer.bottom + 1;
      }).map(child => child.textContent);
    }));
    assert.deepEqual(clipped, [], 'module titles, subjects and states must fit their nodes');
    await page.locator('#detail-panel').evaluate(panel => { panel.scrollTop = 0; }); await screenshot(page, `modules-${width}-graph.png`);
    await selectModule(page, 'M4');
    await graphReadability(page);
    const highlighted = await page.locator('.module-edge[data-selected="true"]').evaluateAll(edges => edges.map(edge => {
      const { from, to } = (edge as HTMLElement).dataset; return `${from}:${to}`;
    }));
    assert.deepEqual(highlighted.sort(), ['M3:M4', 'M4:M1'], 'selection highlights the context input and output relationships');
    await state(page, 'M1', 'active'); await state(page, 'M2', 'active');
    const stacked = await page.evaluate(() => document.querySelector('#module-inspector')!.getBoundingClientRect().top
      >= document.querySelector('.module-graph')!.getBoundingClientRect().bottom);
    if (stacked) {
      assert.equal(await page.locator('#module-inspector').evaluate(element => document.activeElement === element), true, 'stacked module selection must move focus to its inspector');
      await page.locator('[data-module-return]').click();
      assert.equal(await page.locator('[data-module-id="M4"]').evaluate(element => document.activeElement === element), true, 'returning to the graph must focus its selected module');
      await selectModule(page, 'M4');
    } else {
      assert.equal(await page.locator('[data-module-id="M4"]').evaluate(element => document.activeElement === element), true, 'side-by-side module selection must retain focus on the node');
      assert.equal(await page.locator('[data-module-return]').isVisible(), false, 'side-by-side inspection does not need a graph return control');
    }
    await page.locator('#module-inspector').scrollIntoViewIfNeeded(); await screenshot(page, `modules-${width}-inspector.png`);
    const before = await page.locator('#module-inspector').evaluate(inspector => inspector.getBoundingClientRect().top);
    if (width <= 850) {
      await showChat(page); control.progress('diagnostic', `Module hidden at ${width}px`); await sync(h, run.id);
      await showArtifacts(page); await page.locator('#module-inspector[data-module="M4"]').waitFor();
      const after = await page.locator('#module-inspector').evaluate(inspector => inspector.getBoundingClientRect().top);
      assert.ok(Math.abs(after - before) <= 1.5, `switching mobile panes must retain the module reading position: ${JSON.stringify({ width, before, after })}`);
    }
    await page.locator('#detail-tab-source').click(); await page.locator('#detail-tab-modules').click();
    await page.locator('#module-inspector[data-module="M4"]').waitFor();
    await horizontalFit(page, '.module-node');
  }, width);

  await writeReport('passed');
  console.log(`Module checks passed: ${checks.length} scenarios; real events, latest navigation, live following, connection recovery, independent acceptance, parallel workers, retained summaries, stable reading and responsive layouts.`);
  console.log(`Report: ${path.relative(root, reportFile)}`);
} catch (error) {
  await writeReport('failed', error); throw error;
} finally {
  await browser?.close(); await service.close();
}
