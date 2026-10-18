#!/usr/bin/env bun
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import net from 'node:net';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium, type BrowserContext, type Page, type Route } from 'playwright';
import { readWebConfig } from '../apps/web/config';
import { createWebService } from '../apps/web/server';
import type { WebRunner } from '../apps/web/runner';
import type { WebResult, WebRun, WebRunInput } from '../apps/web/shared';
import { closeHistory, openHistory, refreshHistory, selectHistoryRun } from './web-ui-controls';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const output = path.join(root, 'out/web-ui-smoke');
const reportFile = path.join(output, 'results-report.json');
await fs.access(path.join(root, 'out/web/app.js')).catch(() => { throw new Error('Run bun run build:web before the results check.'); });
await fs.mkdir(output, { recursive: true });
await fs.rm(reportFile, { force: true });
const probe = net.createServer();
await new Promise<void>(resolve => probe.listen(0, '127.0.0.1', resolve));
const port = (probe.address() as net.AddressInfo).port;
await new Promise<void>((resolve, reject) => probe.close(error => error ? reject(error) : resolve()));
const origin = `http://127.0.0.1:${port}`;
const credential = `sk-theoremos-results-fixture-${crypto.randomUUID()}`;
const source = 'theorem result_fixture : True := by trivial\n';
const markup = '<img data-report-injection src=x onerror="window.__reportInjected=true">';
const theoremName = `Fixture.report_${'long_identifier_'.repeat(8)}${markup}`;
const diagnostic = `Submission.lean:2:3: error: candidate does not prove the original theorem\n${markup}\n<&> \"quoted\"`;
const failedReport: Record<string, unknown> = {
  schema: 'deepscientist.math.run.v2', runId: 'internal-solver-run-fixture', problemId: 'fixture-problem',
  status: 'evaluated_failed', solver_ready_receipt_valid: true, completion_signal_valid: false,
  turns: 2, solveWallMs: 12_750, usage: { totalTokens: 1200, inputTokens: 900, outputTokens: 300 },
  candidateCheck: { passed: true, status: 'kernel_verified', results: [
    { theoremName, status: 'kernel_verified', sorryCount: 0, admitCount: 0 },
  ] },
  evaluator: { status: 'failed', method: 'host-lean-kernel-all-targets', official: false,
    verification: { passed: false, commit: 'b'.repeat(40), sourceDigest: 'a'.repeat(64), verification: {
      schema: 'deepscientist.mathematics.verification-batch/v1', status: 'failed', durationMs: 1234,
      results: [{ theoremName, proofPath: 'Submission.lean', status: 'failed', sorryCount: 1, admitCount: 0,
        goalsRemaining: 1, error: diagnostic, stdoutPreview: 'Fixture Lean stdout', stderrPreview: 'Fixture Lean stderr' }], events: [],
    } } },
  customPayload: { untouched: true, markup, values: [0, false, null, { nested: 'preserve this field' }] },
};
const result = (report: Record<string, unknown> = {}, status = 'incomplete'): WebResult => ({ status, proof: source, report });
type Control = { emit(value: WebResult): void; finish(value?: WebResult): void; fail(error: Error): void };
const controls = new Map<string, Control>();
let workerStarts = 0;
const runner: WebRunner = {
  async readiness() { return { ready: true, message: 'Local results fixture' }; },
  async run(input, send, signal) {
    workerStarts++;
    await new Promise<void>((resolve, reject) => {
      const cleanup = () => { signal.removeEventListener('abort', abort); controls.delete(input.id); };
      const abort = () => { cleanup(); reject(new Error('Cancelled fixture')); };
      signal.addEventListener('abort', abort, { once: true });
      controls.set(input.id, {
        emit: value => send({ type: 'result', result: value }),
        finish: value => { if (value) send({ type: 'result', result: value }); cleanup(); resolve(); },
        fail: error => { cleanup(); reject(error); },
      });
      if (signal.aborted) abort();
    });
  },
};
const service = createWebService(readWebConfig({ THEOREMOS_WEB_PORT: String(port), THEOREMOS_WEB_PUBLIC_URL: origin,
  THEOREMOS_WEB_STATIC_ROOT: path.join(root, 'out/web'), THEOREMOS_WEB_CONCURRENCY: '8', THEOREMOS_WEB_QUEUE_LIMIT: '32' }), runner);
type RequestRecord = { method: string; pathname: string };
type Harness = {
  page: Page; context: BrowserContext; requests: RequestRecord[]; runIds: string[]; releases: Array<() => void>;
  intercept?: (route: Route) => Promise<boolean>;
};
const checks: Array<{ name: string; elapsedMs: number; requests: RequestRecord[] }> = [];
const screenshots: string[] = [];
const archiveDownloads: Array<{ status: 'cancelled' | 'error'; from: 'header' | 'confirmation' }> = [];
const widths = [1440, 375, 320];
let browser: Awaited<ReturnType<typeof chromium.launch>> | undefined;
let failedScenario = '';
let failureScreenshot: string | undefined;
function deferred() {
  let resolve!: () => void;
  const promise = new Promise<void>(done => { resolve = done; });
  return { promise, resolve };
}
const pathname = (route: Route) => new URL(route.request().url()).pathname;
const isList = (route: Route) => route.request().method() === 'GET' && pathname(route) === '/api/runs';
const isDelete = (route: Route, id?: string) => route.request().method() === 'DELETE' && (!id || pathname(route) === `/api/runs/${id}`);
const deleteCount = (h: Harness, id?: string) => h.requests.filter(request => request.method === 'DELETE' && (!id || request.pathname === `/api/runs/${id}`)).length;
const ready = (page: Page) => page.locator('#submit-run:enabled').waitFor();
async function scenario(name: string, run: (h: Harness) => Promise<void>) {
  failedScenario = name;
  const started = performance.now();
  const context = await browser!.newContext({ viewport: { width: 1440, height: 900 }, permissions: ['clipboard-read', 'clipboard-write'] });
  const page = await context.newPage();
  page.setDefaultTimeout(10_000);
  const h: Harness = { page, context, requests: [], runIds: [], releases: [] };
  const pageErrors: string[] = [];
  page.on('pageerror', error => pageErrors.push(error.message));
  await page.route('**/api/**', async route => {
    h.requests.push({ method: route.request().method(), pathname: pathname(route) });
    if (await h.intercept?.(route)) return;
    await route.continue();
  });
  let deadline: ReturnType<typeof setTimeout> | undefined;
  try {
    await page.goto(origin); await ready(page);
    await Promise.race([run(h), new Promise<never>((_, reject) => {
      deadline = setTimeout(() => reject(new Error(`Results scenario exceeded 35 seconds: ${name}`)), 35_000);
    })]);
    assert.deepEqual(pageErrors, [], 'uncaught browser errors');
    checks.push({ name, elapsedMs: Math.round(performance.now() - started), requests: h.requests });
    console.log(`PASS ${name}`);
  } catch (error) {
    failureScreenshot = `results-failure-${checks.length + 1}.png`;
    await page.screenshot({ path: path.join(output, failureScreenshot), fullPage: true }).catch(() => {});
    throw error;
  } finally {
    clearTimeout(deadline);
    for (const release of h.releases) release();
    for (const id of h.runIds) controls.get(id)?.finish(result());
    await context.close();
  }
}
async function createRun(h: Harness, title: string, completed: WebResult | null = result()): Promise<WebRun> {
  const input: WebRunInput = { providerId: 'openai', apiKey: credential, model: 'fixture-results-model', effort: 'low',
    environment: 'standard', source, task: title, maxTurns: 2, maxRunSeconds: 60, workers: 1, coordination: 'independent' };
  const run = await h.page.evaluate(async input => {
    const session = await (await fetch('/api/session')).json();
    const response = await fetch('/api/runs', { method: 'POST', headers: { 'Content-Type': 'application/json', 'X-CSRF-Token': session.csrfToken }, body: JSON.stringify(input) });
    if (response.status !== 201) throw new Error(`Fixture creation failed: ${response.status}`);
    return (await response.json()).run as WebRun;
  }, input);
  h.runIds.push(run.id);
  assert.ok(controls.has(run.id), 'fixture worker must have started');
  if (completed) controls.get(run.id)!.finish(completed);
  return h.page.evaluate(async id => (await (await fetch(`/api/runs/${id}`)).json()).run as WebRun, run.id);
}
async function refresh(h: Harness) {
  await openHistory(h.page);
  await h.page.locator('#refresh-runs:enabled').waitFor();
  const response = h.page.waitForResponse(response => new URL(response.url()).pathname === '/api/runs' && response.request().method() === 'GET');
  await h.page.locator('#refresh-runs').click();
  assert.equal((await response).status(), 200);
  await h.page.locator('#refresh-runs:enabled').waitFor();
  await closeHistory(h.page);
}
async function select(h: Harness, id: string, report = false) {
  await selectHistoryRun(h.page, id);
  await h.page.locator(report ? '#detail-tab-report' : '#detail-tab-overview').click();
}
async function showDelete(h: Harness, id: string) {
  await select(h, id);
  await h.page.locator('[data-action="delete-run"]').click();
  await h.page.locator('#delete-run-dialog[open]').waitFor();
}
async function deleteSelected(h: Harness, id: string) {
  await showDelete(h, id);
  await h.page.locator('#confirm-delete').click();
  await h.page.locator(`[data-run-id="${id}"]`).waitFor({ state: 'detached' });
  await h.page.locator('#delete-run-dialog[open]').waitFor({ state: 'hidden' });
}
async function screenshot(page: Page, name: string) {
  await page.waitForFunction(() => !document.querySelector('[data-motion]'));
  await page.screenshot({ path: path.join(output, name), fullPage: true });
  screenshots.push(name);
}
async function assertNoResultArchive(h: Harness, run: WebRun, status: 'cancelled' | 'error') {
  async function downloadArchive(selector: string, from: 'header' | 'confirmation') {
    const link = h.page.locator(selector);
    await link.waitFor({ state: 'visible' });
    const pending = h.page.waitForEvent('download');
    await link.click();
    const downloaded = await pending;
    assert.equal(downloaded.suggestedFilename(), `theoremos-${run.id}.json`);
    const raw = await fs.readFile((await downloaded.path())!, 'utf8');
    const archive = JSON.parse(raw) as { schema: string; run: WebRun };
    assert.equal(archive.schema, 'theorem-os.web-export.v1');
    assert.equal(archive.run.id, run.id);
    assert.equal(archive.run.status, status);
    assert.equal(archive.run.result, undefined);
    assert.equal(archive.run.source, run.source);
    assert.equal(archive.run.task, run.task);
    assert.ok(archive.run.events.length > 0);
    assert.equal(raw.includes(credential), false);
    archiveDownloads.push({ status, from });
  }
  await downloadArchive(`#run-detail a[download][href="/api/runs/${run.id}/download"]`, 'header');
  const before = deleteCount(h);
  await showDelete(h, run.id);
  await screenshot(h.page, `results-${status}-archive-confirmation.png`);
  await downloadArchive('#delete-download', 'confirmation');
  await h.page.locator('#cancel-delete').click();
  await h.page.locator('#delete-run-dialog[open]').waitFor({ state: 'hidden' });
  assert.equal(deleteCount(h), before);
}
async function assertNoInjection(page: Page) {
  assert.equal(await page.locator('[data-report-injection]').count(), 0, 'report markup must be escaped');
  assert.equal(await page.evaluate(() => (window as unknown as Record<string, unknown>).__reportInjected), undefined);
}
async function assertHorizontalFit(page: Page, selector: string, width: number) {
  assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), true, `document overflow at ${width}`);
  const bounds = await page.locator(selector).boundingBox();
  assert.ok(bounds && bounds.x >= 0 && bounds.x + bounds.width <= width + 1, `${selector} overflows ${width}px viewport`);
}
async function writeReport(status: 'passed' | 'failed', error?: unknown) {
  await fs.writeFile(reportFile, JSON.stringify({ status, checkedAt: new Date().toISOString(),
    mode: 'Real HTTP service and Chromium with controlled worker results and response failures. No Docker, Lean or model provider is called.',
    paidModelCalls: false, workerStarts, checks, widths, screenshots, archiveDownloads,
    ...(error ? { failedScenario, error: error instanceof Error ? error.message : String(error), failureScreenshot } : {}) }, null, 2) + '\n');
}
try {
  await new Promise<void>((resolve, reject) => { service.server.once('error', reject); service.server.listen(port, '127.0.0.1', resolve); });
  browser = await chromium.launch({ headless: true });

  await scenario('Candidate acceptance stays separate from failed independent evaluation; diagnostics and JSON remain intact', async h => {
    const run = await createRun(h, 'Failed independent evaluation', result(failedReport, 'evaluated_failed'));
    await refresh(h); await select(h, run.id, true);
    await h.page.locator('.report-summary').waitFor();
    assert.equal(await h.page.locator('[data-report-view="summary"]').getAttribute('aria-pressed'), 'true');
    assert.equal(await h.page.locator('[data-check-stage="candidate"] .report-check-heading .badge.passed').count(), 1);
    assert.equal(await h.page.locator('[data-check-stage="evaluation"] .report-check-heading .badge.failed').count(), 1);
    assert.equal(await h.page.locator('.report-summary > .result-banner.passed').count(), 0);
    assert.equal(await h.page.locator('.report-summary > .result-banner.failed').count(), 1);
    const target = h.page.locator('[data-check-stage="evaluation"] .verification-target').first();
    assert.ok((await target.innerText()).includes(theoremName));
    assert.equal(await target.locator('.target-diagnostics[open]').count(), 1);
    assert.ok((await target.locator('.target-diagnostics').innerText()).includes(diagnostic));
    await assertNoInjection(h.page);
    await screenshot(h.page, 'results-desktop-1440-summary.png');
    await h.page.locator('[data-report-view="json"]').click();
    assert.equal(await h.page.locator('.code-scroll.report code').textContent(), JSON.stringify(failedReport, null, 2));
    await h.page.locator('[data-action="copy-report"]').click();
    assert.deepEqual(JSON.parse(await h.page.evaluate(() => navigator.clipboard.readText())), failedReport);
    const download = h.page.waitForEvent('download');
    await h.page.locator('[data-action="download-report"]').click();
    assert.deepEqual(JSON.parse(await fs.readFile((await (await download).path())!, 'utf8')), failedReport);
    await h.page.locator('[data-report-view="summary"]').click();
    await h.page.locator('.report-summary').waitFor();
    await assertNoInjection(h.page);
  });

  await scenario('Long diagnostics disclose clipping and open the intact original report at desktop and mobile widths', async h => {
    const prefix = `${diagnostic}\n${'Lean diagnostic context '.repeat(200)}`.slice(0, 4000);
    assert.equal(prefix.length, 4000);
    const report = { candidateCheck: { passed: false, results: [
      { theoremName: 'Fixture.long_diagnostic', status: 'failed', error: `${prefix}first-tail`,
        stdoutPreview: `${prefix}different-tail`, stderrPreview: 'Short stderr remains visible' },
    ] } };
    const run = await createRun(h, 'Clipped report fixture', result(report, 'evaluated_failed'));
    await refresh(h); await select(h, run.id, true);
    for (const width of widths) {
      await h.page.setViewportSize({ width, height: width > 850 ? 900 : 812 });
      if (width <= 850) await h.page.locator('#mobile-runs').click();
      await h.page.locator('[data-report-view="summary"]').click();
      assert.equal(await h.page.locator('.diagnostic-entry').count(), 3, 'diagnostics with different tails must remain separate');
      assert.equal(await h.page.locator('.diagnostic-limit').count(), 2, 'only clipped diagnostics show the notice');
      assert.deepEqual(await h.page.locator('.diagnostic-output').allTextContents(), [prefix, prefix, 'Short stderr remains visible']);
      await assertHorizontalFit(h.page, '.diagnostic-entry:first-of-type .diagnostic-limit', width);
      await assertNoInjection(h.page);
      const link = h.page.locator('.report-detail-link').last();
      await link.scrollIntoViewIfNeeded();
      assert.ok(await h.page.locator('#detail-panel').evaluate(panel => panel.scrollTop) > 0,
        'the original-report entry must be tested from a scrolled diagnostic');
      await screenshot(h.page, `results-${width}-clipped-diagnostic.png`);
      await assertHorizontalFit(h.page, '.diagnostic-entry:first-of-type .report-detail-link', width);
      const before = h.requests.filter(request => request.method !== 'GET').length;
      await link.click();
      assert.equal(await h.page.locator('[data-report-view="json"]').getAttribute('aria-pressed'), 'true');
      assert.deepEqual(JSON.parse((await h.page.locator('.code-scroll.report code').textContent())!), report);
      assert.equal(await h.page.locator('[data-report-view="json"]').evaluate(button => button === document.activeElement), true,
        'opening the original report must leave focus on the JSON view control');
      assert.equal(await h.page.locator('#detail-panel').evaluate(panel => panel.scrollTop), 0,
        'switching reports must return the outer panel to the beginning');
      assert.equal(await h.page.locator('.code-scroll.report').evaluate(report => report.scrollTop), 0);
      const jsonButton = await h.page.locator('[data-report-view="json"]').boundingBox();
      assert.ok(jsonButton && jsonButton.y >= 0 && jsonButton.y + jsonButton.height <= h.page.viewportSize()!.height,
        'the focused JSON view control must be visible');
      await screenshot(h.page, `results-${width}-original-report.png`);
      assert.equal(h.requests.filter(request => request.method !== 'GET').length, before, 'opening the report must not write to the API');
      await h.page.locator('[data-action="copy-report"]').click();
      assert.deepEqual(JSON.parse(await h.page.evaluate(() => navigator.clipboard.readText())), report);
    }
    const download = h.page.waitForEvent('download');
    await h.page.locator('[data-action="download-report"]').click();
    assert.deepEqual(JSON.parse(await fs.readFile((await (await download).path())!, 'utf8')), report);
  });

  await scenario('Missing and malformed reports remain readable; canceled and error records without results retain downloadable archives', async h => {
    const reports = [{}, { status: 'evaluated_passed', candidateCheck: { passed: 'true', status: { invalid: true }, results: [null, 5, {}, { theoremName: markup, status: ['kernel_verified'] }] },
      evaluator: { status: ['passed'], verification: { verification: { results: 'not-an-array' } } }, turns: -1,
      solveWallMs: '1000', usage: { totalTokens: '999', inputTokens: -2 }, custom: markup }];
    for (const [index, report] of reports.entries()) {
      const run = await createRun(h, `Compatibility report ${index}`, result(report));
      await refresh(h); await select(h, run.id, true);
      await h.page.locator('.report-summary').waitFor();
      assert.equal(await h.page.locator('.report-summary > .result-banner.passed').count(), 0);
      assert.equal(await h.page.locator('.report-check-heading .badge.passed').count(), 0);
      await assertNoInjection(h.page);
      await h.page.locator('[data-report-view="json"]').click();
      assert.deepEqual(JSON.parse((await h.page.locator('.code-scroll.report code').textContent())!), report);
    }
    const broken = await createRun(h, 'Error without a result', null);
    controls.get(broken.id)!.fail(new Error(`Fixture worker error ${markup}`));
    await refresh(h); await select(h, broken.id, true);
    await h.page.locator('.diagnostic-output').waitFor();
    assert.ok((await h.page.locator('#detail-panel').innerText()).includes('Fixture worker error'));
    await assertNoInjection(h.page);
    await assertNoResultArchive(h, broken, 'error');
    const cancelled = await createRun(h, 'Cancelled without a result', null);
    await refresh(h); await select(h, cancelled.id);
    await h.page.locator('[data-action="cancel"]').click();
    await h.page.locator('.result-banner').filter({ hasText: '运行已取消' }).waitFor();
    await assertNoResultArchive(h, cancelled, 'cancelled');
  });

  await scenario('An early passed result cannot make a still-running task accepted or deletable', async h => {
    const run = await createRun(h, 'Running worker with an early result', null);
    const early = result({ candidateCheck: { passed: true }, evaluator: { status: 'passed' } }, 'evaluated_passed');
    controls.get(run.id)!.emit(early);
    await refresh(h); await select(h, run.id, true);
    await h.page.locator('.report-summary').waitFor();
    assert.equal(await h.page.locator('.run-row.selected .badge.passed').count(), 0);
    assert.equal(await h.page.locator('.report-summary > .result-banner.passed').count(), 0);
    assert.equal(await h.page.locator('[data-action="delete-run"]').count(), 0);
    await h.page.locator('#detail-tab-source').click();
    assert.equal(await h.page.locator('[data-source-view="proof"]').innerText(), '候选源码');
    controls.get(run.id)!.finish();
    await refresh(h);
    await h.page.locator('.run-row.selected .badge.passed').waitFor({ state: 'attached' });
    await h.page.locator('[data-action="delete-run"]').waitFor();
  });

  await scenario('Cancel, close and Escape dismiss deletion without issuing DELETE', async h => {
    const title = `Delete confirmation ${markup}`;
    const run = await createRun(h, title);
    await refresh(h);
    for (const action of ['cancel', 'close', 'escape']) {
      await showDelete(h, run.id);
      assert.equal(await h.page.locator('#delete-title').textContent(), run.title);
      if (await h.page.locator('#delete-download').isVisible()) assert.ok((await h.page.locator('#delete-download').getAttribute('href'))?.includes(run.id));
      await assertNoInjection(h.page);
      if (action === 'escape') await h.page.keyboard.press('Escape');
      else await h.page.locator(action === 'cancel' ? '#cancel-delete' : '#close-delete').click();
      await h.page.locator('#delete-run-dialog[open]').waitFor({ state: 'hidden' });
    }
    assert.equal(deleteCount(h), 0);
    assert.equal(await h.page.locator(`[data-run-id="${run.id}"]`).count(), 1);
  });

  await scenario('Successful deletion sends one request, selects an adjacent run, and handles the final empty list', async h => {
    const first = await createRun(h, 'First run');
    const middle = await createRun(h, 'Middle run');
    const last = await createRun(h, 'Last run');
    await refresh(h); await select(h, middle.id);
    await deleteSelected(h, middle.id);
    assert.equal(deleteCount(h, middle.id), 1);
    const selected = await h.page.locator('.run-row.selected').getAttribute('data-run-id');
    assert.ok(selected === first.id || selected === last.id, 'deletion must select a neighboring record');
    await refresh(h);
    assert.equal(await h.page.locator(`[data-run-id="${middle.id}"]`).count(), 0);
    await deleteSelected(h, selected!);
    const finalId = selected === first.id ? last.id : first.id;
    await h.page.locator(`[data-run-id="${finalId}"].selected`).waitFor({ state: 'attached' });
    await deleteSelected(h, finalId);
    assert.equal(await h.page.locator('[data-run-id]').count(), 0);
    assert.equal(await h.page.locator('#run-count').innerText(), '0');
    assert.equal(await h.page.locator('.detail-empty').count(), 1);
    assert.equal(deleteCount(h), 3);
  });

  await scenario('409 and CSRF 403 deletion failures preserve the record and do not replay DELETE', async h => {
    const run = await createRun(h, 'Preserve on delete errors');
    await refresh(h);
    for (const status of [409, 403]) {
      h.intercept = async route => {
        if (!isDelete(route, run.id)) return false;
        if (status === 409) await route.fulfill({ status, json: { error: 'Fixture record is active' } });
        else await route.continue({ headers: { ...route.request().headers(), 'x-csrf-token': 'invalid-delete-fixture-token' } });
        return true;
      };
      const before = deleteCount(h, run.id);
      await showDelete(h, run.id);
      await h.page.locator('#confirm-delete').click();
      await h.page.locator('#delete-error').waitFor({ state: 'visible' });
      assert.equal(await h.page.locator(`[data-run-id="${run.id}"]`).count(), 1);
      await h.page.waitForTimeout(250);
      assert.equal(deleteCount(h, run.id), before + 1);
      await h.page.locator('#cancel-delete').click();
      await ready(h.page);
    }
    h.intercept = undefined;
    await refresh(h);
    assert.equal(await h.page.locator(`[data-run-id="${run.id}"]`).count(), 1);
  });

  await scenario('A committed DELETE with a lost response is reconciled through GET and never replayed', async h => {
    const run = await createRun(h, 'Delete response lost');
    await refresh(h);
    const committed = deferred();
    h.intercept = async route => {
      if (!isDelete(route, run.id)) return false;
      const response = await route.fetch();
      assert.equal(response.status(), 200);
      committed.resolve();
      await route.abort('failed');
      return true;
    };
    await showDelete(h, run.id);
    const beforeGet = h.requests.filter(request => request.method === 'GET' && request.pathname === '/api/runs').length;
    await h.page.locator('#confirm-delete').click();
    await committed.promise;
    await h.page.locator(`[data-run-id="${run.id}"]`).waitFor({ state: 'detached' });
    await h.page.locator('#delete-error').waitFor({ state: 'visible' });
    await h.page.locator('#confirm-delete:disabled').waitFor();
    assert.equal(await h.page.locator('#delete-run-dialog[open]').count(), 1);
    await h.page.locator('#cancel-delete:enabled').click();
    await h.page.locator('#delete-run-dialog[open]').waitFor({ state: 'hidden' });
    await ready(h.page);
    await h.page.waitForTimeout(250);
    assert.equal(deleteCount(h, run.id), 1);
    assert.ok(h.requests.filter(request => request.method === 'GET' && request.pathname === '/api/runs').length > beforeGet);
    await refresh(h);
    assert.equal(await h.page.locator(`[data-run-id="${run.id}"]`).count(), 0);
    assert.equal(deleteCount(h, run.id), 1);
  });

  await scenario('A stale in-flight list response cannot resurrect a successfully deleted record', async h => {
    const removed = await createRun(h, 'Delete while an old list is in flight');
    const survivor = await createRun(h, 'Keep this neighboring run');
    await refresh(h); await select(h, removed.id);
    const held = deferred(), release = deferred(), settled = deferred();
    h.releases.push(release.resolve);
    let hold = true;
    h.intercept = async route => {
      if (!isList(route) || !hold) return false;
      hold = false;
      const response = await route.fetch();
      const snapshot = await response.json() as { runs: WebRun[] };
      assert.ok(snapshot.runs.some(run => run.id === removed.id));
      held.resolve(); await release.promise;
      await route.fulfill({ status: 200, json: snapshot }).catch(() => {});
      settled.resolve();
      return true;
    };
    await refreshHistory(h.page);
    await held.promise;
    await deleteSelected(h, removed.id);
    release.resolve(); await settled.promise;
    await h.page.waitForTimeout(250);
    assert.equal(await h.page.locator(`[data-run-id="${removed.id}"]`).count(), 0);
    assert.equal(await h.page.locator(`[data-run-id="${survivor.id}"].selected`).count(), 1);
    await refresh(h);
    assert.equal(await h.page.locator(`[data-run-id="${removed.id}"]`).count(), 0);
    assert.equal(deleteCount(h, removed.id), 1);
  });

  await scenario('Report summaries, raw JSON and native deletion dialogs fit 320, 375 and 1440 pixel viewports', async h => {
    const run = await createRun(h, `${'Long deletion title '.repeat(5)}${markup}`, result(failedReport, 'evaluated_failed'));
    await refresh(h); await select(h, run.id, true);
    for (const width of widths) {
      await h.page.setViewportSize({ width, height: width > 850 ? 900 : 812 });
      if (width <= 850) await h.page.locator('#mobile-runs').click();
      await h.page.locator('[data-report-view="summary"]').click();
      await assertHorizontalFit(h.page, '.report-summary', width);
      const headingsFit = await h.page.locator('.target-heading').evaluateAll(headings => headings.every(heading => {
        const name = heading.querySelector('code')!.getBoundingClientRect();
        const badge = heading.querySelector('.badge')!.getBoundingClientRect();
        return name.right <= badge.left + 1 || name.top >= badge.bottom || badge.top >= name.bottom;
      }));
      assert.equal(headingsFit, true, `theorem name overlaps status at ${width}px`);
      await screenshot(h.page, `results-${width}-summary.png`);
      await h.page.locator('[data-report-view="json"]').click();
      await assertHorizontalFit(h.page, '.code-scroll.report', width);
      assert.deepEqual(JSON.parse((await h.page.locator('.code-scroll.report code').textContent())!), failedReport);
      await h.page.locator('[data-action="delete-run"]').click();
      await h.page.locator('#delete-run-dialog[open]').waitFor();
      await assertHorizontalFit(h.page, '#delete-run-dialog', width);
      assert.equal(await h.page.locator('#delete-run-dialog').evaluate(dialog => dialog.scrollWidth <= dialog.clientWidth), true, `dialog contents overflow at ${width}px`);
      for (const id of ['confirm-delete', 'cancel-delete', 'close-delete']) {
        const bounds = await h.page.locator(`#${id}`).boundingBox();
        assert.ok(bounds && bounds.y >= 0 && bounds.y + bounds.height <= 812 + (width > 850 ? 88 : 0), `${id} outside viewport at ${width}px`);
      }
      await assertNoInjection(h.page);
      await screenshot(h.page, `results-${width}-delete.png`);
      await h.page.locator('#cancel-delete').click();
    }
    assert.equal(deleteCount(h), 0);
  });

  await writeReport('passed');
  console.log(`Results report: ${reportFile}`);
} catch (error) {
  await writeReport('failed', error);
  throw error;
} finally {
  await browser?.close();
  await service.close();
}
