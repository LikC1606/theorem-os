#!/usr/bin/env bun
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import net from 'node:net';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium, type BrowserContext, type Page, type Route } from 'playwright';
import { readWebConfig, webLimits, webTemplates } from '../apps/web/config';
import { createWebService } from '../apps/web/server';
import type { WebRunner } from '../apps/web/runner';
import { closeDialog, closeHistory, closeSettings, openHistory, openSettings, withSettings } from './web-ui-controls';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const output = path.join(root, 'out/web-ui-smoke');
const reportFile = path.join(output, 'preparation-report.json');
const credential = `sk-theoremos-preparation-fixture-${crypto.randomUUID()}`;
const widths = [1440, 375, 320];
await fs.access(path.join(root, 'out/web/app.js')).catch(() => { throw new Error('Run bun run build:web before the preparation check.'); });
await fs.mkdir(output, { recursive: true });
await fs.rm(reportFile, { force: true });
const probe = net.createServer();
await new Promise<void>(resolve => probe.listen(0, '127.0.0.1', resolve));
const port = (probe.address() as net.AddressInfo).port;
await new Promise<void>((resolve, reject) => probe.close(error => error ? reject(error) : resolve()));
const origin = `http://127.0.0.1:${port}`;
let workerStarts = 0;
const runner: WebRunner = {
  async readiness() { return { ready: true, message: 'Local preparation fixture' }; },
  async run(input, send) {
    workerStarts++;
    send({ type: 'result', result: { status: 'incomplete', proof: input.input.source, report: { fixture: true } } });
  },
};
const service = createWebService(readWebConfig({ THEOREMOS_WEB_PORT: String(port), THEOREMOS_WEB_PUBLIC_URL: origin,
  THEOREMOS_WEB_STATIC_ROOT: path.join(root, 'out/web') }), runner);
type RequestRecord = { method: string; pathname: string };
type Harness = { page: Page; context: BrowserContext; requests: RequestRecord[];
  intercept?: (route: Route) => Promise<boolean>; releases: Array<() => void> };
const checks: Array<{ name: string; elapsedMs: number; requests: RequestRecord[] }> = [];
const screenshots: string[] = [];
const validationVisibility: Array<{ field: string; width: number; geometry: unknown }> = [];
let browser: Awaited<ReturnType<typeof chromium.launch>> | undefined;
let failedScenario = '';
let failureScreenshot: string | undefined;

async function scenario(name: string, run: (h: Harness) => Promise<void>, width = 1440, expectedPosts = 0) {
  failedScenario = name;
  const started = performance.now();
  const context = await browser!.newContext({ viewport: { width, height: width > 850 ? 900 : 812 }, reducedMotion: 'reduce' });
  const page = await context.newPage();
  page.setDefaultTimeout(10_000);
  const h: Harness = { page, context, requests: [], releases: [] };
  const errors: string[] = [];
  const external: string[] = [];
  page.on('pageerror', error => errors.push(error.message));
  await context.route(/^https?:\/\//, async route => {
    const destination = new URL(route.request().url());
    if (destination.origin !== origin) { external.push(destination.href); await route.abort(); return; }
    if (destination.pathname.startsWith('/api/')) {
      h.requests.push({ method: route.request().method(), pathname: destination.pathname });
      if (await h.intercept?.(route)) return;
    }
    await route.continue();
  });
  let deadline: ReturnType<typeof setTimeout> | undefined;
  try {
    await Promise.race([run(h), new Promise<never>((_, reject) => {
      deadline = setTimeout(() => reject(new Error(`Preparation scenario exceeded 35 seconds: ${name}`)), 35_000);
    })]);
    assert.deepEqual(errors, [], 'uncaught browser errors');
    assert.deepEqual(external, [], 'preparation must not contact a model provider or external site');
    assert.equal(h.requests.filter(request => request.method === 'POST' && request.pathname === '/api/runs').length, expectedPosts,
      'invalid fields and configuration changes must not create runs');
    checks.push({ name, elapsedMs: Math.round(performance.now() - started), requests: h.requests });
    console.log(`PASS ${name}`);
  } catch (error) {
    failureScreenshot = `preparation-failure-${checks.length + 1}.png`;
    await page.screenshot({ path: path.join(output, failureScreenshot) }).catch(() => {});
    throw error;
  } finally {
    clearTimeout(deadline);
    for (const release of h.releases) release();
    await context.close();
  }
}
async function open(h: Harness) {
  await h.page.goto(origin);
  await h.page.locator('#submit-run:enabled').waitFor();
  await h.page.locator('#submission-readiness[data-state="missing"]').waitFor();
}
async function readiness(page: Page, state: string) {
  await page.locator(`#submission-readiness[data-state="${state}"]`).waitFor();
}
async function invalid(page: Page, id: string) {
  const field = page.locator(`#${id}`);
  const error = page.locator(`#${id}-validation`);
  assert.equal(await error.isVisible(), true, `${id} must have a visible local validation message`);
  assert.ok((await error.innerText()).trim());
  assert.equal(await field.getAttribute('aria-invalid'), 'true');
  assert.ok((await field.getAttribute('aria-describedby'))?.split(/\s+/).includes(`${id}-validation`));
  assert.equal(await field.evaluate(field => (field as HTMLInputElement).validity.customError), true);
  assert.equal(await field.evaluate(field => field === document.activeElement), true, `${id} must receive focus`);
}
async function corrected(page: Page, id: string, value: string) {
  await page.locator(`#${id}`).fill(value);
  assert.equal(await page.locator(`#${id}-validation`).isVisible(), false, `${id} must clear its corrected error`);
  assert.notEqual(await page.locator(`#${id}`).getAttribute('aria-invalid'), 'true');
  assert.equal(await page.locator(`#${id}`).evaluate(field => (field as HTMLInputElement).validity.valid), true);
}
async function snapshot(page: Page, name: string, fullPage = false) {
  await page.screenshot({ path: path.join(output, name), fullPage });
  screenshots.push(name);
}
async function bounds(page: Page, selector: string) {
  const box = await page.locator(selector).boundingBox();
  const viewport = page.viewportSize()!;
  assert.ok(box && box.x >= 0 && box.y >= 0 && box.x + box.width <= viewport.width + 1 &&
    box.y + box.height <= viewport.height + 1, `${selector} must fit ${viewport.width}px viewport`);
  assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth + 1), true);
}
async function visibleSettingsError(page: Page, id: string) {
  const geometry = await page.evaluate(id => {
    const scroller = document.querySelector<HTMLElement>('#run-settings .settings-content')!;
    const control = document.getElementById(id)!;
    const error = document.getElementById(`${id}-validation`)!;
    const rect = (element: Element) => {
      const { top, right, bottom, left, width, height } = element.getBoundingClientRect();
      return { top, right, bottom, left, width, height };
    };
    const scrollBox = rect(scroller);
    const visible = {
      top: Math.max(0, scrollBox.top + scroller.clientTop),
      right: Math.min(innerWidth, scrollBox.left + scroller.clientLeft + scroller.clientWidth),
      bottom: Math.min(innerHeight, scrollBox.top + scroller.clientTop + scroller.clientHeight),
      left: Math.max(0, scrollBox.left + scroller.clientLeft),
    };
    const fieldBox = rect(control), errorBox = rect(error);
    return { visible, control: fieldBox, error: errorBox, scrollTop: scroller.scrollTop,
      controlIntersects: Math.min(fieldBox.right, visible.right) > Math.max(fieldBox.left, visible.left) &&
        Math.min(fieldBox.bottom, visible.bottom) > Math.max(fieldBox.top, visible.top),
      errorFullyVisible: errorBox.width > 0 && errorBox.height > 0 && errorBox.top >= visible.top - 1 &&
        errorBox.right <= visible.right + 1 && errorBox.bottom <= visible.bottom + 1 && errorBox.left >= visible.left - 1,
    };
  }, id);
  validationVisibility.push({ field: id, width: page.viewportSize()!.width, geometry });
  assert.equal(geometry.controlIntersects, true, `${id} must intersect the settings scroller after automatic focus: ${JSON.stringify(geometry)}`);
  assert.equal(geometry.errorFullyVisible, true, `${id} error must be fully readable inside the settings scroller after automatic focus: ${JSON.stringify(geometry)}`);
}
async function doesNotStealFocus(page: Page, selector: string) {
  assert.equal(await page.evaluate(async selector => {
    const dialog = document.querySelector<HTMLDialogElement>(selector)!;
    const task = document.querySelector<HTMLTextAreaElement>('#task')!;
    const closed = new Promise(resolve => dialog.addEventListener('close', resolve, { once: true }));
    dialog.close();
    task.focus();
    await closed;
    return document.activeElement === task;
  }, selector), true, `${selector}'s queued close event must preserve the next focus choice`);
}
async function writeReport(status: 'passed' | 'failed', error?: unknown) {
  await fs.writeFile(reportFile, JSON.stringify({ status, checkedAt: new Date().toISOString(),
    mode: 'Real local HTTP service and Chromium with an in-process fixture runner. No Docker, Lean or model provider is called.',
    paidModelCalls: false, workerStarts, checks, widths, screenshots, validationVisibility,
    ...(error ? { failedScenario, error: error instanceof Error ? error.message : String(error), failureScreenshot } : {}) }, null, 2) + '\n');
}

try {
  await new Promise<void>((resolve, reject) => { service.server.once('error', reject); service.server.listen(port, '127.0.0.1', resolve); });
  browser = await chromium.launch({ headless: true });

  for (const width of widths) await scenario(`First-run preparation is explicit, local and visible at ${width}px`, async h => {
    const { page } = h;
    await open(h);
    assert.match(await page.locator('#submission-readiness').innerText(), /API Key/);
    assert.equal(await page.locator('#run-settings').isVisible(), false);
    assert.equal(await page.locator('[id$="-validation"]:visible').count(), 0, 'untouched fields must not show validation errors');
    assert.equal(await page.locator('#readiness-action').isVisible(), true);
    await bounds(page, '#submission-readiness');
    await bounds(page, '#submit-run');
    const selected = await page.locator('#template').inputValue();
    assert.ok(selected);
    assert.equal(await page.locator(`[data-chat-template="${selected}"]`).getAttribute('aria-pressed'), 'true');
    assert.equal(await page.locator('[data-chat-template][aria-pressed="true"]').count(), 1);
    await snapshot(page, `preparation-${width}.png`);
    await page.locator('#prepare-run').click();
    await page.locator('#run-settings[open]').waitFor();
    assert.equal(await page.locator('#api-key').evaluate(field => field === document.activeElement), true);
    await page.locator('#api-key').fill(credential);
    await closeSettings(page);
    assert.equal(await page.locator('#prepare-run').evaluate(button => button === document.activeElement), true,
      'Native closing must return to the preparation button that opened the dialog');
    await readiness(page, 'ready');
    assert.match(await page.locator('#submission-readiness').innerText(), /提交配置已填写/);
    assert.match(await page.locator('#submission-readiness').innerText(), /可用性将在提交时确认/);
    assert.equal((await page.locator('#submission-readiness').innerText()).includes(credential), false);
    assert.equal(h.requests.filter(request => request.method !== 'GET').length, 0);
    assert.equal(workerStarts, 0);
    await page.locator('#composer-settings').click();
    await closeSettings(page);
    assert.equal(await page.locator('#composer-settings').evaluate(button => button === document.activeElement), true,
      'Closing settings opened from the composer must restore the composer trigger');
    await page.locator('#composer-settings').click();
    await doesNotStealFocus(page, '#run-settings');
    await openHistory(page);
    await closeHistory(page);
    assert.equal(await page.locator('#open-history').evaluate(button => button === document.activeElement), true);
    await openHistory(page);
    await doesNotStealFocus(page, '#history-dialog');
  }, width);

  await scenario('Invalid settings identify the exact field, clear on correction and never POST', async h => {
    const { page } = h;
    await open(h);
    await openSettings(page);
    await page.locator('#api-key').fill(credential);
    const validSource = await page.locator('#source').inputValue();
    const validModel = await page.locator('#model').inputValue();
    const cases = [
      { id: 'source', value: ' \n\t ', good: validSource },
      { id: 'source', value: '中'.repeat(Math.floor(webLimits.maxSourceBytes / 3) + 1), good: validSource },
      { id: 'model', value: '   ', good: validModel },
      { id: 'model', value: 'invalid model', good: validModel },
      { id: 'model', value: 'm'.repeat(129), good: validModel },
      { id: 'api-key', value: '   ', good: credential },
      { id: 'api-key', value: 'sk-x', good: credential },
      { id: 'api-key', value: 'sk-fixture internal-space', good: credential },
      { id: 'api-key', value: 'sk-fixture-非ASCII', good: credential },
      { id: 'api-key', value: 'k'.repeat(4097), good: credential },
      { id: 'max-turns', value: '1.5', good: '3' },
      { id: 'max-seconds', value: '29', good: '90' },
      { id: 'workers', value: String(webLimits.maxWorkers + 1), good: '1' },
    ];
    for (const { id, value, good } of cases) {
      await page.locator(`#${id}`).fill(value);
      await page.locator('#settings-submit').click();
      assert.equal(await page.locator('#run-settings').isVisible(), true, 'settings errors must stay in the active dialog');
      await invalid(page, id);
      if (id === 'api-key' && value.trim()) assert.equal((await page.locator('#api-key-validation').innerText()).includes(value), false,
        'Validation must not repeat the entered secret');
      assert.equal(h.requests.filter(request => request.method === 'POST').length, 0);
      await corrected(page, id, good);
    }
    await closeSettings(page);
    await readiness(page, 'ready');
  });

  await scenario('Invalid tasks leave settings, focus the composer and recover without a request', async h => {
    const { page } = h;
    await open(h);
    await withSettings(page, () => page.locator('#api-key').fill(credential));
    for (const value of [' \n\t ', '中'.repeat(Math.floor(webLimits.maxTaskBytes / 3) + 1)]) {
      await page.locator('#task').fill(value);
      await openSettings(page);
      await closeDialog(page, '#run-settings', () => page.locator('#settings-submit').click());
      await invalid(page, 'task');
      await corrected(page, 'task', '保留原题，构造并验证证明。');
    }
    await readiness(page, 'ready');
  });

  await scenario('Nested source editing keeps settings open and restores its source trigger', async h => {
    const { page } = h;
    await open(h);
    await openSettings(page);
    const original = await page.locator('#source').inputValue();
    await page.locator('#expand-source').click();
    await page.locator('#source-editor[open]').waitFor();
    assert.equal(await page.locator('#run-settings').evaluate(dialog => (dialog as HTMLDialogElement).open), true);
    assert.equal(await page.locator('#expanded-source').evaluate(field => field === document.activeElement), true);
    await page.locator('#expanded-source').fill(`${original}\n-- discarded preparation fixture`);
    await closeDialog(page, '#source-editor', () => page.keyboard.press('Escape'));
    assert.equal(await page.locator('#expand-source').evaluate(button => button === document.activeElement), true);
    assert.equal(await page.locator('#source').inputValue(), original);
    await page.locator('#expand-source').click();
    const edited = `${original}\n-- applied preparation fixture`;
    await page.locator('#expanded-source').fill(edited);
    await closeDialog(page, '#source-editor', () => page.locator('#apply-editor').click());
    assert.equal(await page.locator('#source').inputValue(), edited);
    assert.equal(await page.locator('#expand-source').evaluate(button => button === document.activeElement), true);
    await closeSettings(page);
  });

  await scenario('Confirmed imports open the API Key field without a delayed focus override', async h => {
    const { page } = h;
    await open(h);
    const template = webTemplates.find(template => template.environment === 'standard')!;
    const draft = { providerId: 'openai', model: 'fixture-import-model', effort: 'high', environment: 'standard', templateId: '',
      source: template.source, task: 'Imported preparation task', maxTurns: '3', maxRunSeconds: '90', workers: '1', coordination: 'cooperative' };
    await page.locator('#task-file').setInputFiles({ name: 'preparation.json', mimeType: 'application/json',
      buffer: Buffer.from(JSON.stringify({ schema: 'theorem-os.web-draft.v1', draft })) });
    await page.locator('#import-task-dialog[open]').waitFor();
    await closeDialog(page, '#import-task-dialog', () => page.locator('#confirm-import').click());
    await page.locator('#run-settings[open]').waitFor();
    assert.equal(await page.locator('#api-key').evaluate(field => field === document.activeElement), true);
    assert.equal(await page.locator('#api-key').inputValue(), '');
    assert.equal(await page.locator('#model').inputValue(), draft.model);
    assert.equal(await page.locator('#task').inputValue(), draft.task);
    await closeSettings(page);
    await readiness(page, 'missing');
  });

  for (const width of [320, 375]) await scenario(`Mobile settings errors remain readable after automatic focus at ${width}px`, async h => {
    const { page } = h;
    await open(h);
    await openSettings(page);
    await page.locator('#api-key').fill(credential);
    const validSource = await page.locator('#source').inputValue();
    const validModel = await page.locator('#model').inputValue();
    const cases = [
      { id: 'model', value: 'invalid model', good: validModel },
      { id: 'source', value: '中'.repeat(Math.floor(webLimits.maxSourceBytes / 3) + 1), good: validSource },
      { id: 'api-key', value: 'sk-x', good: credential },
    ];
    for (const { id, value, good } of cases) {
      await page.locator(`#${id}`).fill(value);
      await page.locator('#settings-submit').click();
      await invalid(page, id);
      // Observe the product's focus scrolling; do not scroll the error into view in the test.
      await snapshot(page, `preparation-${width}-${id}-error.png`);
      await visibleSettingsError(page, id);
      assert.equal(h.requests.filter(request => request.method === 'POST').length, 0);
      await corrected(page, id, good);
    }
  }, width);

  await scenario('A successful local fixture submission shows progress and requires the next Key', async h => {
    const { page } = h;
    await open(h);
    await withSettings(page, () => page.locator('#api-key').fill(credential));
    await readiness(page, 'ready');
    let release!: () => void;
    const gate = new Promise<void>(resolve => { release = resolve; });
    h.releases.push(release);
    h.intercept = async route => {
      if (route.request().method() !== 'POST' || new URL(route.request().url()).pathname !== '/api/runs') return false;
      await gate;
      await route.continue();
      return true;
    };
    const response = page.waitForResponse(response => new URL(response.url()).pathname === '/api/runs' && response.request().method() === 'POST');
    await page.locator('#submit-run').click();
    await readiness(page, 'submitting');
    assert.equal(await page.locator('#submit-run').isDisabled(), true);
    release();
    assert.equal((await response).status(), 201);
    await page.waitForFunction(() => (document.querySelector('#api-key') as HTMLInputElement).value === '');
    await readiness(page, 'missing');
    assert.equal(await page.locator('#api-key').getAttribute('type'), 'password');
    assert.equal(workerStarts, 1, 'only the explicit valid submission may start the local fixture');
    assert.equal((await page.locator('#submission-readiness').innerText()).includes(credential), false);
  }, 1440, 1);

  await writeReport('passed');
  console.log(`Preparation checks passed: ${checks.length} scenarios, 3 viewport sizes, visible local readiness, field-specific validation, zero invalid POSTs, native dialog focus and nested editing, import handoff, and one local fixture submission.`);
  console.log(`Report: ${path.relative(root, reportFile)}`);
} catch (error) {
  await writeReport('failed', error);
  throw error;
} finally {
  await browser?.close();
  await service.close();
}
