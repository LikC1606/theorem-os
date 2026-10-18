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
import { draftRecoveryStorageKey } from '../apps/web/client/draftRecovery';
import { closeDialog, closeHistory, closeSettings, discardSourceEditor, openHistory, openSettings, withSettings } from './web-ui-controls';

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
async function editSource(h: Harness, source: string) {
  await open(h); await openSettings(h.page);
  await h.page.locator('#template').selectOption('');
  await h.page.locator('#source').fill(source);
  await h.page.locator('#expand-source').click();
  await h.page.locator('#source-editor[open]').waitFor();
}
async function selectSourceText(page: Page, start: number, end = start, direction: 'forward' | 'backward' | 'none' = 'none') {
  await page.locator('#expanded-source').evaluate((node, selection) => {
    const editor = node as HTMLTextAreaElement;
    editor.focus(); editor.setSelectionRange(selection.start, selection.end, selection.direction);
  }, { start, end, direction });
}
async function editorValue(page: Page, expected: string) {
  await page.waitForFunction(expected => (document.querySelector('#expanded-source') as HTMLTextAreaElement).value === expected, expected);
}
async function editorPosition(page: Page, expected: string) {
  await page.waitForFunction(expected => document.querySelector('#editor-position')?.textContent === expected, expected);
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
    await discardSourceEditor(page, () => page.keyboard.press('Escape'));
    assert.equal(await page.locator('#expand-source').evaluate(button => button === document.activeElement), true);
    assert.equal(await page.locator('#source').inputValue(), original);
    await page.locator('#expand-source').click();
    const edited = `${original}\n-- applied preparation fixture`;
    await page.locator('#expanded-source').fill(edited);
    await closeDialog(page, '#source-editor', () => page.locator('#apply-editor').click());
    assert.equal(await page.locator('#source').inputValue(), edited);
    assert.equal(await page.locator('#editor-discard-dialog').isVisible(), false, 'successful Apply must close directly');
    assert.equal(await page.locator('#expand-source').evaluate(button => button === document.activeElement), true);
    await closeSettings(page);
  });

  for (const width of widths) await scenario(`Dirty close requests retain scratch edits, focus and native undo at ${width}px`, async h => {
    const { page } = h;
    const source = `theorem retained_editor_fixture : True := by\n  trivial\n${Array.from({ length: 210 }, (_, index) => `-- editor context ${index + 1}`).join('\n')}`;
    const edited = `${source} -- retained native edit`;
    await editSource(h, source);
    const recoveryBefore = await page.evaluate(key => sessionStorage.getItem(key), draftRecoveryStorageKey);
    await selectSourceText(page, source.length);
    await page.keyboard.insertText(' -- retained native edit');
    await editorValue(page, edited);
    assert.equal(await page.locator('#editor-change-status').innerText(), '修改尚未应用');
    const editor = await page.locator('#expanded-source').elementHandle();
    const methods = [
      { close: () => page.locator('#close-editor').click(), resume: () => page.locator('#keep-editing').click() },
      { close: () => page.locator('#cancel-editor').click(), resume: () => page.locator('#close-editor-discard').click() },
      { close: () => page.keyboard.press('Escape'), resume: () => page.keyboard.press('Escape') },
    ];
    for (const [index, method] of methods.entries()) {
      await selectSourceText(page, source.indexOf('-- editor context 145'), source.indexOf('-- editor context 147'), 'backward');
      const before = await page.locator('#expanded-source').evaluate(node => {
        const editor = node as HTMLTextAreaElement;
        editor.scrollTop = 190;
        return { start: editor.selectionStart, end: editor.selectionEnd, direction: editor.selectionDirection,
          top: editor.scrollTop, left: editor.scrollLeft };
      });
      assert.ok(before.top > 0);
      await method.close();
      await page.locator('#editor-discard-dialog[open]').waitFor();
      assert.equal(await page.locator('#source-editor').evaluate(dialog => (dialog as HTMLDialogElement).open), true);
      assert.equal(await page.locator('#keep-editing').evaluate(button => button === document.activeElement), true,
        'the safe continuation must receive initial focus');
      assert.equal(await page.locator('#source').inputValue(), source);
      assert.equal(await page.evaluate(key => sessionStorage.getItem(key), draftRecoveryStorageKey), recoveryBefore);
      for (const selector of ['#editor-discard-dialog', '#keep-editing', '#discard-editor-changes']) await bounds(page, selector);
      if (index === 0) await snapshot(page, `source-editor-${width}-discard-confirmation.png`);
      await closeDialog(page, '#editor-discard-dialog', method.resume);
      assert.equal(await editor!.evaluate(node => node === document.querySelector('#expanded-source')), true);
      assert.deepEqual(await page.locator('#expanded-source').evaluate(async node => {
        await new Promise<void>(resolve => requestAnimationFrame(() => resolve()));
        const editor = node as HTMLTextAreaElement;
        return { start: editor.selectionStart, end: editor.selectionEnd, direction: editor.selectionDirection,
          top: editor.scrollTop, left: editor.scrollLeft };
      }), before, 'continuing must preserve the active reading position and backward selection');
      assert.equal(await page.locator('#expanded-source').evaluate(node => node === document.activeElement), true);
      await editorValue(page, edited);
    }
    await page.keyboard.press('Control+z'); await editorValue(page, source);
    assert.equal(await page.locator('#editor-change-status').innerText(), '未修改');
    await page.keyboard.press('Control+Shift+z'); await editorValue(page, edited);
    await discardSourceEditor(page);
    assert.equal(await page.locator('#source').inputValue(), source);
    assert.equal(await page.evaluate(key => sessionStorage.getItem(key), draftRecoveryStorageKey), recoveryBefore);
    assert.equal(await page.locator('#expand-source').evaluate(button => button === document.activeElement), true);
    await page.locator('#expand-source').click();
    await editorValue(page, source);
    await closeDialog(page, '#source-editor', () => page.keyboard.press('Escape'));
    await closeSettings(page);
  }, width);

  await scenario('Unchanged, reverted and no-op edits close directly while keyboard confirmation defaults to continuing', async h => {
    const { page } = h;
    const source = 'theorem clean_editor_fixture : True := by\n  trivial';
    await editSource(h, source);
    for (const action of ['#close-editor', '#cancel-editor', 'Escape']) {
      assert.equal(await page.locator('#editor-change-status').innerText(), '未修改');
      await closeDialog(page, '#source-editor', () => action === 'Escape' ? page.keyboard.press('Escape') : page.locator(action).click());
      assert.equal(await page.locator('#editor-discard-dialog').isVisible(), false);
      await page.locator('#expand-source').click();
    }
    await selectSourceText(page, 0);
    await page.locator('#editor-outdent').click();
    assert.equal(await page.locator('#editor-change-status').innerText(), '未修改');
    await selectSourceText(page, source.length);
    await page.keyboard.insertText(' -- keyboard fixture');
    await page.keyboard.press('Escape');
    await page.locator('#editor-discard-dialog[open]').waitFor();
    await closeDialog(page, '#editor-discard-dialog', () => page.keyboard.press('Enter'));
    assert.equal(await page.locator('#expanded-source').evaluate(node => node === document.activeElement), true);
    await editorValue(page, `${source} -- keyboard fixture`);
    await page.keyboard.press('Control+z'); await editorValue(page, source);
    assert.equal(await page.locator('#editor-change-status').innerText(), '未修改');
    await closeDialog(page, '#source-editor', () => page.keyboard.press('Escape'));
    assert.equal(await page.locator('#editor-discard-dialog').isVisible(), false);
    await closeSettings(page);
  });

  await scenario('Invalid scratch buffers stay protected and application still creates exactly one recovery backup', async h => {
    const { page } = h;
    const source = 'theorem invalid_editor_fixture : True := by\n  trivial';
    await editSource(h, source);
    const recoveryBefore = await page.evaluate(key => sessionStorage.getItem(key), draftRecoveryStorageKey);
    for (const invalid of [' \n\t ', 'x'.repeat(webLimits.maxSourceBytes + 1)]) {
      await page.locator('#expanded-source').fill(invalid);
      await page.locator('#apply-editor').click();
      assert.equal(await page.locator('#editor-error').isVisible(), true);
      await page.locator('#close-editor').click();
      await page.locator('#editor-discard-dialog[open]').waitFor();
      await closeDialog(page, '#editor-discard-dialog', () => page.locator('#keep-editing').click());
      await editorValue(page, invalid);
      assert.equal(await page.locator('#editor-error').isVisible(), true, 'continuing must not hide an unresolved validation error');
      assert.equal(await page.locator('#source').inputValue(), source);
      assert.equal(await page.evaluate(key => sessionStorage.getItem(key), draftRecoveryStorageKey), recoveryBefore);
    }
    const applied = `${source}\n-- valid applied edit`;
    await page.locator('#expanded-source').fill(applied);
    await closeDialog(page, '#source-editor', () => page.locator('#apply-editor').click());
    assert.equal(await page.locator('#editor-discard-dialog').isVisible(), false);
    assert.equal(await page.locator('#source').inputValue(), applied);
    const recovery = await page.evaluate(key => JSON.parse(sessionStorage.getItem(key)!), draftRecoveryStorageKey);
    assert.equal(recovery.reason, 'edit'); assert.equal(recovery.task.draft.source, source);
    await closeSettings(page);
  });

  await scenario('Delayed Lean imports leave the original editor baseline and stale-revision check intact', async h => {
    const { page } = h;
    const source = 'theorem delayed_editor_fixture : True := by\n  trivial';
    const incoming = `${source}\n-- delayed file replacement`;
    await open(h); await openSettings(page);
    await page.locator('#template').selectOption(''); await page.locator('#source').fill(source);
    await page.evaluate(() => {
      const original = File.prototype.arrayBuffer;
      File.prototype.arrayBuffer = async function () {
        File.prototype.arrayBuffer = original;
        const data = await original.call(this);
        await new Promise<void>(resolve => { (window as unknown as { releaseEditorImport: () => void }).releaseEditorImport = resolve; });
        return data;
      };
    });
    await page.locator('#source-file').setInputFiles({ name: 'editor-delayed.lean', mimeType: 'text/plain', buffer: Buffer.from(incoming) });
    await page.waitForFunction(() => typeof (window as unknown as { releaseEditorImport?: () => void }).releaseEditorImport === 'function');
    await page.locator('#expand-source').click();
    await page.locator('#expanded-source').fill(incoming);
    await page.keyboard.press('Escape'); await page.locator('#editor-discard-dialog[open]').waitFor();
    await page.evaluate(() => (window as unknown as { releaseEditorImport: () => void }).releaseEditorImport());
    await page.waitForFunction(incoming => (document.querySelector('#source') as HTMLTextAreaElement).value === incoming, incoming);
    const recoveryAfterImport = await page.evaluate(key => sessionStorage.getItem(key), draftRecoveryStorageKey);
    await closeDialog(page, '#editor-discard-dialog', () => page.locator('#keep-editing').click());
    await editorValue(page, incoming);
    assert.equal(await page.locator('#editor-change-status').innerText(), '修改尚未应用', 'dirty state compares the opening baseline, even when a new draft has the same text');
    await page.locator('#apply-editor').click();
    assert.match(await page.locator('#editor-error').innerText(), /原始草稿已变化/);
    await discardSourceEditor(page);
    assert.equal(await page.locator('#source').inputValue(), incoming);
    assert.equal(await page.evaluate(key => sessionStorage.getItem(key), draftRecoveryStorageKey), recoveryAfterImport);
    await closeSettings(page);
  });

  await scenario('Direct editor entry restores its trigger and old close events cannot clear a reopened confirmation', async h => {
    const { page } = h;
    await open(h);
    const source = await page.locator('#source').inputValue();
    await page.locator('#edit-draft-source').click();
    await page.locator('#expanded-source').fill(`${source}\n-- direct discarded edit`);
    await discardSourceEditor(page);
    assert.equal(await page.locator('#edit-draft-source').evaluate(button => button === document.activeElement), true);
    assert.equal(await page.locator('#run-settings').isVisible(), false);
    await page.locator('#edit-draft-source').click();
    await page.locator('#expanded-source').fill(`${source}\n-- first session`);
    await page.locator('#close-editor').click(); await page.locator('#editor-discard-dialog[open]').waitFor();
    const reopened = `${source}\n-- reopened session`;
    await page.locator('#discard-editor-changes').evaluate((button, reopened) => {
      (button as HTMLButtonElement).click();
      (document.querySelector('#edit-draft-source') as HTMLButtonElement).click();
      const editor = document.querySelector('#expanded-source') as HTMLTextAreaElement;
      editor.value = reopened; editor.dispatchEvent(new Event('input', { bubbles: true }));
      editor.setSelectionRange(2, 7, 'backward');
      (document.querySelector('#close-editor') as HTMLButtonElement).click();
    }, reopened);
    await page.evaluate(() => new Promise<void>(resolve => requestAnimationFrame(() => resolve())));
    await page.locator('#editor-discard-dialog[open]').waitFor();
    await closeDialog(page, '#editor-discard-dialog', () => page.locator('#keep-editing').click());
    await editorValue(page, reopened);
    assert.deepEqual(await page.locator('#expanded-source').evaluate(node => {
      const editor = node as HTMLTextAreaElement;
      return [editor.selectionStart, editor.selectionEnd, editor.selectionDirection];
    }), [2, 7, 'backward']);
    await discardSourceEditor(page);
    assert.equal(await page.locator('#source').inputValue(), source);
    assert.equal(await page.locator('#edit-draft-source').evaluate(button => button === document.activeElement), true);
  });

  for (const width of widths) await scenario(`Source indentation keeps native undo, selected-line boundaries and local drafts at ${width}px`, async h => {
    const { page } = h;
    const source = 'theorem indentation_fixture : True := by\n  have h : True := by\n    trivial\n  exact h\n-- untouched next line\n';
    const first = source.indexOf('  have'), end = source.indexOf('-- untouched');
    const indented = source.split('\n').map((line, index) => index >= 1 && index <= 3 ? `  ${line}` : line).join('\n');
    await editSource(h, source);
    const recoveryBefore = await page.evaluate(key => sessionStorage.getItem(key), draftRecoveryStorageKey);
    await editorPosition(page, '第 1 行 · 第 1 列');
    await selectSourceText(page, first + 2, end, 'backward');
    await editorPosition(page, '第 2 行 · 第 3 列');
    await page.locator('#editor-indent').click();
    await editorValue(page, indented);
    assert.deepEqual(await page.locator('#expanded-source').evaluate(node => {
      const editor = node as HTMLTextAreaElement;
      return { start: editor.selectionStart, end: editor.selectionEnd, direction: editor.selectionDirection, focused: editor === document.activeElement };
    }), { start: first + 4, end: end + 6, direction: 'backward', focused: true });
    await editorPosition(page, '第 2 行 · 第 5 列');
    assert.equal(await page.locator('#source').inputValue(), source, 'indentation stays in the modal buffer');
    assert.equal(await page.evaluate(key => sessionStorage.getItem(key), draftRecoveryStorageKey), recoveryBefore,
      'scratch edits do not replace the existing recovery backup');
    await page.keyboard.press('Control+z'); await editorValue(page, source);
    await page.keyboard.press('Control+Shift+z'); await editorValue(page, indented);
    await selectSourceText(page, first + 4, end + 6, 'backward');
    await page.locator('#editor-outdent').click(); await editorValue(page, source);
    await page.keyboard.press('Control+z'); await editorValue(page, indented);
    await page.keyboard.press('Control+Shift+z'); await editorValue(page, source);
    for (const selector of ['#source-editor', '.editor-toolbar', '#editor-indent', '#editor-outdent', '#editor-position', '#apply-editor', '#cancel-editor']) await bounds(page, selector);
    const placement = await page.evaluate(() => {
      const buttons = document.querySelector('.editor-indent-tools')!.getBoundingClientRect();
      const position = document.querySelector('#editor-position')!.getBoundingClientRect();
      return { buttonsRight: buttons.right, positionLeft: position.left };
    });
    assert.ok(placement.buttonsRight <= placement.positionLeft, 'cursor status must not overlap tools');
    await snapshot(page, `source-editor-${width}-indentation.png`);
    await closeDialog(page, '#source-editor', () => page.locator('#cancel-editor').click());
    assert.equal(await page.locator('#source').inputValue(), source);
    assert.equal(await page.evaluate(key => sessionStorage.getItem(key), draftRecoveryStorageKey), recoveryBefore);
    await page.locator('#expand-source').click();
    await selectSourceText(page, first + 2, end, 'backward');
    await page.locator('#editor-indent').click();
    await closeDialog(page, '#source-editor', () => page.locator('#apply-editor').click());
    assert.equal(await page.locator('#source').inputValue(), indented);
    assert.equal(await page.locator('#restore-draft-settings').isVisible(), true, 'applying remains one recoverable draft replacement');
    const recovery = await page.evaluate(key => JSON.parse(sessionStorage.getItem(key)!), draftRecoveryStorageKey);
    assert.equal(recovery.reason, 'edit'); assert.equal(recovery.task.draft.source, source);
    await page.locator('#expand-source').click();
    await page.keyboard.press('Control+z'); await editorValue(page, indented);
    assert.equal(await page.locator('#source').inputValue(), indented, 'reopening must not expose an old editing transaction');
    await closeDialog(page, '#source-editor', () => page.keyboard.press('Escape'));
    await closeSettings(page);
  }, width);

  await scenario('Editor shortcuts preserve ordinary input, IME and Tab focus navigation', async h => {
    const { page } = h;
    const source = 'theorem keyboard_indent_fixture : True := by\n  trivial';
    const start = source.indexOf('  trivial');
    await editSource(h, source);
    await selectSourceText(page, start + 2);
    await page.keyboard.press('Control+]');
    await editorValue(page, source.slice(0, start) + '  ' + source.slice(start));
    await page.keyboard.press('Control+['); await editorValue(page, source);
    await page.keyboard.press('Meta+]');
    await editorValue(page, source.slice(0, start) + '  ' + source.slice(start));
    await page.keyboard.press('Meta+['); await editorValue(page, source);
    await selectSourceText(page, 0);
    await page.keyboard.press('Control+['); await editorValue(page, source);
    for (const modifiers of [
      { ctrlKey: true, metaKey: false, altKey: false, shiftKey: false, isComposing: true },
      { ctrlKey: true, metaKey: false, altKey: true, shiftKey: false, isComposing: false },
      { ctrlKey: false, metaKey: true, altKey: false, shiftKey: true, isComposing: false },
    ]) {
      assert.equal(await page.locator('#expanded-source').evaluate((node, modifiers) => node.dispatchEvent(new KeyboardEvent('keydown', {
        key: ']', bubbles: true, cancelable: true, ...modifiers,
      })), modifiers), true, 'indentation must not consume IME or unrelated modifier combinations');
      await editorValue(page, source);
    }
    await page.keyboard.press('Tab');
    assert.equal(await page.locator('#cancel-editor').evaluate(button => button === document.activeElement), true, 'Tab leaves the textarea');
    await page.keyboard.press('Shift+Tab');
    assert.equal(await page.locator('#expanded-source').evaluate(editor => editor === document.activeElement), true);
    await page.keyboard.press('Shift+Tab');
    assert.equal(await page.locator('#editor-line-toggle').evaluate(button => button === document.activeElement), true);
    await selectSourceText(page, source.length);
    await page.keyboard.type(' -- typed');
    const typed = `${source} -- typed`;
    await editorValue(page, typed);
    await page.keyboard.press('Control+]');
    await editorValue(page, typed.slice(0, start) + '  ' + typed.slice(start));
    await page.keyboard.press('Control+z'); await editorValue(page, typed);
    await page.keyboard.press('Control+Shift+z');
    await editorValue(page, typed.slice(0, start) + '  ' + typed.slice(start));
    await discardSourceEditor(page, () => page.keyboard.press('Escape'));
    assert.equal(await page.locator('#source').inputValue(), source);
    assert.equal(await page.locator('#source').evaluate(node => node.dispatchEvent(new KeyboardEvent('keydown', {
      key: ']', ctrlKey: true, bubbles: true, cancelable: true,
    }))), true, 'editor shortcuts are scoped to the expanded editor');
    await closeSettings(page);
  });

  await scenario('Cursor positions count Unicode characters and indentation preserves a scrolled reading position', async h => {
    const { page } = h;
    const source = `-- 🙂x\ntheorem editor_position_fixture : True := by\n  trivial\n${Array.from({ length: 220 }, (_, index) => `-- context row ${index + 1}`).join('\n')}`;
    await editSource(h, source);
    await selectSourceText(page, '-- 🙂'.length);
    await editorPosition(page, '第 1 行 · 第 5 列');
    await selectSourceText(page, 0, '-- 🙂'.length, 'backward');
    await editorPosition(page, '第 1 行 · 第 1 列');
    await selectSourceText(page, source.indexOf('-- context row 175'));
    const before = await page.locator('#expanded-source').evaluate(node => {
      const editor = node as HTMLTextAreaElement;
      editor.scrollTop = 120;
      return { top: editor.scrollTop, left: editor.scrollLeft, lines: editor.value.split('\n').length };
    });
    await page.locator('#editor-indent').click();
    assert.deepEqual(await page.locator('#expanded-source').evaluate(node => {
      const editor = node as HTMLTextAreaElement;
      return { top: editor.scrollTop, left: editor.scrollLeft, lines: editor.value.split('\n').length };
    }), before);
    await editorPosition(page, '第 178 行 · 第 3 列');
    assert.equal(await page.locator('#source').inputValue(), source);
    assert.match(await page.locator('#editor-count').innerText(), /^223 行/);
    await discardSourceEditor(page, () => page.keyboard.press('Escape'));
    await closeSettings(page);
  });

  await scenario('An unavailable native edit keeps source and selection intact and permits manual editing', async h => {
    const { page } = h;
    const source = 'theorem unavailable_indent_fixture : True := by\n  trivial';
    await editSource(h, source);
    const start = source.indexOf('  trivial') + 2;
    for (const mode of ['false', 'throw']) {
      await selectSourceText(page, start, source.length, 'backward');
      await page.evaluate(mode => { document.execCommand = () => { if (mode === 'throw') throw new Error('Fixture unavailable edit'); return false; }; }, mode);
      await page.locator('#editor-indent').click();
      await editorValue(page, source);
      assert.equal(await page.locator('#editor-error').isVisible(), true);
      assert.match(await page.locator('#editor-error').innerText(), /未能调整缩进/);
      assert.deepEqual(await page.locator('#expanded-source').evaluate(node => {
        const editor = node as HTMLTextAreaElement;
        return [editor.selectionStart, editor.selectionEnd, editor.selectionDirection];
      }), [start, source.length, 'backward']);
    }
    await selectSourceText(page, source.length);
    await page.keyboard.type(' ');
    await editorValue(page, `${source} `);
    assert.equal(await page.locator('#editor-error').isVisible(), false);
    assert.equal(await page.locator('#source').inputValue(), source);
    await discardSourceEditor(page);
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
