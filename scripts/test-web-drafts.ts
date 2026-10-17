#!/usr/bin/env bun
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import net from 'node:net';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium, type BrowserContext, type Page, type Route } from 'playwright';
import { readWebConfig, webTemplates } from '../apps/web/config';
import { createWebService } from '../apps/web/server';
import type { WebRunner } from '../apps/web/runner';
import type { WebRun } from '../apps/web/shared';
import { fillConfig, refreshHistory, selectConfig, showChat, withSettings } from './web-ui-controls';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const output = path.join(root, 'out/web-ui-smoke');
const reportFile = path.join(output, 'drafts-report.json');
const storageKey = 'theorem-os.web-draft.v1';
const credential = `sk-theoremos-draft-fixture-${crypto.randomUUID()}`;
const markup = '<img data-draft-injection src=x onerror="window.__draftInjected=true">';
type Draft = {
  providerId: string; model: string; effort: string; environment: string; templateId: string;
  source: string; task: string; maxTurns: string; maxRunSeconds: string; workers: string; coordination: string;
};
const ids = { providerId: 'provider', model: 'model', effort: 'effort', environment: 'environment', templateId: 'template',
  source: 'source', task: 'task', maxTurns: 'max-turns', maxRunSeconds: 'max-seconds', workers: 'workers' };
const imported: Draft = { providerId: 'backup', model: 'fixture-import-model', effort: 'medium', environment: 'standard', templateId: '',
  source: `-- ${markup}\ntheorem imported_task : True := by trivial\n`, task: `Imported task\n${markup}`,
  maxTurns: '4', maxRunSeconds: '120', workers: '2', coordination: 'independent' };
const draftFile = (draft: Draft) => ({ schema: storageKey, draft });
const draftBytes = (draft: Draft) => Buffer.from(JSON.stringify(draftFile(draft)));
await fs.access(path.join(root, 'out/web/app.js')).catch(() => { throw new Error('Run bun run build:web before the drafts check.'); });
await fs.mkdir(output, { recursive: true });
await fs.rm(reportFile, { force: true });
const probe = net.createServer();
await new Promise<void>(resolve => probe.listen(0, '127.0.0.1', resolve));
const port = (probe.address() as net.AddressInfo).port;
await new Promise<void>((resolve, reject) => probe.close(error => error ? reject(error) : resolve()));
const origin = `http://127.0.0.1:${port}`;
let workerStarts = 0;
const runner: WebRunner = {
  async readiness() { return { ready: true, message: 'Local draft fixture' }; },
  async run() { workerStarts++; throw new Error('Draft workflows must not start a worker'); },
};
const service = createWebService(readWebConfig({ THEOREMOS_WEB_PORT: String(port), THEOREMOS_WEB_PUBLIC_URL: origin,
  THEOREMOS_WEB_STATIC_ROOT: path.join(root, 'out/web'), THEOREMOS_WEB_PROVIDERS: JSON.stringify([
    { id: 'openai', name: 'OpenAI', baseUrl: 'https://api.openai.com/v1' },
    { id: 'backup', name: 'Fixture backup', baseUrl: 'https://example.invalid/v1' },
  ]) }), runner);
type Harness = { page: Page; context: BrowserContext; requests: Array<{ method: string; pathname: string }>;
  intercept?: (route: Route) => Promise<boolean>; releases: Array<() => void> };
const checks: Array<{ name: string; elapsedMs: number; requests: Harness['requests'] }> = [];
const screenshots: string[] = [];
const widths = [1440, 375, 320];
let browser: Awaited<ReturnType<typeof chromium.launch>> | undefined;
let failedScenario = '';
let failureScreenshot: string | undefined;
const ready = (page: Page) => page.locator('#submit-run:enabled').waitFor();
const dialog = (page: Page) => page.locator('#import-task-dialog[open]');
function deferred() {
  let resolve!: () => void;
  const promise = new Promise<void>(done => { resolve = done; });
  return { promise, resolve };
}
async function scenario(name: string, run: (h: Harness) => Promise<void>) {
  failedScenario = name;
  const started = performance.now();
  const context = await browser!.newContext({ viewport: { width: 1440, height: 900 } });
  const page = await context.newPage();
  page.setDefaultTimeout(10_000);
  const h: Harness = { page, context, requests: [], releases: [] };
  const errors: string[] = [];
  page.on('pageerror', error => errors.push(error.message));
  await page.route('**/api/**', async route => {
    h.requests.push({ method: route.request().method(), pathname: new URL(route.request().url()).pathname });
    if (await h.intercept?.(route)) return;
    await route.continue();
  });
  let deadline: ReturnType<typeof setTimeout> | undefined;
  try {
    await Promise.race([run(h), new Promise<never>((_, reject) => {
      deadline = setTimeout(() => reject(new Error(`Draft scenario exceeded 35 seconds: ${name}`)), 35_000);
    })]);
    assert.deepEqual(errors, [], 'uncaught browser errors');
    assert.equal(h.requests.filter(request => request.method !== 'GET').length, 0, 'draft workflow must only read API endpoints');
    assert.equal(await page.locator('#run-count').innerText(), '0', 'import must not populate run history');
    checks.push({ name, elapsedMs: Math.round(performance.now() - started), requests: h.requests });
    console.log(`PASS ${name}`);
  } catch (error) {
    failureScreenshot = `drafts-failure-${checks.length + 1}.png`;
    await page.screenshot({ path: path.join(output, failureScreenshot), fullPage: true }).catch(() => {});
    throw error;
  } finally {
    clearTimeout(deadline);
    for (const release of h.releases) release();
    await context.close();
  }
}
async function open(h: Harness) { await h.page.goto(origin); await ready(h.page); }
async function snapshot(page: Page): Promise<Draft> {
  return page.evaluate(ids => ({ ...Object.fromEntries(Object.entries(ids).map(([key, id]) =>
    [key, (document.getElementById(id) as HTMLInputElement).value])),
    coordination: (document.querySelector('input[name="coordination"]:checked') as HTMLInputElement).value }) as Draft, ids);
}
async function fill(page: Page, value: Draft) {
  await withSettings(page, async () => {
    await page.locator('#provider').selectOption(value.providerId);
    await page.locator('#environment').selectOption(value.environment);
    await page.locator('#template').selectOption('');
    await page.locator('#effort').selectOption(value.effort);
    for (const key of ['model', 'source', 'maxTurns', 'maxRunSeconds', 'workers'] as const) await page.locator(`#${ids[key]}`).fill(value[key]);
    await page.locator(`input[name="coordination"][value="${value.coordination}"]`).check();
  });
  await page.locator('#task').fill(value.task);
  if (value.templateId) await selectConfig(page, 'template', value.templateId);
}
async function assertDraft(page: Page, expected: Draft) { assert.deepEqual(await snapshot(page), expected); }
async function saved(page: Page, expected: Draft) {
  await page.waitForFunction(({ key, expected }) => {
    try {
      const actual = JSON.parse(sessionStorage.getItem(key) || 'null');
      return actual?.schema === key && Object.entries(expected).every(([field, value]) => actual.draft?.[field] === value);
    }
    catch { return false; }
  }, { key: storageKey, expected });
}
async function assertKeyNotStored(page: Page) {
  const stored = await page.evaluate(() => ({ session: JSON.stringify(sessionStorage), local: JSON.stringify(localStorage) }));
  assert.equal(stored.session.includes(credential), false);
  assert.equal(stored.local, '{}', 'drafts must not be written to localStorage');
  if (await page.evaluate(key => sessionStorage.getItem(key) !== null, storageKey)) {
    const body = await page.evaluate(key => JSON.parse(sessionStorage.getItem(key)!), storageKey);
    assert.equal(Object.hasOwn(body.draft, 'apiKey'), false);
  }
}
async function importFile(page: Page, buffer: Buffer, name = 'draft.json') {
  await showChat(page);
  const choosing = page.waitForEvent('filechooser');
  await page.locator('#import-task').click();
  await (await choosing).setFiles({ name, mimeType: 'application/json', buffer });
}
async function noInjection(page: Page) {
  assert.equal(await page.locator('[data-draft-injection]').count(), 0);
  assert.equal(await page.evaluate(() => (window as unknown as Record<string, unknown>).__draftInjected), undefined);
}
async function screenshot(page: Page, name: string) {
  await page.screenshot({ path: path.join(output, name), fullPage: true });
  screenshots.push(name);
}
async function seed(h: Harness, body: string) {
  await h.context.addInitScript(({ key, body }) => sessionStorage.setItem(key, body), { key: storageKey, body });
}
async function gateFile(page: Page, filename: string) {
  await page.evaluate(filename => {
    type Gate = { seen: boolean; complete: boolean; promise: Promise<void>; release(): void };
    const exposed = window as unknown as { __draftReadGate: Gate };
    let release!: () => void;
    exposed.__draftReadGate = { seen: false, complete: false, promise: new Promise<void>(resolve => { release = resolve; }), release: () => release() };
    const read = File.prototype.arrayBuffer;
    File.prototype.arrayBuffer = async function(this: File) {
      if (this.name !== filename) return read.call(this);
      exposed.__draftReadGate.seen = true;
      await exposed.__draftReadGate.promise;
      try { return await read.call(this); }
      finally { exposed.__draftReadGate.complete = true; }
    };
  }, filename);
}
async function fileReadStarted(page: Page) {
  await page.waitForFunction(() => (window as unknown as { __draftReadGate: { seen: boolean } }).__draftReadGate.seen);
}
async function releaseFile(page: Page) {
  await page.evaluate(() => (window as unknown as { __draftReadGate: { release(): void } }).__draftReadGate.release());
  await page.waitForFunction(() => (window as unknown as { __draftReadGate: { complete: boolean } }).__draftReadGate.complete);
  await page.waitForTimeout(100);
}
async function writeReport(status: 'passed' | 'failed', error?: unknown) {
  await fs.writeFile(reportFile, JSON.stringify({ status, checkedAt: new Date().toISOString(),
    mode: 'Real HTTP service and Chromium with local task files and controlled storage failures. No Docker, Lean or model provider is called.',
    paidModelCalls: false, workerStarts, checks, widths, screenshots,
    ...(error ? { failedScenario, error: error instanceof Error ? error.message : String(error), failureScreenshot } : {}) }, null, 2) + '\n');
}
try {
  await new Promise<void>((resolve, reject) => { service.server.once('error', reject); service.server.listen(port, '127.0.0.1', resolve); });
  browser = await chromium.launch({ headless: true });

  await scenario('Autosave restores every draft field on refresh without storing the API key or sharing drafts with another tab', async h => {
    await open(h);
    await fill(h.page, imported);
    await fillConfig(h.page, 'api-key', credential);
    await saved(h.page, imported);
    await assertKeyNotStored(h.page);
    await h.page.reload(); await ready(h.page);
    await assertDraft(h.page, imported);
    assert.equal(await h.page.locator('#api-key').inputValue(), '');
    const other = await h.context.newPage();
    await other.goto(origin); await ready(other);
    assert.notEqual((await snapshot(other)).source, imported.source);
    assert.equal(await other.evaluate(key => sessionStorage.getItem(key), storageKey), null);
    await other.close();
    await assertKeyNotStored(h.page);
  });

  await scenario('Visibility changes and immediate reload flush edits; empty numeric fields remain empty after recovery', async h => {
    await open(h);
    const value = { ...imported, maxTurns: '', maxRunSeconds: '', workers: '' };
    await fill(h.page, value);
    await saved(h.page, value);
    const hiddenTask = 'Edit flushed synchronously when the page becomes hidden';
    const flushed = await h.page.evaluate(({ key, task }) => {
      const field = document.querySelector('#task') as HTMLTextAreaElement;
      field.value = task; field.dispatchEvent(new Event('input', { bubbles: true }));
      const previous = Object.getOwnPropertyDescriptor(document, 'hidden');
      Object.defineProperty(document, 'hidden', { configurable: true, value: true });
      document.dispatchEvent(new Event('visibilitychange'));
      if (previous) Object.defineProperty(document, 'hidden', previous);
      else Reflect.deleteProperty(document, 'hidden');
      return JSON.parse(sessionStorage.getItem(key)!).draft.task;
    }, { key: storageKey, task: hiddenTask });
    assert.equal(flushed, hiddenTask);
    const task = 'Last edit immediately before navigation';
    const loaded = h.page.waitForEvent('load');
    await h.page.evaluate(task => {
      const field = document.querySelector('#task') as HTMLTextAreaElement;
      field.value = task; field.dispatchEvent(new Event('input', { bubbles: true }));
      location.reload();
    }, task);
    await loaded; await ready(h.page);
    await assertDraft(h.page, { ...value, task });
    await assertKeyNotStored(h.page);
  });

  await scenario('Template identity follows exact source and task matches; reset removes the old saved draft', async h => {
    await open(h);
    const defaults = await snapshot(h.page);
    const initial = webTemplates.find(template => template.id === defaults.templateId)!;
    assert.ok(initial);
    assert.equal(defaults.source, initial.source);
    assert.equal(defaults.task, initial.task);
    const addition = webTemplates.find(template => template.id === 'addition')!;
    await selectConfig(h.page, 'environment', 'standard');
    await selectConfig(h.page, 'template', 'addition');
    const selected = await snapshot(h.page);
    assert.equal(selected.source, addition.source);
    await saved(h.page, selected);
    await h.page.reload(); await ready(h.page);
    await assertDraft(h.page, selected);
    await fillConfig(h.page, 'source', imported.source);
    const custom = await snapshot(h.page);
    assert.equal(custom.templateId, '');
    await saved(h.page, custom);
    await h.page.reload(); await ready(h.page);
    await assertDraft(h.page, custom);
    await withSettings(h.page, () => h.page.locator('#reset-form').click());
    assert.equal(await h.page.evaluate(key => sessionStorage.getItem(key), storageKey), null);
    await h.page.reload(); await ready(h.page);
    await assertDraft(h.page, defaults);
  });

  await scenario('Reconnection preserves edits made during recovery and unavailable providers stay unselected', async h => {
    await seed(h, JSON.stringify(draftFile({ ...imported, providerId: 'removed-provider' })));
    await open(h);
    const expected = { ...imported, providerId: '' };
    await assertDraft(h.page, expected);
    const gate = deferred(), seen = deferred();
    h.releases.push(gate.resolve);
    let expire = true;
    h.intercept = async route => {
      const pathname = new URL(route.request().url()).pathname;
      if (pathname === '/api/runs' && expire) {
        expire = false; await route.fulfill({ status: 401, json: { error: 'Expired draft session fixture' } }); return true;
      }
      if (pathname === '/api/session') { seen.resolve(); await gate.promise; }
      return false;
    };
    await refreshHistory(h.page); await seen.promise;
    expected.task += '\nEdited while reconnecting.';
    await h.page.locator('#task').fill(expected.task);
    gate.resolve(); await ready(h.page);
    await assertDraft(h.page, expected);
  });

  await scenario('Draft export preserves all fields and excludes the key; cancel, close and Escape preserve the current draft', async h => {
    await open(h);
    await fill(h.page, imported);
    await fillConfig(h.page, 'api-key', credential);
    const downloading = h.page.waitForEvent('download');
    await h.page.locator('#export-draft').click();
    const file = await downloading;
    const bytes = await fs.readFile((await file.path())!);
    assert.deepEqual(JSON.parse(bytes.toString('utf8')), draftFile(imported));
    assert.equal(bytes.includes(Buffer.from(credential)), false);
    const incoming = { ...imported, task: 'Different incoming task', source: 'theorem different : True := by trivial\n' };
    for (const action of ['cancel', 'close', 'escape']) {
      await importFile(h.page, draftBytes(incoming)); await dialog(h.page).waitFor();
      await assertDraft(h.page, imported);
      assert.equal(await h.page.locator('#api-key').inputValue(), credential);
      if (action === 'escape') await h.page.keyboard.press('Escape');
      else await h.page.locator(action === 'cancel' ? '#cancel-import' : '#close-import').click();
      await dialog(h.page).waitFor({ state: 'hidden' });
      await assertDraft(h.page, imported);
      assert.equal(await h.page.locator('#api-key').inputValue(), credential);
    }
    await assertKeyNotStored(h.page);
  });

  await scenario('Confirmed draft and archive imports restore original fields, clear the key and never create history', async h => {
    await open(h);
    await fillConfig(h.page, 'api-key', credential);
    await importFile(h.page, Buffer.concat([Buffer.from([0xef, 0xbb, 0xbf]), draftBytes(imported)]), 'bom-draft.json');
    await dialog(h.page).waitFor();
    assert.equal(await h.page.locator('#import-task-preview').textContent(), imported.task);
    assert.equal(await h.page.locator('#import-source-preview').textContent(), imported.source);
    await h.page.locator('#confirm-import').click(); await dialog(h.page).waitFor({ state: 'hidden' });
    await assertDraft(h.page, imported);
    assert.equal(await h.page.locator('#api-key').inputValue(), '');
    await saved(h.page, imported);
    const archiveDraft = { ...imported, providerId: 'openai', model: 'archive-original-model', effort: 'high', source: 'theorem archive_original : True := by sorry\n',
      task: 'Archive original task', maxTurns: '3', maxRunSeconds: '90', workers: '1', coordination: 'cooperative' };
    const proofPrefix = '-- fixture candidate proof, never the original task\n';
    const archivedRun: WebRun = { id: crypto.randomUUID(), title: 'Archived success', status: 'completed', phase: 'evaluated_passed',
      providerId: archiveDraft.providerId, model: archiveDraft.model, effort: 'high', environment: 'standard', source: archiveDraft.source,
      task: archiveDraft.task, maxTurns: 3, maxRunSeconds: 90, workers: 1, coordination: 'cooperative', createdAt: new Date().toISOString(), updatedAt: new Date().toISOString(),
      events: Array.from({ length: 30 }, (_, index) => ({ sequence: index + 1, at: new Date().toISOString(), type: 'fixture_activity', message: 'e'.repeat(2_000) })),
      result: { status: 'evaluated_passed', proof: proofPrefix + 'p'.repeat(128 * 1024 - Buffer.byteLength(proofPrefix)),
        report: { ignored: true, retainedOnlyInArchive: 'report payload '.repeat(12_000) } } };
    const archiveBytes = Buffer.from(JSON.stringify({ schema: 'theorem-os.web-export.v1', run: archivedRun }));
    assert.ok(archiveBytes.length > 256 * 1024 && archiveBytes.length <= 16 * 1024 * 1024);
    await fillConfig(h.page, 'api-key', credential);
    await importFile(h.page, archiveBytes, 'archive.json');
    await dialog(h.page).waitFor();
    assert.equal(await h.page.locator('#import-source-preview').textContent(), archiveDraft.source);
    await h.page.locator('#confirm-import').click(); await dialog(h.page).waitFor({ state: 'hidden' });
    await assertDraft(h.page, archiveDraft);
    assert.equal(await h.page.locator('#api-key').inputValue(), '');
    await saved(h.page, archiveDraft);
    await assertKeyNotStored(h.page);
  });

  await scenario('Invalid, oversized and malformed UTF-8 files preserve the active draft and key', async h => {
    await open(h); await fill(h.page, imported); await fillConfig(h.page, 'api-key', credential);
    const invalid = [
      { name: 'oversized.json', buffer: Buffer.alloc(16 * 1024 * 1024 + 1, 32) },
      { name: 'invalid-utf8.json', buffer: Buffer.from([0x7b, 0x22, 0xc3, 0x28, 0x22, 0x7d]) },
      { name: 'broken.json', buffer: Buffer.from('{broken') },
      { name: 'unknown-schema.json', buffer: Buffer.from(JSON.stringify({ schema: 'unknown', draft: imported })) },
      { name: 'large-source.json', buffer: draftBytes({ ...imported, source: 'x'.repeat(32_769) }) },
      { name: 'large-task.json', buffer: draftBytes({ ...imported, task: 'x'.repeat(8193) }) },
    ];
    for (const file of invalid) {
      await importFile(h.page, file.buffer, file.name);
      await h.page.locator('#draft-error').waitFor({ state: 'visible' });
      assert.equal(await dialog(h.page).count(), 0);
      await assertDraft(h.page, imported);
      assert.equal(await h.page.locator('#api-key').inputValue(), credential);
    }
  });

  await scenario('Late reads cannot overwrite key edits, a newer file preview or edits made after preview', async h => {
    await open(h); await fill(h.page, imported); await fillConfig(h.page, 'api-key', credential);
    await gateFile(h.page, 'slow.json');
    const incoming = { ...imported, task: 'Delayed first file' };
    await importFile(h.page, draftBytes(incoming), 'slow.json'); await fileReadStarted(h.page);
    await fillConfig(h.page, 'api-key', `${credential}-edited`);
    await releaseFile(h.page);
    assert.equal(await dialog(h.page).count(), 0);
    await assertDraft(h.page, imported);
    assert.equal(await h.page.locator('#api-key').inputValue(), `${credential}-edited`);
    await gateFile(h.page, 'first.json');
    await importFile(h.page, draftBytes(incoming), 'first.json'); await fileReadStarted(h.page);
    const second = { ...imported, task: 'Newer second file' };
    await importFile(h.page, draftBytes(second), 'second.json'); await dialog(h.page).waitFor();
    await releaseFile(h.page);
    assert.equal(await h.page.locator('#import-filename').textContent(), 'second.json');
    assert.equal(await h.page.locator('#import-task-preview').textContent(), second.task);
    await h.page.locator('#confirm-import').click(); await dialog(h.page).waitFor({ state: 'hidden' });
    await assertDraft(h.page, second);
    await importFile(h.page, draftBytes(incoming)); await dialog(h.page).waitFor();
    await h.page.evaluate(() => {
      const model = document.querySelector('#model') as HTMLInputElement;
      model.value = 'edited-after-preview'; model.dispatchEvent(new Event('input', { bubbles: true }));
    });
    await h.page.locator('#confirm-import:disabled').waitFor();
    await h.page.locator('#import-notice').waitFor({ state: 'visible' });
    await h.page.locator('#cancel-import').click();
    await assertDraft(h.page, { ...second, model: 'edited-after-preview' });
  });

  await scenario('Corrupt saved JSON does not block editing or saving a fresh draft', async h => {
    await seed(h, '{broken-storage-json');
    await open(h);
    await fill(h.page, imported);
    await saved(h.page, imported);
    await assertKeyNotStored(h.page);
  });

  for (const failure of ['unavailable', 'quota'] as const) {
    await scenario(`Storage ${failure} failures leave the composer and draft export usable`, async h => {
      await h.context.addInitScript(({ failure, key }) => {
        if (failure === 'unavailable') Object.defineProperty(window, 'sessionStorage', { configurable: true,
          get() { throw new DOMException('Fixture storage unavailable', 'SecurityError'); } });
        else {
          const original = Storage.prototype.setItem;
          Storage.prototype.setItem = function(name, value) {
            if (name === key) throw new DOMException('Fixture storage quota', 'QuotaExceededError');
            original.call(this, name, value);
          };
        }
      }, { failure, key: storageKey });
      await open(h); await fill(h.page, imported); await h.page.waitForTimeout(350);
      await assertDraft(h.page, imported);
      assert.equal(await h.page.locator('#source').isEnabled(), true);
      const downloading = h.page.waitForEvent('download');
      await h.page.locator('#export-draft').click();
      const exported = JSON.parse(await fs.readFile((await (await downloading).path())!, 'utf8'));
      assert.deepEqual(exported, draftFile(imported));
      assert.equal(await h.page.evaluate(() => JSON.stringify(localStorage)), '{}');
    });
  }

  await scenario('Import previews escape filenames and source text and fit 320, 375 and 1440 pixel layouts', async h => {
    await open(h); await fill(h.page, imported);
    const filename = 'draft-<img data-draft-injection src=x>.json';
    const long = { ...imported, source: `-- ${'long_identifier_'.repeat(25)}\n${imported.source}`, task: `${imported.task}\n${'Long task '.repeat(24)}` };
    for (const width of widths) {
      const height = width > 850 ? 900 : 812;
      await h.page.setViewportSize({ width, height });
      await showChat(h.page);
      assert.equal(await h.page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), true, `compose overflow at ${width}`);
      await screenshot(h.page, `drafts-${width}-composer.png`);
      await importFile(h.page, draftBytes(long), filename); await dialog(h.page).waitFor();
      assert.equal(await h.page.locator('#import-filename').textContent(), filename);
      assert.equal(await h.page.locator('#import-source-preview').textContent(), long.source);
      await noInjection(h.page);
      assert.equal(await h.page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), true, `preview overflow at ${width}`);
      const bounds = await dialog(h.page).boundingBox();
      assert.ok(bounds && bounds.x >= 0 && bounds.x + bounds.width <= width + 1);
      assert.equal(await dialog(h.page).evaluate(target => target.scrollWidth <= target.clientWidth), true, `dialog overflow at ${width}`);
      for (const id of ['confirm-import', 'cancel-import', 'close-import']) {
        const button = await h.page.locator(`#${id}`).boundingBox();
        assert.ok(button && button.x >= 0 && button.x + button.width <= width + 1 && button.y >= 0 && button.y + button.height <= height + 1, `${id} outside ${width}x${height}`);
      }
      await screenshot(h.page, `drafts-${width}-import.png`);
      await h.page.locator('#cancel-import').click();
      await assertDraft(h.page, imported);
    }
  });

  assert.equal(workerStarts, 0);
  await writeReport('passed');
  console.log(`Drafts report: ${reportFile}`);
} catch (error) {
  await writeReport('failed', error);
  throw error;
} finally {
  await browser?.close();
  await service.close();
}
